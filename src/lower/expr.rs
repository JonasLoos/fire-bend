// src/bend/lower/expr.rs
// Expression lowering: terms in A-normal form, closures, calls, matches,
// iterators for `for` loops, and conditions.

use std::collections::HashSet;

use super::body::*;
use super::*;

impl<'a> Lower<'a> {
    /// Resolve a typed-AST type in the current instance.
    pub fn rty(&mut self, ctx: &FnCtx, t: &Type) -> Type {
        let t = self.store.substitute(t, &ctx.inst.subst);
        self.store.resolve(&t)
    }

    pub fn bty(&mut self, ctx: &FnCtx, t: &Type, line: usize) -> Ty {
        let r = self.rty(ctx, t);
        self.ty(&r, &[], line)
    }

    /// Bind a term to a fresh temporary (a let, or a bind when monadic).
    pub fn temp(&mut self, ctx: &mut FnCtx, value: Term, ty: Ty, monadic: bool) -> Term {
        let name = self.fresh("__t");
        if monadic {
            ctx.seg.push(Stmt::Bind { name: name.clone(), ty, value });
        } else {
            match ctx.mode {
                Mode::Pure => {
                    let value = annotate_if_needed(value, &ty);
                    ctx.seg.push(Stmt::Let { name: name.clone(), reusable: false, ty: None, value })
                }
                _ => ctx.seg.push(Stmt::Let { name: name.clone(), reusable: false, ty: Some(ty), value }),
            }
        }
        Term::Var(name)
    }

    /// Adapt a call of a callee in `callee_mode` to the current mode: pure
    /// calls stay terms; monadic ones are bound to a temporary.
    pub fn adapt_call(&mut self, ctx: &mut FnCtx, call: Term, callee_mode: Mode, result_ty: Ty, line: usize) -> Term {
        match (callee_mode, ctx.mode) {
            (Mode::Pure, _) => call,
            (Mode::Result, Mode::Result) | (Mode::Io, Mode::Io) => self.temp(ctx, call, result_ty, true),
            (Mode::Result, Mode::Io) => {
                let wrapped = Term::Call("F.io_unwrap".into(), vec![Term::TyArg(result_ty.clone()), call]);
                self.temp(ctx, wrapped, result_ty, true)
            }
            (m, _) => {
                self.error(line, format!("internal: a {:?} call inside a {:?} function", m, ctx.mode));
                call
            }
        }
    }

    // -- expressions ---------------------------------------------------------

    pub fn lower_expr(&mut self, ctx: &mut FnCtx, e: &TExpr) -> Term {
        let line = e.line;
        match &e.kind {
            TExprKind::Local(n) => {
                if !ctx.locals.contains_key(n) {
                    self.error(line, format!("internal: unknown local {}", n));
                }
                Term::Var(Self::mangle(n))
            }
            TExprKind::Lit(l) => self.lower_lit(ctx, l, &e.ty, line),
            TExprKind::List(items) => {
                let ts: Vec<Term> = items.iter().map(|i| self.lower_expr(ctx, i)).collect();
                Term::List(ts)
            }
            TExprKind::EmptyMap => {
                let vt = match self.rty(ctx, &e.ty) {
                    Type::Map(v) => self.ty(&v, &[], line),
                    _ => Ty::Unit,
                };
                Term::Call("Map.new".into(), vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(vt)])
            }
            TExprKind::MakeRecord(rec, fields) => {
                self.ensure_record_type(*rec);
                let ts: Vec<Term> = fields.iter().map(|f| self.lower_expr(ctx, f)).collect();
                Term::Ctor(self.record_ctor_name(*rec), ts)
            }
            TExprKind::Field(o, rec, idx) => {
                let ot = self.rty(ctx, &o.ty);
                let obj = self.lower_expr(ctx, o);
                self.field_get(*rec, *idx, &ot, obj, line)
            }
            TExprKind::Member(o, name) => self.lower_member(ctx, o, name, &e.ty, line),
            TExprKind::SetField(o, rec, idx, v) => {
                let ot = self.rty(ctx, &o.ty);
                let obj = self.lower_expr(ctx, o);
                let val = self.lower_expr(ctx, v);
                self.field_set(*rec, *idx, &ot, obj, val, line)
            }
            TExprKind::SelfValue(rec) => {
                let fields: Vec<Term> = self.tp.records[*rec].fields.iter().map(|f| Term::Var(Self::mangle(&f.name))).collect();
                Term::Ctor(self.record_ctor_name(*rec), fields)
            }
            TExprKind::Call(def, args) => self.lower_call(ctx, *def, args, &e.ty, line),
            TExprKind::CallValue(f, args) => {
                let ft = self.rty(ctx, &f.ty);
                let rep = self.closure_rep(&ft, line);
                let fterm = self.lower_expr(ctx, f);
                let mut targs = vec![fterm];
                for a in args {
                    targs.push(self.lower_expr(ctx, a));
                }
                match rep.code {
                    Some(code) => {
                        let mode = self.rep_mode(&ft);
                        let rt = self.bty(ctx, &e.ty, line);
                        let call = Term::Call(code, targs);
                        self.adapt_call(ctx, call, mode, rt, line)
                    }
                    None => {
                        self.error(line, "this function value has no known origin and cannot be called");
                        Term::unit()
                    }
                }
            }
            TExprKind::MethodCall { recv, name, args } => self.lower_method_call(ctx, recv, name, args, &e.ty, line, false).0,
            TExprKind::Builtin(name, args) => self.lower_builtin(ctx, name, args, &e.ty, line),
            TExprKind::Lambda(def) => {
                let ft = self.rty(ctx, &e.ty);
                let (t, _) = self.closure_value(ctx, *def, &ft, line);
                t
            }
            TExprKind::DefRef(def) => {
                let ft = self.rty(ctx, &e.ty);
                let (t, _) = self.closure_value(ctx, *def, &ft, line);
                t
            }
            TExprKind::If { cond, then, else_ } => {
                let c = self.lower_cond(ctx, cond);
                let rt = self.bty(ctx, &e.ty, line);
                let live = self.live_in_exprs(ctx, &[then, else_], &Cont::Join { name: String::new(), live: vec![] });
                let live = self.with_captures(ctx, &live, &[then, else_]);
                let name = self.fresh(&format!("{}.ife", ctx.base));
                let mut tctx = self.sub_ctx(ctx, &live);
                tctx.result = rt.clone();
                let tb = self.lower_expr_body(&mut tctx, then);
                let mut ectx = self.sub_ctx(ctx, &live);
                ectx.result = rt.clone();
                let eb = self.lower_expr_body(&mut ectx, else_);
                let body = Body::Match { scrutinee: "__c".into(), arms: vec![(Pat::Ctor("True".into(), vec![]), tb), (Pat::Ctor("False".into(), vec![]), eb)] };
                self.emit_helper(&tctx, name.clone(), &live, vec![Param { name: "__c".into(), reusable: false, ty: Ty::Bool }], rt.clone(), body);
                let call = self.call_helper(&name, &live, vec![c]);
                self.adapt_call(ctx, call, ctx.mode, rt, line)
            }
            TExprKind::Match { subject, arms } => {
                let subj = self.lower_expr(ctx, subject);
                let sty = self.bty(ctx, &subject.ty, line);
                let stt = self.rty(ctx, &subject.ty);
                let rt = self.bty(ctx, &e.ty, line);
                let bodies: Vec<&TExpr> = arms.iter().map(|a| &a.body).collect();
                let mut live = self.live_in_exprs(ctx, &bodies, &Cont::Join { name: String::new(), live: vec![] });
                for a in arms {
                    if let Some(g) = &a.guard {
                        for n in self.live_in_exprs(ctx, &[g], &Cont::Join { name: String::new(), live: vec![] }) {
                            if !live.contains(&n) {
                                live.push(n);
                            }
                        }
                    }
                }
                let live = self.with_captures(ctx, &live, &bodies);
                let name = self.lower_match_arms(ctx, arms, &live, sty, stt, MatchKind::Expr(rt.clone()), line);
                let call = self.call_helper(&name, &live, vec![subj]);
                self.adapt_call(ctx, call, ctx.mode, rt, line)
            }
            TExprKind::Block(b) => {
                // inline: statements into the segment, value of the last
                let saved = ctx.locals.clone();
                let mut val = Term::unit();
                let n = b.stmts.len();
                for (i, s) in b.stmts.iter().enumerate() {
                    if i + 1 == n {
                        if let TStmtKind::Expr(v) = &s.kind {
                            val = self.lower_expr(ctx, v);
                            break;
                        }
                    }
                    match &s.kind {
                        TStmtKind::Let { .. } | TStmtKind::Assign { .. } | TStmtKind::Expr(_) | TStmtKind::Bind { .. } => {
                            // reuse the statement lowering for simple statements
                            let tail = self.lower_simple_stmt(ctx, s);
                            let _ = tail;
                        }
                        _ => {
                            self.error(s.line, "a block used as a value may only contain simple statements; move branching into a def");
                        }
                    }
                }
                ctx.locals = saved;
                val
            }
            TExprKind::And(a, b) | TExprKind::Or(a, b) => {
                let is_and = matches!(e.kind, TExprKind::And(_, _));
                let at = self.rty(ctx, &a.ty);
                let pure_b = expr_effect_of(self.tp, &self.effects, b) == Effect::Pure;
                if matches!(at, Type::Bool) && pure_b {
                    let ta = self.lower_expr(ctx, a);
                    let tb = self.lower_expr(ctx, b);
                    return if is_and { Term::And(Box::new(ta), Box::new(tb)) } else { Term::Or(Box::new(ta), Box::new(tb)) };
                }
                // general: if truthy(a) then (a or b) else (b or a)
                let ife = if is_and {
                    TExpr { kind: TExprKind::If { cond: a.clone(), then: b.clone(), else_: a.clone() }, ty: e.ty.clone(), line }
                } else {
                    TExpr { kind: TExprKind::If { cond: a.clone(), then: a.clone(), else_: b.clone() }, ty: e.ty.clone(), line }
                };
                self.lower_expr(ctx, &ife)
            }
            TExprKind::Not(a) => {
                let c = self.lower_cond(ctx, a);
                Term::Call("Bool.not".into(), vec![c])
            }
            TExprKind::BinOp(op, a, b) => {
                let at = self.rty(ctx, &a.ty);
                // a custom operator whose left operand's class was not known
                // when the expression was typed: the class's method
                if let (Type::Record(_, _), Some(sym)) = (&at, op.symbol()) {
                    if !matches!(op, BinOp::Eq | BinOp::Ne) {
                        return self.lower_method_call(ctx, a, sym, std::slice::from_ref(&**b), &e.ty, line, false).0;
                    }
                }
                let ta = self.lower_expr(ctx, a);
                let tb = self.lower_expr(ctx, b);
                self.lower_binop(ctx, *op, ta, tb, &at, line)
            }
            TExprKind::Neg(a) => {
                let at = self.rty(ctx, &a.ty);
                let ta = self.lower_expr(ctx, a);
                match at {
                    Type::Float => Term::Call("F32.neg".into(), vec![ta]),
                    _ => Term::op(Term::U32(0), "-", ta, Ty::U32),
                }
            }
            TExprKind::MakeOk(v) => {
                let t = self.lower_expr(ctx, v);
                Term::ctor("Done", vec![t])
            }
            TExprKind::MakeErr(v) => {
                let t = self.lower_expr(ctx, v);
                Term::ctor("Fail", vec![t])
            }
            TExprKind::MakeSome(v) => {
                let t = self.lower_expr(ctx, v);
                Term::ctor("Some", vec![t])
            }
            TExprKind::Pipe { left, func } => self.lower_pipe(ctx, left, func, &e.ty, line),
            TExprKind::Stage { op, input, func } => self.lower_stage(ctx, *op, input, func, &e.ty, line),
            TExprKind::Handle { left, handler, is_func } => self.lower_handle(ctx, left, handler, *is_func, &e.ty, line),
            TExprKind::Range { start, end } => match end {
                Some(en) => {
                    let s = self.lower_expr(ctx, start);
                    let en = self.lower_expr(ctx, en);
                    Term::ctor("F.Range.mk", vec![s, en])
                }
                None => {
                    self.error(line, "an open range can only be iterated, indexed, or piped into a stage");
                    Term::unit()
                }
            },
            TExprKind::RangeList(a, b) => {
                let ta = self.lower_expr(ctx, a);
                let tb = self.lower_expr(ctx, b);
                Term::Call("F.range.to_list".into(), vec![ta, tb])
            }
            TExprKind::Comprehension { pattern, iterables, filter, body } => {
                // a loop accumulating into a list
                let acc = self.fresh("__acc");
                let elem_bt = self.bty(ctx, &body.ty, line);
                let elem_tt = self.rty(ctx, &body.ty);
                let list_tt = Type::list(elem_tt.clone());
                let push = TStmt {
                    kind: TStmtKind::Assign {
                        name: acc.clone(),
                        value: TExpr { kind: TExprKind::Builtin("cons".into(), vec![(**body).clone(), TExpr { kind: TExprKind::Local(acc.clone()), ty: list_tt.clone(), line }]), ty: list_tt.clone(), line },
                    },
                    line,
                };
                let inner: Vec<TStmt> = match filter {
                    Some(f) => vec![TStmt { kind: TStmtKind::If { cond: (**f).clone(), then: TBlock { stmts: vec![push] }, elifs: vec![], else_: None }, line }],
                    None => vec![push],
                };
                let for_stmt = TStmt { kind: TStmtKind::For { pattern: pattern.clone(), iterables: iterables.clone(), body: TBlock { stmts: inner } }, line };
                let result_expr = TExpr { kind: TExprKind::Builtin("list_reverse".into(), vec![TExpr { kind: TExprKind::Local(acc.clone()), ty: list_tt.clone(), line }]), ty: list_tt.clone(), line };
                let block = TBlock {
                    stmts: vec![
                        TStmt { kind: TStmtKind::Let { name: acc.clone(), mutable: true, value: TExpr { kind: TExprKind::List(vec![]), ty: list_tt.clone(), line } }, line },
                        for_stmt,
                        TStmt { kind: TStmtKind::Expr(result_expr), line },
                    ],
                };
                // as a helper def returning the list
                let mut names = HashSet::new();
                for s in &block.stmts {
                    free_stmt(s, &mut names);
                }
                let mut live: Vec<String> = names.into_iter().filter(|n| ctx.locals.contains_key(n)).collect();
                live.sort();
                let live = self.with_captures(ctx, &live, &[body]);
                let name = self.fresh(&format!("{}.comp", ctx.base));
                let mut cctx = self.sub_ctx(ctx, &live);
                let list_bt = Ty::list(elem_bt);
                cctx.result = list_bt.clone();
                cctx.fn_result = list_bt.clone();
                cctx.base = name.clone();
                cctx.method = None;
                cctx.ctor = None;
                cctx.loops.clear();
                let cbody = self.lower_block(&mut cctx, &block.stmts, Cont::Ret);
                self.emit_helper(&cctx, name.clone(), &live, vec![], list_bt.clone(), cbody);
                let call = self.call_helper(&name, &live, vec![]);
                self.adapt_call(ctx, call, ctx.mode, list_bt, line)
            }
            TExprKind::FString(parts) => self.lower_fstring(ctx, parts, line),
            TExprKind::Abort(msg) => {
                let m = self.lower_expr(ctx, msg);
                let rt = self.bty(ctx, &e.ty, line);
                self.abort_term(ctx, m, rt, line)
            }
        }
    }

    /// The live set plus the captures of lambda sites inside the expressions.
    pub fn with_captures(&self, ctx: &FnCtx, live: &[String], exprs: &[&TExpr]) -> Vec<String> {
        let mut out: Vec<String> = live.to_vec();
        for e in exprs {
            let mut sites = Vec::new();
            collect_lambda_sites(e, &mut sites);
            for d in sites {
                for (n, _) in &self.tp.defs[d].captures {
                    if ctx.locals.contains_key(n) && !out.contains(n) {
                        out.push(n.clone());
                    }
                }
            }
        }
        out.sort();
        out
    }

    /// A simple statement inside a value block.
    fn lower_simple_stmt(&mut self, ctx: &mut FnCtx, s: &TStmt) {
        match &s.kind {
            TStmtKind::Let { name, value, .. } | TStmtKind::Assign { name, value } => {
                let t = self.lower_expr(ctx, value);
                let bt = self.bty(ctx, &value.ty, s.line);
                let tt = self.rty(ctx, &value.ty);
                self.bind_local(ctx, name, t, bt, tt);
            }
            TStmtKind::Expr(v) => {
                let t = self.lower_expr(ctx, v);
                if !matches!(t, Term::Var(_)) {
                    let bt = self.bty(ctx, &v.ty, s.line);
                    self.temp(ctx, t, bt, false);
                }
            }
            TStmtKind::Bind { name, def } => {
                let d = &self.tp.defs[*def];
                let fn_ty = self.store.instantiate(&d.scheme.clone()).0;
                let fn_ty = self.store.substitute(&fn_ty, &ctx.inst.subst);
                let (term, bt) = self.closure_value(ctx, *def, &fn_ty, s.line);
                ctx.env_of.insert(*def, name.clone());
                self.bind_local(ctx, name, term, bt, fn_ty);
            }
            _ => {}
        }
    }

    /// An expression as the body of a helper def (its own segment).
    pub fn lower_expr_body(&mut self, ctx: &mut FnCtx, e: &TExpr) -> Body {
        let saved = std::mem::take(&mut ctx.seg);
        let t = self.lower_expr(ctx, e);
        let seg = std::mem::replace(&mut ctx.seg, saved);
        self.make_body(ctx, seg, Tail::pure(t))
    }

    /// An abort in the current mode.
    pub fn abort_term(&mut self, ctx: &mut FnCtx, msg: Term, result_ty: Ty, _line: usize) -> Term {
        match ctx.mode {
            Mode::Io => {
                let call = Term::Call("IO.die".into(), vec![Term::TyArg(result_ty.clone()), Term::U32(1), msg]);
                self.temp(ctx, call, result_ty, true)
            }
            Mode::Result => {
                let call = Term::ctor("Fail", vec![msg]);
                self.temp(ctx, call, result_ty, true)
            }
            Mode::Pure => {
                // the effect analysis judged this unreachable (e.g. the
                // fallback of an exhaustive match): a pure crash if it is not
                Term::Call("F.crash".into(), vec![Term::TyArg(result_ty), msg])
            }
        }
    }

    fn lower_lit(&mut self, ctx: &mut FnCtx, l: &Lit, ty: &Type, line: usize) -> Term {
        let _ = line;
        match l {
            Lit::Int(i) => Term::U32(*i as i32 as u32),
            Lit::Float(x) => Term::F32(*x as f32),
            Lit::Str(s) => Term::Str(s.clone()),
            Lit::Bool(b) => Term::boolean(*b),
            Lit::Nothing => match self.rty(ctx, ty) {
                Type::Maybe(_) => Term::ctor("None", vec![]),
                _ => Term::unit(),
            },
        }
    }

    // -- fields --------------------------------------------------------------

    pub fn field_get(&mut self, rec: RecId, idx: usize, obj_ty: &Type, obj: Term, line: usize) -> Term {
        self.ensure_record_type(rec);
        let name = format!("{}.get_{}", self.record_type_name(rec).replace("F.", "f."), Self::mangle(&self.tp.records[rec].fields[idx].name));
        if !self.emitted_defs.contains(&name) {
            self.emitted_defs.insert(name.clone());
            let n = self.tp.records[rec].fields.len();
            let erased: Vec<String> = (0..n).map(|i| format!("T{}", i)).collect();
            let fields: Vec<(String, bool)> = (0..n).map(|i| (format!("f{}", i), false)).collect();
            let rty = Ty::Named(self.record_type_name(rec), erased.iter().map(|e| Ty::Param(e.clone())).collect());
            self.defs.push(Def {
                name: name.clone(),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased,
                params: vec![Param { name: "r".into(), reusable: false, ty: rty }],
                ret: Ty::Param(format!("T{}", idx)),
                body: Body::Match { scrutinee: "r".into(), arms: vec![(Pat::Ctor(self.record_ctor_name(rec), fields), Body::term(Term::var(&format!("f{}", idx))))] },
            });
        }
        let mut args = self.type_args_of(rec, obj_ty, line);
        args.push(obj);
        Term::Call(name, args)
    }

    pub fn field_set(&mut self, rec: RecId, idx: usize, obj_ty: &Type, obj: Term, val: Term, line: usize) -> Term {
        self.ensure_record_type(rec);
        let name = format!("{}.set_{}", self.record_type_name(rec).replace("F.", "f."), Self::mangle(&self.tp.records[rec].fields[idx].name));
        if !self.emitted_defs.contains(&name) {
            self.emitted_defs.insert(name.clone());
            let n = self.tp.records[rec].fields.len();
            let erased: Vec<String> = (0..n).map(|i| format!("T{}", i)).collect();
            let fields: Vec<(String, bool)> = (0..n).map(|i| (format!("f{}", i), false)).collect();
            let rty = Ty::Named(self.record_type_name(rec), erased.iter().map(|e| Ty::Param(e.clone())).collect());
            let rebuilt: Vec<Term> = (0..n).map(|i| if i == idx { Term::var("v") } else { Term::var(&format!("f{}", i)) }).collect();
            self.defs.push(Def {
                name: name.clone(),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased,
                params: vec![Param { name: "r".into(), reusable: false, ty: rty.clone() }, Param { name: "v".into(), reusable: false, ty: Ty::Param(format!("T{}", idx)) }],
                ret: rty,
                body: Body::Match { scrutinee: "r".into(), arms: vec![(Pat::Ctor(self.record_ctor_name(rec), fields), Body::term(Term::Ctor(self.record_ctor_name(rec), rebuilt)))] },
            });
        }
        let mut args = self.type_args_of(rec, obj_ty, line);
        args.push(obj);
        args.push(val);
        Term::Call(name, args)
    }

    /// The erased type arguments of a record value's type.
    pub fn type_args_of(&mut self, rec: RecId, obj_ty: &Type, line: usize) -> Vec<Term> {
        match self.store.resolve(obj_ty) {
            Type::Record(r, args) if r == rec => args.iter().map(|a| Term::TyArg(self.ty(a, &[], line))).collect(),
            _ => {
                let n = self.tp.records[rec].fields.len();
                (0..n).map(|_| Term::TyArg(Ty::Unit)).collect()
            }
        }
    }

    /// `obj.name`: a field read, a member through the parent chain, or a
    /// bound method value.
    fn lower_member(&mut self, ctx: &mut FnCtx, o: &TExpr, name: &str, ty: &Type, line: usize) -> Term {
        let ot = self.rty(ctx, &o.ty);
        match &ot {
            Type::Record(rec, _) => {
                let rec = *rec;
                if let Some(path) = self.member_path(rec, name) {
                    let mut cur_ty = ot.clone();
                    let mut cur = self.lower_expr(ctx, o);
                    for (r, idx) in path {
                        let next_ty = match self.store.resolve(&cur_ty) {
                            Type::Record(_, args) => args[idx].clone(),
                            _ => Type::Unit,
                        };
                        cur = self.field_get(r, idx, &cur_ty, cur, line);
                        cur_ty = next_ty;
                    }
                    return cur;
                }
                // a bound method
                if let Some(def) = crate::infer::find_method_static(&self.tp.records, &self.store, rec, name) {
                    let ft = self.rty(ctx, ty);
                    let recv = self.lower_expr(ctx, o);
                    return self.bound_method_value(ctx, def, &ft, recv, line);
                }
                self.error(line, format!("{} has no member {}", self.tp.records[rec].name, name));
                Term::unit()
            }
            Type::Result(_, _) => {
                // .ok / .err as a soft accessor is not typed; only via match
                self.error(line, "read a result with match or destructuring, not .ok/.err");
                Term::unit()
            }
            other => {
                let n = format!("{:?}", other);
                self.error(line, format!("no member .{} on {}", name, n));
                Term::unit()
            }
        }
    }

    /// The field path (record, index)* from `rec` to a member named `name`,
    /// through `__parent` fields.
    pub fn member_path(&self, rec: RecId, name: &str) -> Option<Vec<(RecId, usize)>> {
        let r = &self.tp.records[rec];
        if let Some(idx) = r.field_index(name) {
            return Some(vec![(rec, idx)]);
        }
        if let Some(pidx) = r.parent_field() {
            if let Type::Record(prec, _) = self.store.shallow(&r.field_vars[pidx]) {
                if let Some(mut rest) = self.member_path(prec, name) {
                    rest.insert(0, (rec, pidx));
                    return Some(rest);
                }
            }
        }
        None
    }

    // -- closures ------------------------------------------------------------

    /// The closure value of `def` at function type `fn_ty`, built from the
    /// current locals; returns the term and its Bend type.
    pub fn closure_value(&mut self, ctx: &mut FnCtx, def: DefId, fn_ty: &Type, line: usize) -> (Term, Ty) {
        let fn_ty = self.store.resolve(fn_ty);
        let (params, ret) = match &fn_ty {
            Type::Fn(p, r, _) => (p.clone(), (**r).clone()),
            _ => {
                self.error(line, "internal: closure of a non-function type");
                return (Term::unit(), Ty::Unit);
            }
        };
        let d = &self.tp.defs[def];
        let primary = d.template_of.unwrap_or(def);
        let captured_env = ctx.env_of.get(&def).or_else(|| ctx.env_of.get(&primary)).filter(|n| ctx.locals.contains_key(*n)).cloned();
        let env_term = if d.captures.is_empty() {
            Term::unit()
        } else if let Some(local) = captured_env {
            // the function value was captured whole: its environment is that local
            Term::Var(Self::mangle(&local))
        } else {
            let captures = d.captures.clone();
            let mut fields = Vec::new();
            for (n, _) in &captures {
                if !ctx.locals.contains_key(n) {
                    self.error(line, format!("{} is used before it is defined (captured by a nested function)", n));
                }
                fields.push(Term::Var(Self::mangle(n)));
            }
            // the env type name comes from the instance
            let inst_fn = Type::Fn(params.clone(), Box::new(ret.clone()), 0);
            let inst = self.instance_for(def, &inst_fn, line);
            let env_ty = self.instances.values().find(|i| i.name == inst).and_then(|i| i.env.clone());
            match env_ty {
                Some(Ty::Named(n, _)) => Term::Ctor(format!("{}.mk", n), fields),
                _ => Term::unit(),
            }
        };
        let rep = self.closure_rep(&fn_ty, line);
        // several possible functions: wrap in the sum
        if let Ty::Named(sum, _) = &rep.ty {
            if sum.starts_with("F.Fn") {
                let (code, _) = self.member_code_pub(def, &params, &ret, line);
                let idx = self.sum_member_index(sum, &code);
                return (Term::Ctor(format!("{}.c{}", sum, idx), vec![env_term]), rep.ty.clone());
            }
        }
        (env_term, rep.ty)
    }

    /// A method bound to a receiver as a value.
    fn bound_method_value(&mut self, ctx: &mut FnCtx, def: DefId, fn_ty: &Type, recv: Term, line: usize) -> Term {
        let _ = ctx;
        let fn_ty = self.store.resolve(fn_ty);
        let (params, ret) = match &fn_ty {
            Type::Fn(p, r, _) => (p.clone(), (**r).clone()),
            _ => return Term::unit(),
        };
        // make sure the closure set knows this method
        if let Type::Fn(_, _, c) = &fn_ty {
            self.store.clos_add(*c, def);
        }
        let (code, env_ty) = self.member_code_pub(def, &params, &ret, line);
        let env_name = match &env_ty {
            Ty::Named(n, _) => n.clone(),
            _ => return Term::unit(),
        };
        let env_term = Term::Ctor(format!("{}.mk", env_name), vec![recv]);
        let rep = self.closure_rep(&fn_ty, line);
        if let Ty::Named(sum, _) = &rep.ty {
            if sum.starts_with("F.Fn") {
                let idx = self.sum_member_index(sum, &code);
                return Term::Ctor(format!("{}.c{}", sum, idx), vec![env_term]);
            }
        }
        env_term
    }

    pub fn sum_member_index(&self, sum: &str, code: &str) -> usize {
        for t in &self.types {
            if t.name == sum {
                for (i, (_, _)) in t.ctors.iter().enumerate() {
                    let _ = i;
                }
            }
        }
        // the ctor list was built from sorted codes; recover the order from
        // the apply def
        let apply = format!("{}.apply", sum);
        if let Some(d) = self.defs.iter().find(|d| d.name == apply) {
            if let Body::Match { arms, .. } = &d.body {
                for (i, (_, b)) in arms.iter().enumerate() {
                    if let Body::Block { tail: Term::Call(f, _), .. } = b {
                        if f == code {
                            return i;
                        }
                    }
                }
            }
        }
        0
    }

    /// The mode of calling a function value of this type.
    pub fn rep_mode(&mut self, fn_ty: &Type) -> Mode {
        match fn_ty {
            Type::Fn(_, _, c) => {
                let set = self.store.clos_set(*c);
                let members: Vec<DefId> = set.into_iter().collect();
                self.set_mode(&members)
            }
            _ => Mode::Pure,
        }
    }

    // -- calls ---------------------------------------------------------------

    fn lower_call(&mut self, ctx: &mut FnCtx, def: DefId, args: &[TExpr], ret: &Type, line: usize) -> Term {
        let arg_tys: Vec<Type> = args.iter().map(|a| self.rty(ctx, &a.ty)).collect();
        let ret_t = self.rty(ctx, ret);
        let fn_ty = Type::Fn(arg_tys, Box::new(ret_t.clone()), 0);
        let inst = self.instance_for(def, &fn_ty, line);
        let info = self.instances.values().find(|i| i.name == inst).cloned().expect("instance");
        let mut targs: Vec<Term> = Vec::new();
        if info.env.is_some() {
            // a template copy shares the environment of the def it copies
            let primary = self.tp.defs[def].template_of.unwrap_or(def);
            let env_local = ctx.env_of.get(&def).or_else(|| ctx.env_of.get(&primary)).cloned();
            if def == ctx.inst.def || primary == ctx.inst.def {
                targs.push(Term::var("env"));
            } else if let Some(local) = env_local {
                targs.push(Term::Var(Self::mangle(&local)));
            } else {
                let d = &self.tp.defs[def];
                self.error(line, format!("{} is called before its definition and captures local variables", d.name));
                targs.push(Term::unit());
            }
        }
        for a in args {
            targs.push(self.lower_expr(ctx, a));
        }
        let call = Term::Call(inst, targs);
        let rt = self.ty(&ret_t, &[], line);
        self.adapt_call(ctx, call, info.mode, rt, line)
    }

    /// `recv.name(args)`. Returns the term and, for a mutating method, the
    /// statements that rebind the receiver were already pushed.
    pub fn lower_method_call(&mut self, ctx: &mut FnCtx, recv: &TExpr, name: &str, args: &[TExpr], ret: &Type, line: usize, _stmt_pos: bool) -> (Term, bool) {
        let rt_t = self.rty(ctx, &recv.ty);
        if let Type::Stream(_) = rt_t {
            return (self.lower_stream_method(ctx, recv, name, args, ret, line), false);
        }
        match &rt_t {
            Type::Record(rec, _) => {
                let rec = *rec;
                if let Some(def) = crate::infer::find_method_static(&self.tp.records, &self.store, rec, name) {
                    return self.lower_class_method_call(ctx, recv, rec, def, args, ret, line);
                }
                if let Some(path) = self.member_path(rec, name) {
                    // a function-valued field
                    let fty = match self.field_type_along(&rt_t, &path) {
                        Some(t) => t,
                        None => Type::Unit,
                    };
                    let rep = self.closure_rep(&fty, line);
                    let mut cur_ty = rt_t.clone();
                    let mut cur = self.lower_expr(ctx, recv);
                    for (r, idx) in path {
                        let next_ty = match self.store.resolve(&cur_ty) {
                            Type::Record(_, a) => a[idx].clone(),
                            _ => Type::Unit,
                        };
                        cur = self.field_get(r, idx, &cur_ty, cur, line);
                        cur_ty = next_ty;
                    }
                    let mut targs = vec![cur];
                    for a in args {
                        targs.push(self.lower_expr(ctx, a));
                    }
                    return match rep.code {
                        Some(code) => {
                            let mode = self.rep_mode(&fty);
                            let rt = self.bty(ctx, ret, line);
                            let call = Term::Call(code, targs);
                            (self.adapt_call(ctx, call, mode, rt, line), false)
                        }
                        None => {
                            self.error(line, "this function value has no known origin");
                            (Term::unit(), false)
                        }
                    };
                }
                // record builtins
                let recv_t = self.lower_expr(ctx, recv);
                (self.lower_record_builtin(ctx, rec, &rt_t, name, recv_t, args, ret, line), false)
            }
            _ => {
                let recv_t = self.lower_expr(ctx, recv);
                let targs: Vec<Term> = args.iter().map(|a| self.lower_expr(ctx, a)).collect();
                let arg_tys: Vec<Type> = args.iter().map(|a| self.rty(ctx, &a.ty)).collect();
                let arg_exprs: Vec<&TExpr> = args.iter().collect();
                (self.lower_builtin_method(ctx, &rt_t, name, recv_t, targs, &arg_tys, &arg_exprs, ret, line), false)
            }
        }
    }

    fn field_type_along(&mut self, start: &Type, path: &[(RecId, usize)]) -> Option<Type> {
        let mut cur = self.store.resolve(start);
        for (_, idx) in path {
            match cur {
                Type::Record(_, args) => cur = self.store.resolve(&args[*idx]),
                _ => return None,
            }
        }
        Some(cur)
    }

    fn lower_class_method_call(&mut self, ctx: &mut FnCtx, recv: &TExpr, rec: RecId, def: DefId, args: &[TExpr], ret: &Type, line: usize) -> (Term, bool) {
        let d = &self.tp.defs[def];
        let mutates = matches!(d.kind, DefKind::Method { mutates: true, .. });
        let owner = match &d.kind {
            DefKind::Method { rec, .. } => *rec,
            _ => rec,
        };
        // the receiver as seen by the method: walk up to the owner class
        let recv_t = self.rty(ctx, &recv.ty);
        let mut path: Vec<(RecId, usize)> = Vec::new();
        let mut cur_rec = rec;
        let mut cur_ty = recv_t.clone();
        while cur_rec != owner {
            let pidx = match self.tp.records[cur_rec].parent_field() {
                Some(p) => p,
                None => break,
            };
            path.push((cur_rec, pidx));
            cur_ty = match self.store.resolve(&cur_ty) {
                Type::Record(_, a) => self.store.resolve(&a[pidx]),
                _ => break,
            };
            cur_rec = match &cur_ty {
                Type::Record(r, _) => *r,
                _ => break,
            };
        }
        let arg_tys: Vec<Type> = args.iter().map(|a| self.rty(ctx, &a.ty)).collect();
        let ret_t = self.rty(ctx, ret);
        let mut full = vec![cur_ty.clone()];
        full.extend(arg_tys);
        let fn_ty = Type::Fn(full, Box::new(ret_t.clone()), 0);
        let inst = self.instance_for(def, &fn_ty, line);
        let info = self.instances.values().find(|i| i.name == inst).cloned().expect("instance");
        // receiver value (through the parent path)
        let root = self.lower_expr(ctx, recv);
        let mut recv_term = root.clone();
        let mut walk_ty = recv_t.clone();
        for (r, idx) in &path {
            let next = match self.store.resolve(&walk_ty) {
                Type::Record(_, a) => a[*idx].clone(),
                _ => Type::Unit,
            };
            recv_term = self.field_get(*r, *idx, &walk_ty, recv_term, line);
            walk_ty = next;
        }
        let mut targs = vec![recv_term];
        for a in args {
            targs.push(self.lower_expr(ctx, a));
        }
        let rt = self.ty(&ret_t, &[], line);
        let call = Term::Call(inst, targs);
        if !mutates {
            return (self.adapt_call(ctx, call, info.mode, rt, line), false);
        }
        // mutating: the call answers the new receiver (and the value)
        let owner_bt = self.ty(&cur_ty, &[], line);
        let has_value = rt != Ty::Unit;
        let result_bt = if has_value { Ty::Named("F.Ret".into(), vec![owner_bt.clone(), rt.clone()]) } else { owner_bt.clone() };
        let r = self.adapt_call(ctx, call, info.mode, result_bt.clone(), line);
        let r = self.temp(ctx, r, result_bt.clone(), false);
        let (new_owner, value) = if has_value {
            let fst = Term::Call("F.ret.self".into(), vec![Term::TyArg(owner_bt.clone()), Term::TyArg(rt.clone()), r.clone()]);
            let snd = Term::Call("F.ret.value".into(), vec![Term::TyArg(owner_bt), Term::TyArg(rt.clone()), r]);
            (fst, snd)
        } else {
            (r, Term::unit())
        };
        // rebuild the receiver root with the owner replaced along the path
        let new_root = self.rebuild_along(&recv_t, root, &path, new_owner, line);
        self.rebind_receiver(ctx, recv, new_root, line);
        (value, true)
    }

    /// Rebuild `root` (of type `root_ty`) with the value at `path` replaced.
    fn rebuild_along(&mut self, root_ty: &Type, root: Term, path: &[(RecId, usize)], new_inner: Term, line: usize) -> Term {
        if path.is_empty() {
            return new_inner;
        }
        let (r, idx) = path[0];
        let inner_ty = match self.store.resolve(root_ty) {
            Type::Record(_, a) => a[idx].clone(),
            _ => Type::Unit,
        };
        let inner = self.field_get(r, idx, root_ty, root.clone(), line);
        let new_sub = self.rebuild_along(&inner_ty, inner, &path[1..], new_inner, line);
        self.field_set(r, idx, root_ty, root, new_sub, line)
    }

    /// Rebind the variable at the root of a receiver expression.
    fn rebind_receiver(&mut self, ctx: &mut FnCtx, recv: &TExpr, new_value: Term, line: usize) {
        match &recv.kind {
            TExprKind::Local(n) => {
                let l = ctx.locals[n].clone();
                self.bind_local(ctx, n, new_value, l.ty, l.tt);
            }
            TExprKind::SelfValue(rec) => {
                // rebind every member local from the new record
                let rec = *rec;
                let self_ty = self.rty(ctx, &recv.ty);
                let sbt = self.ty(&self_ty, &[], line);
                let tmp = self.temp(ctx, new_value, sbt, false);
                let fields: Vec<(String, Type)> = match self.store.resolve(&self_ty) {
                    Type::Record(_, args) => self.tp.records[rec].fields.iter().zip(args.iter()).map(|(f, t)| (f.name.clone(), t.clone())).collect(),
                    _ => vec![],
                };
                for (i, (fname, ft)) in fields.iter().enumerate() {
                    let get = self.field_get(rec, i, &self_ty, tmp.clone(), line);
                    let bt = self.ty(ft, &[], line);
                    self.bind_local(ctx, fname, get, bt, ft.clone());
                }
            }
            TExprKind::Field(inner, r, idx) => {
                let inner_ty = self.rty(ctx, &inner.ty);
                let inner_term = self.lower_expr(ctx, inner);
                let rebuilt = self.field_set(*r, *idx, &inner_ty, inner_term, new_value, line);
                self.rebind_receiver(ctx, inner, rebuilt, line);
            }
            TExprKind::Member(inner, name) => {
                let inner_ty = self.rty(ctx, &inner.ty);
                if let Type::Record(rec, _) = &inner_ty {
                    if let Some(path) = self.member_path(*rec, name) {
                        let inner_term = self.lower_expr(ctx, inner);
                        let rebuilt = self.rebuild_along(&inner_ty, inner_term, &path, new_value, line);
                        self.rebind_receiver(ctx, inner, rebuilt, line);
                        return;
                    }
                }
                self.error(line, "cannot rebind this receiver");
            }
            _ => {
                // a temporary (`Make().mutate()`): the updated object is dropped
            }
        }
    }

    // -- pipelines -----------------------------------------------------------

    /// The code def and env term for a stage/callback function value: a
    /// template reference to the code plus the environment value.
    pub fn stage_parts(&mut self, ctx: &mut FnCtx, func: &TExpr, line: usize) -> Option<(String, Term, Ty, Mode)> {
        let ft = self.rty(ctx, &func.ty);
        let rep = self.closure_rep(&ft, line);
        let env = self.lower_expr(ctx, func);
        let mode = self.rep_mode(&ft);
        match rep.code {
            Some(code) => {
                let w = self.tmpl_wrapper(&code);
                Some((w, env, rep.ty, mode))
            }
            None => {
                self.error(line, "this function value has no known origin and cannot be applied");
                None
            }
        }
    }

    /// `.take(n)`, `.first()`, `.drop(n)` (and index/slice) on a lazy stream:
    /// a bounded pull loop in a helper def.
    pub fn lower_stream_method(&mut self, ctx: &mut FnCtx, recv: &TExpr, name: &str, args: &[TExpr], ret: &Type, line: usize) -> Term {
        let elem_tt = match self.rty(ctx, &recv.ty) {
            Type::Stream(e) => (*e).clone(),
            _ => Type::Int,
        };
        match name {
            "take" => self.stream_take(ctx, recv, &args[0], &elem_tt, line),
            "first" => {
                let one = TExpr { kind: TExprKind::Lit(Lit::Int(1)), ty: Type::Int, line };
                let list = self.stream_take(ctx, recv, &one, &elem_tt, line);
                let ebt = self.ty(&elem_tt, &[], line);
                let call = Term::Call("F.list.head_or_abort".into(), vec![Term::TyArg(ebt.clone()), list]);
                self.adapt_call(ctx, call, Mode::Result, ebt, line)
            }
            _ => {
                let _ = ret;
                self.error(line, format!(".{}() on a lazy stream is not supported", name));
                Term::unit()
            }
        }
    }


    fn lower_pipe(&mut self, ctx: &mut FnCtx, left: &TExpr, func: &TExpr, ret: &Type, line: usize) -> Term {
        let lt = self.rty(ctx, &left.ty);
        if let Type::Stream(_) = lt {
            // `stream |> $.take(n)`: inline the lambda's body over the stream
            if let TExprKind::Lambda(def) = &func.kind {
                let d = &self.tp.defs[*def];
                let body_expr = match d.body.stmts.as_slice() {
                    [TStmt { kind: TStmtKind::Return(Some(e)), .. }] | [TStmt { kind: TStmtKind::Expr(e), .. }] => Some(e.clone()),
                    _ => None,
                };
                if let (Some(e), Some(p)) = (body_expr, d.params.first()) {
                    let pname = p.name.clone();
                    let saved = ctx.stream_aliases.get(&pname).cloned();
                    ctx.stream_aliases.insert(pname.clone(), left.clone());
                    ctx.locals.insert(pname.clone(), Local { ty: Ty::Unit, tt: lt.clone() });
                    let t = self.lower_expr(ctx, &e);
                    match saved {
                        Some(s) => {
                            ctx.stream_aliases.insert(pname, s);
                        }
                        None => {
                            ctx.stream_aliases.remove(&pname);
                        }
                    }
                    return t;
                }
            }
            self.error(line, "a lazy stream can only be piped into a `$` expression that consumes it (.take, .first, [..n])");
            return Term::unit();
        }
        let l = self.lower_expr(ctx, left);
        let (code, env, env_ty, fmode) = match self.stage_parts(ctx, func, line) {
            Some(p) => p,
            None => return Term::unit(),
        };
        let rt = self.bty(ctx, ret, line);
        match lt {
            Type::Result(e, a) => {
                // railway: bind through the result
                let ebt = self.ty(&e, &[], line);
                let abt = self.ty(&a, &[], line);
                let f_ret = match self.store.resolve(&func.ty) {
                    Type::Fn(_, r, _) => self.ty(&self.store.resolve(&r), &[], line),
                    _ => Ty::Unit,
                };
                let f_returns_result = matches!(f_ret, Ty::Result(_, _));
                let helper = match (fmode, f_returns_result) {
                    (Mode::Pure, false) => "F.result.map_env",
                    (Mode::Pure, true) => "F.result.bind_env",
                    (Mode::Result, false) => "F.result.map_res_env",
                    (Mode::Result, true) => "F.result.bind_res_env",
                    (Mode::Io, false) => "F.result.map_io_env",
                    (Mode::Io, true) => "F.result.bind_io_env",
                };
                let out_val = match &rt {
                    Ty::Result(_, v) => (**v).clone(),
                    _ => rt.clone(),
                };
                let call = Term::Call(helper.into(), vec![Term::TmplTy(env_ty), Term::TmplTy(ebt), Term::TmplTy(abt), Term::TmplTy(out_val), Term::TmplRef(code), env, l]);
                match fmode {
                    Mode::Pure => call,
                    m => self.adapt_call(ctx, call, m, rt, line),
                }
            }
            _ => {
                let call = Term::Call(code, vec![env, l]);
                self.adapt_call(ctx, call, fmode, rt, line)
            }
        }
    }

    fn lower_stage(&mut self, ctx: &mut FnCtx, op: StageOp, input: &TExpr, func: &TExpr, ret: &Type, line: usize) -> Term {
        let it = self.rty(ctx, &input.ty);
        // a stage over a stream stays a stream: it is consumed elsewhere
        if let Type::Stream(_) = it {
            self.error(line, "internal: a stream stage reached the lowering; streams are consumed by take/first/for");
            return Term::unit();
        }
        let (elem_t, is_result_list) = match &it {
            Type::List(e) => ((**e).clone(), false),
            Type::Range => (Type::Int, false),
            Type::Result(_, a) => match self.store.resolve(a) {
                Type::List(e) => ((*e).clone(), true),
                _ => (Type::Unit, true),
            },
            _ => (Type::Unit, false),
        };
        let mut inp = self.lower_expr(ctx, input);
        if let Type::Range = it {
            inp = Term::Call("F.range.list".into(), vec![inp]);
        }
        let (code, env, env_ty, fmode) = match self.stage_parts(ctx, func, line) {
            Some(p) => p,
            None => return Term::unit(),
        };
        let rt = self.bty(ctx, ret, line);
        let elem_bt = self.ty(&elem_t, &[], line);
        // per-element railway: elements that are results
        let elem_is_result = matches!(elem_bt, Ty::Result(_, _));
        let (in_bt, out_bt) = match (&elem_bt, &rt) {
            (Ty::Result(_, a), Ty::List(o)) => match &**o {
                Ty::Result(_, ov) => ((**a).clone(), (**ov).clone()),
                other => ((**a).clone(), other.clone()),
            },
            (_, Ty::List(o)) => (elem_bt.clone(), (**o).clone()),
            (_, Ty::Result(_, inner)) => match &**inner {
                Ty::List(o) => (elem_bt.clone(), (**o).clone()),
                _ => (elem_bt.clone(), Ty::Unit),
            },
            _ => (elem_bt.clone(), Ty::Unit),
        };
        let base = match (op, elem_is_result) {
            (StageOp::Map, false) => "F.list.map",
            (StageOp::Filter, false) => "F.list.filter",
            (StageOp::Map, true) => "F.list.rmap",
            (StageOp::Filter, true) => "F.list.rfilter",
        };
        let suffix = match fmode {
            Mode::Pure => "_env",
            Mode::Result => "_res_env",
            Mode::Io => "_io_env",
        };
        let helper = format!("{}{}", base, suffix);
        let mut targs = vec![Term::TmplTy(env_ty), Term::TmplTy(in_bt)];
        if op == StageOp::Map {
            targs.push(Term::TmplTy(out_bt));
        }
        if elem_is_result {
            if let Ty::Result(e, _) = &elem_bt {
                targs.push(Term::TmplTy((**e).clone()));
            }
        }
        targs.push(Term::TmplRef(code));
        targs.push(env);
        if is_result_list {
            // the whole input is a result: map inside it
            let list_bt = match &rt {
                Ty::Result(_, l) => (**l).clone(),
                other => other.clone(),
            };
            let ebt = match &rt {
                Ty::Result(e, _) => (**e).clone(),
                _ => Ty::Str,
            };
            let in_list_bt = self.ty(&it, &[], line);
            let in_list_bt = match in_list_bt {
                Ty::Result(_, l) => *l,
                other => other,
            };
            // build a stage over lists as a lambda-free call: F.result.map_list
            let stage_env = self.fresh("__stage");
            let _ = stage_env;
            // simplest: bind the result, then match via prelude helper taking the inner list mapper
            let inner_call_name = self.fresh(&format!("{}.rstage", ctx.base));
            // helper: (env, xs) -> mapped list (in fmode)
            let mut args2 = targs.clone();
            args2.push(Term::var("xs"));
            let inner = Term::Call(helper.clone(), args2);
            let env_param_ty = match &targs[0] {
                Term::TmplTy(t) => t.clone(),
                _ => Ty::Unit,
            };
            let body = Body::term(inner);
            let mut hdef = Def {
                name: inner_call_name.clone(),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased: vec![],
                params: vec![Param { name: "env".into(), reusable: false, ty: env_param_ty }, Param { name: "xs".into(), reusable: false, ty: in_list_bt }],
                ret: fmode.wrap(list_bt.clone()),
                body,
            };
            // the env term was consumed into targs; the helper's env comes from the caller
            hdef.params[0].name = "env".into();
            self.finish_def(&mut hdef);
            self.emitted_defs.insert(inner_call_name.clone());
            self.defs.push(hdef);
            let env_term = targs[targs.len() - 1].clone();
            let rhelper = match fmode {
                Mode::Pure => "F.result.map_env",
                Mode::Result => "F.result.map_res_env",
                Mode::Io => "F.result.map_io_env",
            };
            let env_ty2 = match &targs[0] {
                Term::TmplTy(t) => t.clone(),
                _ => Ty::Unit,
            };
            let call = Term::Call(rhelper.into(), vec![Term::TmplTy(env_ty2), Term::TmplTy(ebt), Term::TmplTy(match self.ty(&it, &[], line) { Ty::Result(_, l) => *l, o => o }), Term::TmplTy(list_bt), Term::TmplRef(inner_call_name), env_term, inp]);
            return match fmode {
                Mode::Pure => call,
                m => self.adapt_call(ctx, call, m, rt, line),
            };
        }
        targs.push(inp);
        let call = Term::Call(helper, targs);
        match fmode {
            Mode::Pure => call,
            m => self.adapt_call(ctx, call, m, rt, line),
        }
    }

    fn lower_handle(&mut self, ctx: &mut FnCtx, left: &TExpr, handler: &TExpr, is_func: bool, ret: &Type, line: usize) -> Term {
        let lt = self.rty(ctx, &left.ty);
        let l = self.lower_expr(ctx, left);
        let rt = self.bty(ctx, ret, line);
        match &lt {
            Type::Result(e, a) => {
                let ebt = self.ty(e, &[], line);
                let abt = self.ty(a, &[], line);
                if !is_func {
                    let h = self.lower_expr(ctx, handler);
                    return Term::Call("F.result.or".into(), vec![Term::TyArg(ebt), Term::TyArg(abt), l, h]);
                }
                let (code, env, env_ty, fmode) = match self.stage_parts(ctx, handler, line) {
                    Some(p) => p,
                    None => return Term::unit(),
                };
                let helper = match fmode {
                    Mode::Pure => "F.result.handle_env",
                    Mode::Result => "F.result.handle_res_env",
                    Mode::Io => "F.result.handle_io_env",
                };
                let call = Term::Call(helper.into(), vec![Term::TmplTy(env_ty), Term::TmplTy(ebt), Term::TmplTy(abt), Term::TmplRef(code), env, l]);
                match fmode {
                    Mode::Pure => call,
                    m => self.adapt_call(ctx, call, m, rt, line),
                }
            }
            Type::List(elem) => match self.store.resolve(elem) {
                Type::Result(e, a) => {
                    let ebt = self.ty(&e, &[], line);
                    let abt = self.ty(&a, &[], line);
                    if !is_func {
                        let h = self.lower_expr(ctx, handler);
                        return Term::Call("F.list.rhandle_value".into(), vec![Term::TyArg(ebt), Term::TyArg(abt), l, h]);
                    }
                    let (code, env, env_ty, fmode) = match self.stage_parts(ctx, handler, line) {
                        Some(p) => p,
                        None => return Term::unit(),
                    };
                    let helper = match fmode {
                        Mode::Pure => "F.list.rhandle_env",
                        Mode::Result => "F.list.rhandle_res_env",
                        Mode::Io => "F.list.rhandle_io_env",
                    };
                    let call = Term::Call(helper.into(), vec![Term::TmplTy(env_ty), Term::TmplTy(ebt), Term::TmplTy(abt), Term::TmplRef(code), env, l]);
                    match fmode {
                        Mode::Pure => call,
                        m => self.adapt_call(ctx, call, m, rt, line),
                    }
                }
                _ => l,
            },
            _ => l,
        }
    }

    // -- conditions ----------------------------------------------------------

    /// A Bool term for the truthiness of an expression.
    pub fn lower_cond(&mut self, ctx: &mut FnCtx, e: &TExpr) -> Term {
        let t = self.rty(ctx, &e.ty);
        let v = self.lower_expr(ctx, e);
        match t {
            Type::Bool => v,
            Type::Int => Term::Call("U32.is_ne".into(), vec![v, Term::U32(0)]),
            Type::Float => Term::Call("F32.is_ne".into(), vec![v, Term::F32(0.0)]),
            Type::Str => Term::Call("Bool.not".into(), vec![Term::Call("String.is_empty".into(), vec![v])]),
            Type::Maybe(inner) => {
                let ibt = self.ty(&inner, &[], e.line);
                Term::Call("Maybe.is_some".into(), vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(ibt), v])
            }
            Type::Unit => Term::boolean(false),
            _ => Term::boolean(true),
        }
    }

    // -- match ---------------------------------------------------------------

    /// Emit the arm-chain helpers for a match; returns the first helper's
    /// name (which takes the live variables and then the subject).
    pub fn lower_match_arms(&mut self, ctx: &mut FnCtx, arms: &[TArm], live: &[String], sty: Ty, stt: Type, kind: MatchKind, line: usize) -> String {
        let base = self.fresh(&format!("{}.m", ctx.base));
        let result = match &kind {
            MatchKind::Stmt(_) => ctx.result.clone(),
            MatchKind::Expr(t) => t.clone(),
        };
        let mut next_name: Option<String> = None;
        // arms from last to first: each arm's failure calls the next
        for (i, arm) in arms.iter().enumerate().rev() {
            let name = format!("{}.a{}", base, i);
            let fail = match &next_name {
                Some(n) => Term::Call(n.clone(), {
                    let mut a: Vec<Term> = live.iter().map(|l| Term::Var(Self::mangle(l))).collect();
                    a.push(Term::var("__subject"));
                    a
                }),
                None => Term::Str("no matching arm".into()),
            };
            let is_fail_abort = next_name.is_none();
            let mut actx = self.sub_ctx(ctx, live);
            actx.result = result.clone();
            actx.locals.insert("__subject".into(), Local { ty: sty.clone(), tt: stt.clone() });
            let body = self.lower_arm(&mut actx, arm, "__subject", &stt, &kind, fail, is_fail_abort, line);
            self.emit_helper(&actx, name.clone(), live, vec![Param { name: "__subject".into(), reusable: true, ty: sty.clone() }], result.clone(), body);
            next_name = Some(name);
        }
        match next_name {
            Some(n) => n,
            None => {
                // no arms: abort
                let name = format!("{}.a0", base);
                let mut actx = self.sub_ctx(ctx, live);
                actx.result = result.clone();
                let t = self.abort_term(&mut actx, Term::Str("no matching arm".into()), result.clone(), line);
                let seg = std::mem::take(&mut actx.seg);
                let body = self.make_body(&actx, seg, Tail::pure(t));
                self.emit_helper(&actx, name.clone(), live, vec![Param { name: "__subject".into(), reusable: true, ty: sty }], result, body);
                name
            }
        }
    }

    /// One arm: nested constructor matches on the subject, then literal
    /// tests and the guard, then the body; failure runs `fail`.
    fn lower_arm(&mut self, ctx: &mut FnCtx, arm: &TArm, subject: &str, stt: &Type, kind: &MatchKind, fail: Term, fail_aborts: bool, line: usize) -> Body {
        let mut plan = PatPlan::default();
        self.plan_pattern(ctx, &arm.pattern, subject.to_string(), stt, &mut plan);
        // the fail body
        let fail_body = |lw: &mut Self, ctx: &mut FnCtx| -> Body {
            if fail_aborts {
                let mut fctx = lw.sub_ctx(ctx, &[]);
                fctx.locals = ctx.locals.clone();
                fctx.result = ctx.result.clone();
                let t = lw.abort_term(&mut fctx, fail.clone(), ctx.result.clone(), line);
                let seg = std::mem::take(&mut fctx.seg);
                lw.make_body(&fctx, seg, Tail::pure(t))
            } else {
                lw.make_body(ctx, vec![], Tail::call(fail.clone(), ctx.mode))
            }
        };
        // innermost: bindings, tests, guard, body
        let inner = {
            let mut ictx = self.sub_ctx(ctx, &ctx.locals.keys().cloned().collect::<Vec<_>>());
            ictx.locals = ctx.locals.clone();
            for (var, ty) in &plan.vars {
                let bt = self.ty(ty, &[], line);
                ictx.locals.insert(var.clone(), Local { ty: bt, tt: ty.clone() });
            }
            for (name, var, ty) in &plan.binds {
                let bt = self.ty(ty, &[], line);
                ictx.locals.insert(name.clone(), Local { ty: bt.clone(), tt: ty.clone() });
                ictx.seg.push(Stmt::Let { name: Self::mangle(name), reusable: false, ty: if ictx.mode == Mode::Pure { None } else { Some(bt) }, value: Term::var(var) });
            }
            // tests then guard: a chain of Bool helpers
            let mut tests: Vec<TExpr> = Vec::new();
            for (var, lit, ty) in &plan.tests {
                tests.push(TExpr {
                    kind: TExprKind::BinOp(BinOp::Eq, Box::new(TExpr { kind: TExprKind::Local(var.clone()), ty: ty.clone(), line }), Box::new(TExpr { kind: TExprKind::Lit(lit.clone()), ty: ty.clone(), line })),
                    ty: Type::Bool,
                    line,
                });
                ictx.locals.insert(var.clone(), Local { ty: self.ty(ty, &[], line), tt: ty.clone() });
            }
            if let Some(g) = &arm.guard {
                tests.push(g.clone());
            }
            self.lower_arm_tests(&mut ictx, &tests, arm, kind, fail.clone(), fail_aborts, line)
        };
        // wrap in the nested constructor matches (outermost first)
        let mut body = inner;
        for (var, pat) in plan.matches.into_iter().rev() {
            let fb = fail_body(self, ctx);
            let arms = vec![(pat, body), (Pat::Wild, fb)];
            body = Body::Match { scrutinee: var, arms };
        }
        body
    }

    /// Tests (Bool expressions) evaluated in order; all must hold.
    fn lower_arm_tests(&mut self, ctx: &mut FnCtx, tests: &[TExpr], arm: &TArm, kind: &MatchKind, fail: Term, fail_aborts: bool, line: usize) -> Body {
        if tests.is_empty() {
            // the arm body
            let seg_before = std::mem::take(&mut ctx.seg);
            let tail = match kind {
                MatchKind::Stmt(k) => {
                    let k = k.clone();
                    if let TExprKind::Block(b) = &arm.body.kind {
                        // a statement arm (e.g. `xs.push(v)`): its assignments
                        // flow into the continuation
                        self.lower_stmts_pub(ctx, &b.stmts, k)
                    } else {
                        let t = self.lower_expr(ctx, &arm.body);
                        if !matches!(t, Term::Var(_)) {
                            let bt = self.bty(ctx, &arm.body.ty, line);
                            self.temp(ctx, t, bt, false);
                        }
                        self.apply_cont(ctx, &k, None)
                    }
                }
                MatchKind::Expr(_) => {
                    let t = self.lower_expr(ctx, &arm.body);
                    Tail::pure(t)
                }
            };
            let mut seg = seg_before;
            seg.append(&mut ctx.seg);
            return self.make_body(ctx, seg, tail);
        }
        let c = self.lower_cond(ctx, &tests[0]);
        let live: Vec<String> = {
            let mut names = HashSet::new();
            for t in &tests[1..] {
                free_expr(t, &mut names);
            }
            free_expr(&arm.body, &mut names);
            if let MatchKind::Stmt(k) = kind {
                for n in self.cont_live(ctx, k) {
                    names.insert(n);
                }
            }
            // a statement arm may return the receiver (mutating method): the
            // member locals stay live; an expression arm only answers a value
            if let MatchKind::Stmt(_) = kind {
                for n in self.ret_live(ctx) {
                    names.insert(n);
                }
            }
            // the fail continuation needs the subject and the live set
            names.insert("__subject".into());
            let mut fail_counts = HashMap::new();
            fail.count_vars(&mut fail_counts);
            for n in ctx.locals.keys() {
                if fail_counts.contains_key(&Self::mangle(n)) {
                    names.insert(n.clone());
                }
            }
            let mut v: Vec<String> = names.into_iter().filter(|n| ctx.locals.contains_key(n)).collect();
            v.sort();
            v
        };
        let live = self.with_captures(ctx, &live, &[&arm.body]);
        let name = self.fresh(&format!("{}.t", ctx.base));
        let mut tctx = self.sub_ctx(ctx, &live);
        tctx.result = ctx.result.clone();
        let then_body = self.lower_arm_tests(&mut tctx, &tests[1..], arm, kind, fail.clone(), fail_aborts, line);
        let else_body = if fail_aborts {
            let mut fctx = self.sub_ctx(ctx, &live);
            fctx.result = ctx.result.clone();
            let t = self.abort_term(&mut fctx, fail, ctx.result.clone(), line);
            let seg = std::mem::take(&mut fctx.seg);
            self.make_body(&fctx, seg, Tail::pure(t))
        } else {
            self.make_body(ctx, vec![], Tail::call(fail, ctx.mode))
        };
        let body = Body::Match { scrutinee: "__c".into(), arms: vec![(Pat::Ctor("True".into(), vec![]), then_body), (Pat::Ctor("False".into(), vec![]), else_body)] };
        self.emit_helper(&tctx, name.clone(), &live, vec![Param { name: "__c".into(), reusable: false, ty: Ty::Bool }], ctx.result.clone(), body);
        let seg = std::mem::take(&mut ctx.seg);
        let call = self.call_helper(&name, &live, vec![c]);
        self.make_body(ctx, seg, Tail::call(call, ctx.mode))
    }

    /// Plan a pattern over a variable: constructor matches (in order),
    /// name bindings, and literal tests.
    fn plan_pattern(&mut self, ctx: &mut FnCtx, p: &TPattern, var: String, ty: &Type, plan: &mut PatPlan) {
        let ty = self.store.resolve(ty);
        match p {
            TPattern::Bind(n) => plan.binds.push((n.clone(), var, ty)),
            TPattern::Wild => {}
            TPattern::Lit(l) => plan.tests.push((var, l.clone(), ty)),
            TPattern::None => plan.matches.push((var, Pat::Ctor("None".into(), vec![]))),
            TPattern::Some(inner) => {
                let v = self.fresh("__p");
                plan.matches.push((var, Pat::Ctor("Some".into(), vec![(v.clone(), true)])));
                let it = match &ty {
                    Type::Maybe(i) => (**i).clone(),
                    _ => Type::Unit,
                };
                plan.vars.push((v.clone(), it.clone()));
                self.plan_pattern(ctx, inner, v, &it, plan);
            }
            TPattern::Ok(inner) | TPattern::Err(inner) => {
                let is_ok = matches!(p, TPattern::Ok(_));
                let v = self.fresh("__p");
                plan.matches.push((var, Pat::Ctor(if is_ok { "Done" } else { "Fail" }.into(), vec![(v.clone(), true)])));
                let it = match &ty {
                    Type::Result(e, a) => {
                        if is_ok { (**a).clone() } else { (**e).clone() }
                    }
                    _ => Type::Unit,
                };
                plan.vars.push((v.clone(), it.clone()));
                self.plan_pattern(ctx, inner, v, &it, plan);
            }
            TPattern::List(items, rest) => {
                let elem = match &ty {
                    Type::List(e) => (**e).clone(),
                    _ => Type::Unit,
                };
                let mut cur = var;
                for item in items {
                    let h = self.fresh("__h");
                    let t = self.fresh("__t");
                    plan.matches.push((cur.clone(), Pat::Ctor("Con".into(), vec![(h.clone(), true), (t.clone(), true)])));
                    plan.vars.push((h.clone(), elem.clone()));
                    plan.vars.push((t.clone(), ty.clone()));
                    self.plan_pattern(ctx, item, h, &elem, plan);
                    cur = t;
                }
                match rest {
                    None => plan.matches.push((cur, Pat::Ctor("Nil".into(), vec![]))),
                    Some(Some(name)) => plan.binds.push((name.clone(), cur, ty.clone())),
                    Some(None) => {}
                }
            }
            TPattern::Record(rec, fields) => {
                self.ensure_record_type(*rec);
                let n = self.tp.records[*rec].fields.len();
                let names: Vec<String> = (0..n).map(|_| self.fresh("__f")).collect();
                plan.matches.push((var, Pat::Ctor(self.record_ctor_name(*rec), names.iter().map(|n| (n.clone(), true)).collect())));
                let args = match &ty {
                    Type::Record(_, a) => a.clone(),
                    _ => vec![Type::Unit; n],
                };
                for (i, n) in names.iter().enumerate() {
                    plan.vars.push((n.clone(), args.get(i).cloned().unwrap_or(Type::Unit)));
                }
                for (idx, sub) in fields {
                    let ft = args.get(*idx).cloned().unwrap_or(Type::Unit);
                    self.plan_pattern(ctx, sub, names[*idx].clone(), &ft, plan);
                }
            }
        }
    }

    // -- iterators -----------------------------------------------------------

    /// How to iterate one `for` iterable.
    pub fn plan_iterator(&mut self, ctx: &mut FnCtx, it: &TExpr) -> IterPlan {
        let t = self.rty(ctx, &it.ty);
        let line = it.line;
        match t {
            Type::List(e) => {
                let elem_ty = self.ty(&e, &[], line);
                let init = self.lower_expr(ctx, it);
                let sv = self.fresh("__rest");
                IterPlan { kind: IterKind::List { elem_ty: elem_ty.clone(), elem_tt: (*e).clone() }, state_var: sv, state_ty: Ty::list(elem_ty), state_tt: Type::list((*e).clone()), init }
            }
            Type::Map(v) => {
                let entries = TExpr { kind: TExprKind::MethodCall { recv: Box::new(it.clone()), name: "entries".into(), args: vec![] }, ty: Type::list(Type::Record(crate::sigs::PAIR_REC, vec![Type::Str, (*v).clone()])), line };
                self.plan_iterator(ctx, &entries)
            }
            Type::Str => {
                let chars = TExpr { kind: TExprKind::MethodCall { recv: Box::new(it.clone()), name: "chars".into(), args: vec![] }, ty: Type::list(Type::Str), line };
                self.plan_iterator(ctx, &chars)
            }
            Type::Range => {
                // a range value or literal: start and end as locals
                let (start, end) = match &it.kind {
                    TExprKind::Range { start, end: Some(end) } => {
                        let s = self.lower_expr(ctx, start);
                        let e = self.lower_expr(ctx, end);
                        (s, e)
                    }
                    _ => {
                        let r = self.lower_expr(ctx, it);
                        let r = self.temp(ctx, r, Ty::Named("F.Range".into(), vec![]), false);
                        (Term::Call("F.range.start".into(), vec![r.clone()]), Term::Call("F.range.end".into(), vec![r]))
                    }
                };
                let end_var = self.fresh("__end");
                self.bind_local(ctx, &end_var, end, Ty::U32, Type::Int);
                let sv = self.fresh("__i");
                IterPlan { kind: IterKind::Range { end_var }, state_var: sv, state_ty: Ty::U32, state_tt: Type::Int, init: start }
            }
            Type::Stream(e) => {
                // an open range with pending stages
                let (start, stages) = self.stream_plan(ctx, it);
                let sv = self.fresh("__n");
                IterPlan { kind: IterKind::Stream { stages, elem_tt: (*e).clone() }, state_var: sv, state_ty: Ty::U32, state_tt: Type::Int, init: start }
            }
            other => {
                self.error(line, format!("cannot iterate over {:?}", other));
                IterPlan { kind: IterKind::Range { end_var: "x".into() }, state_var: "x".into(), state_ty: Ty::U32, state_tt: Type::Int, init: Term::U32(0) }
            }
        }
    }

    /// Unwind a stream expression into its source start and its stages.
    pub fn stream_plan(&mut self, ctx: &mut FnCtx, e: &TExpr) -> (Term, Vec<(StageOp, TExpr)>) {
        let (start, stages, skip) = self.stream_parts(ctx, e);
        if skip.is_some() {
            self.error(e.line, "internal: a stream skip reached an iterator; use take/first");
        }
        let s = self.lower_expr(ctx, &start);
        (s, stages)
    }

    /// A stream as (start expression, stages, items to skip after the
    /// stages), resolving names bound to streams. A `.drop(n)` / `[n..]`
    /// before any stage moves the start; after a stage it becomes a skip.
    pub fn stream_parts(&mut self, ctx: &mut FnCtx, e: &TExpr) -> (TExpr, Vec<(StageOp, TExpr)>, Option<TExpr>) {
        let line = e.line;
        match &e.kind {
            TExprKind::Range { start, end: None } => ((**start).clone(), vec![], None),
            TExprKind::Stage { op, input, func } => {
                let (start, mut stages, skip) = self.stream_parts(ctx, input);
                if skip.is_some() {
                    self.error(line, "a stage after .drop() on a filtered stream is not supported");
                }
                stages.push((*op, (**func).clone()));
                (start, stages, skip)
            }
            TExprKind::Local(n) => {
                if let Some(src) = ctx.stream_aliases.get(n).cloned() {
                    return self.stream_parts(ctx, &src);
                }
                self.error(line, format!("{} holds a lazy stream that was not built in this function; build the pipeline in the same scope", n));
                (TExpr { kind: TExprKind::Lit(Lit::Int(0)), ty: Type::Int, line }, vec![], None)
            }
            TExprKind::Builtin(b, args) if b == "slice" => {
                let a = match &args[1].kind {
                    TExprKind::Range { start, .. } => (**start).clone(),
                    _ => TExpr { kind: TExprKind::Lit(Lit::Int(0)), ty: Type::Int, line },
                };
                let dropped = TExpr { kind: TExprKind::MethodCall { recv: Box::new(args[0].clone()), name: "drop".into(), args: vec![a] }, ty: e.ty.clone(), line };
                self.stream_parts(ctx, &dropped)
            }
            TExprKind::MethodCall { recv, name, args } if name == "drop" => {
                let (start, stages, skip) = self.stream_parts(ctx, recv);
                let n = args[0].clone();
                let add = |a: TExpr, b: TExpr| TExpr { kind: TExprKind::BinOp(BinOp::Add, Box::new(a), Box::new(b)), ty: Type::Int, line };
                if stages.is_empty() {
                    (add(start, n), stages, skip)
                } else {
                    let skip2 = match skip {
                        Some(k) => add(k, n),
                        None => n,
                    };
                    (start, stages, Some(skip2))
                }
            }
            _ => {
                self.error(line, "unsupported stream expression");
                (TExpr { kind: TExprKind::Lit(Lit::Int(0)), ty: Type::Int, line }, vec![], None)
            }
        }
    }

    /// The first `n` items of a stream (after skipping the items a `.drop`
    /// on a filtered stream asked for), as a list, via a loop with a
    /// counter and an accumulator.
    pub fn stream_take(&mut self, ctx: &mut FnCtx, stream: &TExpr, n: &TExpr, elem_tt: &Type, line: usize) -> Term {
        let acc = self.fresh("__acc");
        let cnt = self.fresh("__cnt");
        let x = self.fresh("__x");
        let list_tt = Type::list(elem_tt.clone());
        let local = |n: &str, t: Type| TExpr { kind: TExprKind::Local(n.to_string()), ty: t, line };
        let int = |v: i64| TExpr { kind: TExprKind::Lit(Lit::Int(v)), ty: Type::Int, line };
        let (start, stages, skip) = self.stream_parts(ctx, stream);
        // the source stream rebuilt without the skip
        let mut source = TExpr { kind: TExprKind::Range { start: Box::new(start), end: None }, ty: Type::stream(Type::Int), line };
        for (op, f) in stages {
            let out_ty = match self.store.resolve(&f.ty) {
                Type::Fn(_, r, _) if op == StageOp::Map => Type::stream((*r).clone()),
                _ => source.ty.clone(),
            };
            source = TExpr { kind: TExprKind::Stage { op, input: Box::new(source), func: Box::new(f) }, ty: out_ty, line };
        }
        let skip_expr = skip.unwrap_or_else(|| int(0));
        let keep = TExpr { kind: TExprKind::BinOp(BinOp::Ge, Box::new(local(&cnt, Type::Int)), Box::new(local("__skip", Type::Int))), ty: Type::Bool, line };
        let push = TStmt { kind: TStmtKind::Assign { name: acc.clone(), value: TExpr { kind: TExprKind::Builtin("cons".into(), vec![local(&x, elem_tt.clone()), local(&acc, list_tt.clone())]), ty: list_tt.clone(), line } }, line };
        let body = TBlock {
            stmts: vec![
                TStmt { kind: TStmtKind::If { cond: TExpr { kind: TExprKind::BinOp(BinOp::Ge, Box::new(local(&cnt, Type::Int)), Box::new(TExpr { kind: TExprKind::BinOp(BinOp::Add, Box::new(local("__n", Type::Int)), Box::new(local("__skip", Type::Int))), ty: Type::Int, line })), ty: Type::Bool, line }, then: TBlock { stmts: vec![TStmt { kind: TStmtKind::Break, line }] }, elifs: vec![], else_: None }, line },
                TStmt { kind: TStmtKind::If { cond: keep, then: TBlock { stmts: vec![push] }, elifs: vec![], else_: None }, line },
                TStmt { kind: TStmtKind::Assign { name: cnt.clone(), value: TExpr { kind: TExprKind::BinOp(BinOp::Add, Box::new(local(&cnt, Type::Int)), Box::new(int(1))), ty: Type::Int, line } }, line },
            ],
        };
        let block = TBlock {
            stmts: vec![
                TStmt { kind: TStmtKind::Let { name: "__n".into(), mutable: false, value: n.clone() }, line },
                TStmt { kind: TStmtKind::Let { name: "__skip".into(), mutable: false, value: skip_expr }, line },
                TStmt { kind: TStmtKind::Let { name: acc.clone(), mutable: true, value: TExpr { kind: TExprKind::List(vec![]), ty: list_tt.clone(), line } }, line },
                TStmt { kind: TStmtKind::Let { name: cnt.clone(), mutable: true, value: int(0) }, line },
                TStmt { kind: TStmtKind::For { pattern: TPattern::Bind(x.clone()), iterables: vec![source.clone()], body }, line },
                TStmt { kind: TStmtKind::Expr(TExpr { kind: TExprKind::Builtin("list_reverse".into(), vec![local(&acc, list_tt.clone())]), ty: list_tt.clone(), line }), line },
            ],
        };
        let mut names = HashSet::new();
        for s in &block.stmts {
            free_stmt(s, &mut names);
        }
        // the stream's own free variables (its stages' captures)
        self.free_with_captures(&source, &mut names);
        let mut live: Vec<String> = names.into_iter().filter(|nm| ctx.locals.contains_key(nm) && !ctx.stream_aliases.contains_key(nm)).collect();
        live.sort();
        let name = self.fresh(&format!("{}.take", ctx.base));
        let mut cctx = self.sub_ctx(ctx, &live);
        let list_bt = self.ty(&list_tt, &[], line);
        cctx.result = list_bt.clone();
        cctx.fn_result = list_bt.clone();
        cctx.base = name.clone();
        cctx.method = None;
        cctx.ctor = None;
        cctx.loops.clear();
        let cbody = self.lower_block(&mut cctx, &block.stmts, Cont::Ret);
        self.emit_helper(&cctx, name.clone(), &live, vec![], list_bt.clone(), cbody);
        let call = self.call_helper(&name, &live, vec![]);
        self.adapt_call(ctx, call, ctx.mode, list_bt, line)
    }

    /// Statements that start an iteration: bind the pattern from the
    /// cursors, advance them, and apply stream stages.
    pub fn iterator_prologue(&mut self, ctx: &mut FnCtx, iters: &[IterPlan], pattern: &TPattern, line: usize) -> Vec<TStmt> {
        let mut out = Vec::new();
        let mut items: Vec<TExpr> = Vec::new();
        for p in iters {
            match &p.kind {
                IterKind::List { elem_tt, .. } => {
                    // the driver's body def matches the cursor: expose head/tail
                    // via builtins the body lowering knows
                    let cur = TExpr { kind: TExprKind::Local(p.state_var.clone()), ty: p.state_tt.clone(), line };
                    let head = TExpr { kind: TExprKind::Builtin("__iter_head".into(), vec![cur.clone()]), ty: elem_tt.clone(), line };
                    let tail = TExpr { kind: TExprKind::Builtin("__iter_tail".into(), vec![cur.clone()]), ty: p.state_tt.clone(), line };
                    let done = TExpr { kind: TExprKind::Builtin("__iter_done".into(), vec![cur]), ty: Type::Bool, line };
                    out.push(TStmt { kind: TStmtKind::If { cond: done, then: TBlock { stmts: vec![TStmt { kind: TStmtKind::Break, line }] }, elifs: vec![], else_: None }, line });
                    let item = self.fresh("__it");
                    out.push(TStmt { kind: TStmtKind::Let { name: item.clone(), mutable: false, value: head }, line });
                    out.push(TStmt { kind: TStmtKind::Assign { name: p.state_var.clone(), value: tail }, line });
                    items.push(TExpr { kind: TExprKind::Local(item), ty: elem_tt.clone(), line });
                }
                IterKind::Range { end_var } => {
                    let cur = TExpr { kind: TExprKind::Local(p.state_var.clone()), ty: Type::Int, line };
                    let end = TExpr { kind: TExprKind::Local(end_var.clone()), ty: Type::Int, line };
                    let done = TExpr { kind: TExprKind::BinOp(BinOp::Ge, Box::new(cur.clone()), Box::new(end)), ty: Type::Bool, line };
                    out.push(TStmt { kind: TStmtKind::If { cond: done, then: TBlock { stmts: vec![TStmt { kind: TStmtKind::Break, line }] }, elifs: vec![], else_: None }, line });
                    let item = self.fresh("__it");
                    out.push(TStmt { kind: TStmtKind::Let { name: item.clone(), mutable: false, value: cur.clone() }, line });
                    let next = TExpr { kind: TExprKind::BinOp(BinOp::Add, Box::new(cur), Box::new(TExpr { kind: TExprKind::Lit(Lit::Int(1)), ty: Type::Int, line })), ty: Type::Int, line };
                    out.push(TStmt { kind: TStmtKind::Assign { name: p.state_var.clone(), value: next }, line });
                    items.push(TExpr { kind: TExprKind::Local(item), ty: Type::Int, line });
                }
                IterKind::Stream { stages, elem_tt } => {
                    let cur = TExpr { kind: TExprKind::Local(p.state_var.clone()), ty: Type::Int, line };
                    let item = self.fresh("__it");
                    out.push(TStmt { kind: TStmtKind::Let { name: item.clone(), mutable: true, value: cur.clone() }, line });
                    let next = TExpr { kind: TExprKind::BinOp(BinOp::Add, Box::new(cur), Box::new(TExpr { kind: TExprKind::Lit(Lit::Int(1)), ty: Type::Int, line })), ty: Type::Int, line };
                    out.push(TStmt { kind: TStmtKind::Assign { name: p.state_var.clone(), value: next }, line });
                    let mut cur_ty = Type::Int;
                    for (op, f) in stages {
                        let call = TExpr { kind: TExprKind::CallValue(Box::new(f.clone()), vec![TExpr { kind: TExprKind::Local(item.clone()), ty: cur_ty.clone(), line }]), ty: Type::Bool, line };
                        match op {
                            StageOp::Filter => {
                                let keep = TExpr { kind: TExprKind::Not(Box::new(call)), ty: Type::Bool, line };
                                out.push(TStmt { kind: TStmtKind::If { cond: keep, then: TBlock { stmts: vec![TStmt { kind: TStmtKind::Continue, line }] }, elifs: vec![], else_: None }, line });
                            }
                            StageOp::Map => {
                                let out_ty = match self.store.resolve(&f.ty) {
                                    Type::Fn(_, r, _) => (*r).clone(),
                                    _ => Type::Int,
                                };
                                let mapped = TExpr { kind: TExprKind::CallValue(Box::new(f.clone()), vec![TExpr { kind: TExprKind::Local(item.clone()), ty: cur_ty.clone(), line }]), ty: out_ty.clone(), line };
                                let item2 = self.fresh("__it");
                                out.push(TStmt { kind: TStmtKind::Let { name: item2.clone(), mutable: false, value: mapped }, line });
                                cur_ty = out_ty;
                                let _ = &item;
                                items.push(TExpr { kind: TExprKind::Local(item2), ty: cur_ty.clone(), line });
                                continue;
                            }
                        }
                    }
                    if items.len() < out.len() && !stages.iter().any(|(op, _)| *op == StageOp::Map) {
                        items.push(TExpr { kind: TExprKind::Local(item), ty: elem_tt.clone(), line });
                    } else if stages.iter().all(|(op, _)| *op == StageOp::Filter) {
                        items.push(TExpr { kind: TExprKind::Local(item), ty: elem_tt.clone(), line });
                    }
                }
            }
        }
        // bind the pattern to the row with irrefutable lets
        let row = if items.len() == 1 {
            items.pop().unwrap()
        } else {
            // nested pairs, as the inference typed them
            let mut it = items.into_iter().rev();
            let mut acc = it.next().unwrap();
            for x in it {
                let ty = Type::Record(crate::sigs::PAIR_REC, vec![x.ty.clone(), acc.ty.clone()]);
                acc = TExpr { kind: TExprKind::MakeRecord(crate::sigs::PAIR_REC, vec![x, acc]), ty, line };
            }
            acc
        };
        self.bind_irrefutable(ctx, pattern, row, line, &mut out);
        out
    }
}

impl<'a> Lower<'a> {
    /// Bind a loop/comprehension pattern with lets (list patterns index
    /// the row, which may abort on a shape mismatch, as in Fire).
    pub fn bind_irrefutable(&mut self, ctx: &mut FnCtx, pattern: &TPattern, row: TExpr, line: usize, out: &mut Vec<TStmt>) {
        match pattern {
            TPattern::Bind(n) => out.push(TStmt { kind: TStmtKind::Let { name: n.clone(), mutable: false, value: row }, line }),
            TPattern::Wild => {
                let tmp = self.fresh("__w");
                out.push(TStmt { kind: TStmtKind::Let { name: tmp, mutable: false, value: row }, line });
            }
            TPattern::Record(rec, fields) => {
                let tmp = self.fresh("__r");
                let rt = row.ty.clone();
                out.push(TStmt { kind: TStmtKind::Let { name: tmp.clone(), mutable: false, value: row }, line });
                let args = match self.store.resolve(&rt) {
                    Type::Record(_, a) => a,
                    _ => vec![],
                };
                for (idx, sub) in fields {
                    let fty = args.get(*idx).cloned().unwrap_or(Type::Unit);
                    let get = TExpr { kind: TExprKind::Field(Box::new(TExpr { kind: TExprKind::Local(tmp.clone()), ty: rt.clone(), line }), *rec, *idx), ty: fty, line };
                    self.bind_irrefutable(ctx, sub, get, line, out);
                }
            }
            TPattern::List(items, rest) => {
                let tmp = self.fresh("__l");
                let rt = row.ty.clone();
                let elem = match self.store.resolve(&rt) {
                    Type::List(e) => (*e).clone(),
                    _ => Type::Unit,
                };
                out.push(TStmt { kind: TStmtKind::Let { name: tmp.clone(), mutable: false, value: row }, line });
                for (i, sub) in items.iter().enumerate() {
                    let idx = TExpr { kind: TExprKind::Lit(Lit::Int(i as i64)), ty: Type::Int, line };
                    let get = TExpr { kind: TExprKind::Builtin("index".into(), vec![TExpr { kind: TExprKind::Local(tmp.clone()), ty: rt.clone(), line }, idx]), ty: elem.clone(), line };
                    self.bind_irrefutable(ctx, sub, get, line, out);
                }
                if let Some(Some(r)) = rest {
                    let n = TExpr { kind: TExprKind::Lit(Lit::Int(items.len() as i64)), ty: Type::Int, line };
                    let drop = TExpr { kind: TExprKind::MethodCall { recv: Box::new(TExpr { kind: TExprKind::Local(tmp.clone()), ty: rt.clone(), line }), name: "drop".into(), args: vec![n] }, ty: rt.clone(), line };
                    out.push(TStmt { kind: TStmtKind::Let { name: r.clone(), mutable: false, value: drop }, line });
                }
            }
            _ => {
                self.error(line, "a loop pattern must be a name, a list, or an object pattern");
            }
        }
    }
}

/// The plan of one pattern: nested constructor matches (var, pattern),
/// name bindings (name, var, type), and literal tests (var, literal, type).
#[derive(Debug, Default)]
pub struct PatPlan {
    pub matches: Vec<(String, Pat)>,
    pub binds: Vec<(String, String, Type)>,
    pub tests: Vec<(String, Lit, Type)>,
    /// Every constructor-bound variable with its type (they are locals of
    /// the arm, so helpers split off inside it can receive them).
    pub vars: Vec<(String, Type)>,
}
