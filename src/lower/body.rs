// src/bend/lower/body.rs
// Statement lowering: blocks become straight-line segments ending in a
// tail; every branch is a helper def; loops are drivers.

use std::collections::{HashMap, HashSet};

use super::*;

/// Where a block's control goes when it finishes.
#[derive(Debug, Clone)]
pub enum Cont {
    /// The function's result.
    Ret,
    /// Call a join def with these live variables.
    Join { name: String, live: Vec<String> },
    /// End of a loop iteration: `Next{state}`.
    LoopNext,
}

#[derive(Debug, Clone)]
pub struct Local {
    pub ty: Ty,
    /// The typed-AST type, for closure representations.
    pub tt: Type,
}

#[derive(Debug, Clone)]
pub struct LoopCtx {
    pub ctl: String,
    /// State variables (Fire names) threaded through the loop, in order.
    pub state: Vec<String>,
    pub has_return: bool,
}

pub struct FnCtx {
    pub inst: Instance,
    pub mode: Mode,
    pub locals: HashMap<String, Local>,
    /// def -> the local holding its environment value.
    pub env_of: HashMap<DefId, String>,
    pub loops: Vec<LoopCtx>,
    /// For methods: the record, its field names, and whether it mutates.
    pub method: Option<(RecId, Vec<String>, bool)>,
    pub ctor: Option<RecId>,
    pub seg: Vec<Stmt>,
    pub base: String,
    /// The Bend result type of the code being generated (unwrapped).
    pub result: Ty,
    pub line: usize,
    /// Lazy streams bound to names: the expression that builds them.
    pub stream_aliases: HashMap<String, TExpr>,
    /// The function's own result type (what a `return` carries), which
    /// loop bodies keep while their `result` is the control type.
    pub fn_result: Ty,
}

impl<'a> Lower<'a> {
    pub fn lower_def_instance(&mut self, inst: &Instance) {
        let d = &self.tp.defs[inst.def];
        let line = d.line;
        let mut ctx = FnCtx {
            inst: inst.clone(),
            mode: inst.mode,
            locals: HashMap::new(),
            env_of: HashMap::new(),
            loops: Vec::new(),
            method: None,
            ctor: None,
            seg: Vec::new(),
            base: inst.name.clone(),
            result: inst.ret.clone(),
            line,
            stream_aliases: HashMap::new(),
            fn_result: inst.ret.clone(),
        };
        let mut params: Vec<Param> = Vec::new();
        let mut head_matches: Vec<(String, Pat)> = Vec::new();
        // environment
        if let Some(env_ty) = &inst.env {
            if matches!(d.kind, DefKind::Method { .. } | DefKind::Ctor(_)) {
                self.error(line, format!("{} captures variables from outside its class ({}); pass them as constructor parameters instead", d.name, d.captures.iter().map(|c| c.0.as_str()).collect::<Vec<_>>().join(", ")));
            }
            params.push(Param { name: "env".into(), reusable: false, ty: env_ty.clone() });
            let env_name = match env_ty {
                Ty::Named(n, _) => n.clone(),
                _ => unreachable!(),
            };
            let mut fields = Vec::new();
            for (n, t) in &d.captures {
                let bt = self.ty(t, &inst.subst, line);
                let tt = self.store.substitute(t, &inst.subst);
                ctx.locals.insert(n.clone(), Local { ty: bt, tt: tt.clone() });
                fields.push((Self::mangle(n), false));
                // a captured function value: remember its env for direct calls
                if let Type::Fn(_, _, c) = self.store.resolve(&tt) {
                    let set = self.store.clos_set(c);
                    if set.len() == 1 {
                        let only = *set.iter().next().unwrap();
                        ctx.env_of.insert(only, n.clone());
                    }
                }
            }
            head_matches.push(("env".into(), Pat::Ctor(format!("{}.mk", env_name), fields)));
        }
        // self for methods
        let mut ret_ty = inst.ret.clone();
        if let DefKind::Method { rec, mutates } = &d.kind {
            let rec = *rec;
            let self_ty = inst.params[0].clone();
            params.push(Param { name: "self".into(), reusable: false, ty: self_ty.clone() });
            let self_tt = match self.store.substitute(&d.scheme.ty, &inst.subst) {
                Type::Fn(ps, _, _) => ps[0].clone(),
                _ => unreachable!(),
            };
            let self_tt = self.store.resolve(&self_tt);
            let args = match &self_tt {
                Type::Record(_, a) => a.clone(),
                _ => vec![],
            };
            let mut fields = Vec::new();
            let mut names = Vec::new();
            for (i, f) in self.tp.records[rec].fields.iter().enumerate() {
                let ft = args.get(i).cloned().unwrap_or(Type::Unit);
                let bt = self.ty(&ft, &[], line);
                ctx.locals.insert(f.name.clone(), Local { ty: bt, tt: ft });
                fields.push((Self::mangle(&f.name), false));
                names.push(f.name.clone());
            }
            head_matches.push(("self".into(), Pat::Ctor(self.record_ctor_name(rec), fields)));
            ctx.method = Some((rec, names, *mutates));
            ctx.locals.insert("self".into(), Local { ty: self_ty.clone(), tt: self_tt });
            if *mutates {
                ret_ty = if inst.ret == Ty::Unit { self_ty } else { Ty::Named("F.Ret".into(), vec![self_ty, inst.ret.clone()]) };
            }
        }
        if let DefKind::Ctor(rec) = &d.kind {
            ctx.ctor = Some(*rec);
        }
        ctx.result = ret_ty.clone();
        ctx.fn_result = ret_ty.clone();
        // parameters
        let param_offset = if matches!(d.kind, DefKind::Method { .. }) { 1 } else { 0 };
        for (i, p) in d.params.iter().enumerate() {
            let bt = inst.params[i + param_offset].clone();
            let tt = self.store.substitute(&p.ty, &inst.subst);
            ctx.locals.insert(p.name.clone(), Local { ty: bt.clone(), tt });
            params.push(Param { name: Self::mangle(&p.name), reusable: false, ty: bt });
        }
        // body
        let body = self.lower_block(&mut ctx, &d.body.stmts, Cont::Ret);
        let body = wrap_head_matches(head_matches, body);
        let mut def = Def {
            name: inst.name.clone(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params,
            ret: inst.mode.wrap(ret_ty),
            body,
        };
        self.finish_def(&mut def);
        self.emitted_defs.insert(def.name.clone());
        self.defs.push(def);
    }

    /// Quantity fix-up and do-block splitting, then emit.
    pub fn finish_def(&mut self, def: &mut Def) {
        self.split_do_blocks(def);
        self.fix_quantities(def);
        // Bend's termination checker only accepts structural recursion;
        // user recursion is marked unsafe (proofs are not this backend's goal)
        let mut refs = std::collections::BTreeSet::new();
        def.body.def_refs(&mut refs);
        if refs.contains(&def.name) {
            def.is_unsafe = true;
        }
    }

    // -- helpers -------------------------------------------------------------

    /// Emit a helper def continuing the current function: same mode, the
    /// given live variables as parameters (plus extras), and result type.
    pub fn emit_helper(&mut self, ctx: &FnCtx, name: String, live: &[String], extra: Vec<Param>, ret: Ty, body: Body) -> String {
        let mut params: Vec<Param> = Vec::new();
        for n in live {
            let l = &ctx.locals[n];
            params.push(Param { name: Self::mangle(n), reusable: false, ty: l.ty.clone() });
        }
        params.extend(extra);
        let mut def = Def { name: name.clone(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params, ret: ctx.mode.wrap(ret), body };
        self.finish_def(&mut def);
        self.emitted_defs.insert(name.clone());
        self.defs.push(def);
        name
    }

    pub fn call_helper(&self, name: &str, live: &[String], extra: Vec<Term>) -> Term {
        let mut args: Vec<Term> = live.iter().map(|n| Term::Var(Self::mangle(n))).collect();
        args.extend(extra);
        Term::Call(name.to_string(), args)
    }

    /// Free Fire locals referenced by statements, restricted to the
    /// variables defined in the context.
    pub fn live_in(&self, ctx: &FnCtx, stmts: &[TStmt], k: &Cont) -> Vec<String> {
        let mut names = HashSet::new();
        for s in stmts {
            free_stmt(s, &mut names);
        }
        for n in self.cont_live(ctx, k) {
            names.insert(n);
        }
        let mut out: Vec<String> = names.into_iter().filter(|n| ctx.locals.contains_key(n)).collect();
        out.sort();
        out
    }

    pub fn live_in_exprs(&self, ctx: &FnCtx, exprs: &[&TExpr], k: &Cont) -> Vec<String> {
        let mut names = HashSet::new();
        for e in exprs {
            free_expr(e, &mut names);
        }
        for n in self.cont_live(ctx, k) {
            names.insert(n);
        }
        let mut out: Vec<String> = names.into_iter().filter(|n| ctx.locals.contains_key(n)).collect();
        out.sort();
        out
    }

    pub fn cont_live(&self, ctx: &FnCtx, k: &Cont) -> Vec<String> {
        match k {
            Cont::Ret => self.ret_live(ctx),
            Cont::Join { live, .. } => live.clone(),
            Cont::LoopNext => ctx.loops.last().map(|l| l.state.clone()).unwrap_or_default(),
        }
    }

    /// Variables the function's return needs: member locals of a mutating
    /// method or a constructor.
    pub fn ret_live(&self, ctx: &FnCtx) -> Vec<String> {
        if let Some((_, names, true)) = &ctx.method {
            return names.clone();
        }
        if let Some(rec) = ctx.ctor {
            return self.tp.records[rec].fields.iter().map(|f| f.name.clone()).collect();
        }
        // a `return` inside a loop body carries through the loop's Return
        vec![]
    }

    // -- blocks --------------------------------------------------------------

    /// Lower statements into a body for the current def/helper.
    pub fn lower_block(&mut self, ctx: &mut FnCtx, stmts: &[TStmt], k: Cont) -> Body {
        let saved_seg = std::mem::take(&mut ctx.seg);
        let saved_locals = ctx.locals.clone();
        let tail = self.lower_stmts(ctx, stmts, k);
        let seg = std::mem::replace(&mut ctx.seg, saved_seg);
        ctx.locals = saved_locals;
        self.make_body(ctx, seg, tail)
    }

    pub fn make_body(&self, ctx: &FnCtx, seg: Vec<Stmt>, tail: Tail) -> Body {
        match ctx.mode {
            Mode::Pure => Body::Block { stmts: seg, tail: tail.term },
            m => {
                let monad = m.wrap(ctx.result.clone());
                let t = if tail.monadic { DoTail::Step(tail.term) } else { DoTail::Return(tail.term) };
                Body::Do { monad, stmts: seg, tail: t }
            }
        }
    }

    pub fn lower_stmts_pub(&mut self, ctx: &mut FnCtx, stmts: &[TStmt], k: Cont) -> Tail {
        self.lower_stmts(ctx, stmts, k)
    }

    /// Lower a statement list; returns the tail. Pushes lets/binds into
    /// `ctx.seg`.
    fn lower_stmts(&mut self, ctx: &mut FnCtx, stmts: &[TStmt], k: Cont) -> Tail {
        for (i, s) in stmts.iter().enumerate() {
            ctx.line = s.line;
            match &s.kind {
                // `x = match ...` / `x = if ...` whose branches assign or mutate:
                // lowered as a statement whose branches each bind `x`, so the
                // side effects flow on (an expression helper would lose them)
                TStmtKind::Let { name, value, .. } | TStmtKind::Assign { name, value }
                    if matches!(value.kind, TExprKind::Match { .. } | TExprKind::If { .. }) && self.expr_has_mutation(ctx, value) =>
                {
                    let is_new = !ctx.locals.contains_key(name);
                    let bt = self.ty(&value.ty, &ctx.inst.subst.clone(), s.line);
                    let tt = self.store.substitute(&value.ty, &ctx.inst.subst);
                    ctx.locals.insert(name.clone(), Local { ty: bt, tt });
                    let assign = |v: &TExpr| TBlock { stmts: vec![TStmt { kind: TStmtKind::Assign { name: name.clone(), value: v.clone() }, line: s.line }] };
                    let synthetic = match &value.kind {
                        TExprKind::Match { subject, arms } => {
                            let arms: Vec<TArm> = arms
                                .iter()
                                .map(|a| TArm { pattern: a.pattern.clone(), guard: a.guard.clone(), body: TExpr { kind: TExprKind::Block(assign(&a.body)), ty: Type::Unit, line: a.line }, line: a.line })
                                .collect();
                            TStmt { kind: TStmtKind::Match { subject: (**subject).clone(), arms }, line: s.line }
                        }
                        TExprKind::If { cond, then, else_ } => TStmt { kind: TStmtKind::If { cond: (**cond).clone(), then: assign(then), elifs: vec![], else_: Some(assign(else_)) }, line: s.line },
                        _ => unreachable!(),
                    };
                    let rest = &stmts[i + 1..];
                    let k2 = if rest.is_empty() {
                        k.clone()
                    } else {
                        let live = self.live_in(ctx, rest, &k);
                        let jname = self.fresh(&format!("{}.j", ctx.base));
                        let mut jctx = self.sub_ctx(ctx, &live);
                        let body = self.lower_block(&mut jctx, rest, k.clone());
                        let result = ctx.result.clone();
                        self.emit_helper(ctx, jname.clone(), &live, vec![], result, body);
                        Cont::Join { name: jname, live }
                    };
                    // the branches define the name; the join receives it from them
                    if is_new {
                        ctx.locals.remove(name);
                    }
                    return self.lower_branching(ctx, &synthetic, k2);
                }
                TStmtKind::Let { name, value, .. } => {
                    if let Type::Stream(_) = self.rty(ctx, &value.ty) {
                        // a lazy stream: remembered, consumed where used
                        ctx.stream_aliases.insert(name.clone(), value.clone());
                        ctx.locals.insert(name.clone(), Local { ty: Ty::Unit, tt: self.rty(ctx, &value.ty) });
                        continue;
                    }
                    let t = self.lower_expr(ctx, value);
                    let bt = self.ty(&value.ty, &ctx.inst.subst.clone(), s.line);
                    let tt = self.store.substitute(&value.ty, &ctx.inst.subst);
                    self.bind_local(ctx, name, t, bt, tt);
                }
                TStmtKind::Assign { name, value } => {
                    let t = self.lower_expr(ctx, value);
                    let l = ctx.locals.get(name).cloned();
                    match l {
                        Some(l) => self.bind_local(ctx, name, t, l.ty, l.tt),
                        None => {
                            let bt = self.ty(&value.ty, &ctx.inst.subst.clone(), s.line);
                            let tt = self.store.substitute(&value.ty, &ctx.inst.subst);
                            self.bind_local(ctx, name, t, bt, tt);
                        }
                    }
                }
                TStmtKind::Bind { name, def } => {
                    // the closure value of a nested def, captured here
                    let d = &self.tp.defs[*def];
                    let scheme_ty = d.scheme.ty.clone();
                    let fn_ty = self.store.instantiate(&Scheme { vars: d.scheme.vars.clone(), ty: scheme_ty }).0;
                    let fn_ty = self.store.substitute(&fn_ty, &ctx.inst.subst);
                    let (term, bt) = self.closure_value(ctx, *def, &fn_ty, s.line);
                    ctx.env_of.insert(*def, name.clone());
                    self.bind_local(ctx, name, term, bt, fn_ty);
                }
                TStmtKind::Expr(e) => {
                    let is_last = i + 1 == stmts.len();
                    if is_last && matches!(k, Cont::Ret) && !matches!(ctx.ctor, Some(_)) {
                        // the block's value
                        let t = self.lower_expr(ctx, e);
                        return self.apply_cont(ctx, &k, Some((t, e)));
                    }
                    let t = self.lower_expr(ctx, e);
                    self.discard(ctx, t, e);
                }
                TStmtKind::Return(v) => {
                    let val = match v {
                        Some(e) => {
                            let t = self.lower_expr(ctx, e);
                            Some((t, e))
                        }
                        None => None,
                    };
                    return self.do_return(ctx, val);
                }
                TStmtKind::Break => {
                    let lp = ctx.loops.last().cloned().expect("break inside loop");
                    let state: Vec<Term> = lp.state.iter().map(|n| Term::Var(Self::mangle(n))).collect();
                    return Tail::pure(Term::Ctor(format!("{}.Break", lp.ctl), state));
                }
                TStmtKind::Continue => {
                    let lp = ctx.loops.last().cloned().expect("continue inside loop");
                    let state: Vec<Term> = lp.state.iter().map(|n| Term::Var(Self::mangle(n))).collect();
                    return Tail::pure(Term::Ctor(format!("{}.Next", lp.ctl), state));
                }
                TStmtKind::If { .. } | TStmtKind::Match { .. } | TStmtKind::While { .. } | TStmtKind::For { .. } => {
                    let rest = &stmts[i + 1..];
                    let k2 = if rest.is_empty() {
                        k.clone()
                    } else {
                        // a join def for the rest of the block
                        let live = self.live_in(ctx, rest, &k);
                        let name = self.fresh(&format!("{}.j", ctx.base));
                        let mut jctx = self.sub_ctx(ctx, &live);
                        let body = self.lower_block(&mut jctx, rest, k.clone());
                        let result = ctx.result.clone();
                        self.emit_helper(ctx, name.clone(), &live, vec![], result, body);
                        Cont::Join { name, live }
                    };
                    return self.lower_branching(ctx, s, k2);
                }
            }
        }
        self.apply_cont(ctx, &k, None)
    }

    /// Does the expression assign a local or call a mutating method?
    pub fn expr_has_mutation(&self, ctx: &FnCtx, e: &TExpr) -> bool {
        let mut assigned = HashSet::new();
        assigned_in_expr(e, &mut assigned);
        if !assigned.is_empty() {
            return true;
        }
        let _ = ctx;
        let mut found = false;
        {
            let records = &self.tp.records;
            let defs = &self.tp.defs;
            let store = &self.store;
            let mut check = |x: &TExpr| {
                if found {
                    return;
                }
                if let TExprKind::MethodCall { recv, name, .. } = &x.kind {
                    if let Type::Record(r, _) = store.resolve(&recv.ty) {
                        if let Some(d) = crate::infer::find_method_static(records, store, r, name) {
                            if matches!(defs[d].kind, DefKind::Method { mutates: true, .. }) {
                                found = true;
                            }
                        }
                    }
                }
            };
            crate::tast::walk_expr(e, &mut check);
        }
        found
    }

    /// A child context for a helper def: the same function, only the live
    /// locals visible.
    pub fn sub_ctx(&self, ctx: &FnCtx, live: &[String]) -> FnCtx {
        let mut locals = HashMap::new();
        for n in live {
            locals.insert(n.clone(), ctx.locals[n].clone());
        }
        // member locals of a mutating method / ctor stay visible
        for n in self.ret_live(ctx) {
            if let Some(l) = ctx.locals.get(&n) {
                locals.insert(n.clone(), l.clone());
            }
        }
        FnCtx {
            inst: ctx.inst.clone(),
            mode: ctx.mode,
            locals,
            env_of: ctx.env_of.clone(),
            loops: ctx.loops.clone(),
            method: ctx.method.clone(),
            ctor: ctx.ctor,
            seg: Vec::new(),
            base: ctx.base.clone(),
            result: ctx.result.clone(),
            line: ctx.line,
            stream_aliases: ctx.stream_aliases.clone(),
            fn_result: ctx.fn_result.clone(),
        }
    }

    pub fn bind_local(&mut self, ctx: &mut FnCtx, name: &str, value: Term, bt: Ty, tt: Type) {
        let bname = Self::mangle(name);
        match ctx.mode {
            Mode::Pure => {
                let value = annotate_if_needed(value, &bt);
                ctx.seg.push(Stmt::Let { name: bname, reusable: false, ty: None, value })
            }
            _ => ctx.seg.push(Stmt::Let { name: bname, reusable: false, ty: Some(bt.clone()), value }),
        }
        ctx.locals.insert(name.to_string(), Local { ty: bt, tt });
    }

    /// An expression statement whose value is dropped.
    fn discard(&mut self, ctx: &mut FnCtx, t: Term, e: &TExpr) {
        // a bare variable or literal: nothing to do
        if matches!(t, Term::Var(_) | Term::U32(_) | Term::F32(_) | Term::Str(_) | Term::Nat(_) | Term::Chr(_)) {
            return;
        }
        if let Term::Ctor(_, args) = &t {
            if args.is_empty() {
                return;
            }
        }
        let _ = e;
        let tmp = self.fresh("_u");
        match ctx.mode {
            Mode::Pure => ctx.seg.push(Stmt::Let { name: tmp, reusable: false, ty: None, value: t }),
            _ => {
                let bt = self.ty(&e.ty, &ctx.inst.subst.clone(), ctx.line);
                ctx.seg.push(Stmt::Let { name: tmp, reusable: false, ty: Some(bt), value: t })
            }
        }
    }

    /// `return v` (or falling off the end with a value).
    fn do_return(&mut self, ctx: &mut FnCtx, val: Option<(Term, &TExpr)>) -> Tail {
        if let Some(lp) = ctx.loops.last().cloned() {
            // inside a loop body: the driver propagates it
            let v = match val {
                Some((t, _)) => t,
                None => Term::unit(),
            };
            let _ = lp;
            let ctl = ctx.loops.last().unwrap().ctl.clone();
            return Tail::pure(Term::Ctor(format!("{}.Return", ctl), vec![v]));
        }
        self.apply_cont(ctx, &Cont::Ret, val)
    }

    /// The tail for a finished block.
    pub fn apply_cont(&mut self, ctx: &mut FnCtx, k: &Cont, val: Option<(Term, &TExpr)>) -> Tail {
        match k {
            Cont::Ret => {
                let v = val.map(|(t, _)| t);
                self.function_result(ctx, v)
            }
            Cont::Join { name, live } => Tail::call(self.call_helper(name, live, vec![]), ctx.mode),
            Cont::LoopNext => {
                let lp = ctx.loops.last().cloned().expect("loop");
                let state: Vec<Term> = lp.state.iter().map(|n| Term::Var(Self::mangle(n))).collect();
                Tail::pure(Term::Ctor(format!("{}.Next", lp.ctl), state))
            }
        }
    }

    /// The value a function hands back: its result, the rebuilt self of a
    /// mutating method, or the constructed record.
    pub fn function_result(&mut self, ctx: &mut FnCtx, v: Option<Term>) -> Tail {
        if matches!(self.tp.defs[ctx.inst.def].kind, DefKind::Main) && ctx.loops.is_empty() && ctx.result == Ty::Unit {
            if let Some(t) = v {
                if !matches!(t, Term::Var(_) | Term::U32(_) | Term::Str(_) | Term::Ctor(_, _)) {
                    self.temp(ctx, t, Ty::Unit, false);
                }
            }
            return Tail::pure(Term::unit());
        }
        if let Some(rec) = ctx.ctor {
            let fields: Vec<Term> = self.tp.records[rec].fields.iter().map(|f| Term::Var(Self::mangle(&f.name))).collect();
            return Tail::pure(Term::Ctor(self.record_ctor_name(rec), fields));
        }
        if let Some((rec, names, true)) = ctx.method.clone() {
            let fields: Vec<Term> = names.iter().map(|n| Term::Var(Self::mangle(n))).collect();
            let new_self = Term::Ctor(self.record_ctor_name(rec), fields);
            return match v {
                Some(t) if ctx.inst.ret != Ty::Unit => Tail::pure(Term::ctor("F.Ret.mk", vec![new_self, t])),
                _ => Tail::pure(new_self),
            };
        }
        Tail::pure(v.unwrap_or_else(Term::unit))
    }

    // -- branching statements ------------------------------------------------

    fn lower_branching(&mut self, ctx: &mut FnCtx, s: &TStmt, k: Cont) -> Tail {
        match &s.kind {
            TStmtKind::If { cond, then, elifs, else_ } => {
                // elifs nest as an if in the else block
                let else_block: Option<TBlock> = if elifs.is_empty() {
                    else_.clone()
                } else {
                    let (c, b) = elifs[0].clone();
                    Some(TBlock { stmts: vec![TStmt { kind: TStmtKind::If { cond: c, then: b, elifs: elifs[1..].to_vec(), else_: else_.clone() }, line: s.line }] })
                };
                let c = self.lower_cond(ctx, cond);
                let mut all: Vec<&TStmt> = then.stmts.iter().collect();
                if let Some(e) = &else_block {
                    all.extend(e.stmts.iter());
                }
                let owned: Vec<TStmt> = all.into_iter().cloned().collect();
                let live = self.live_in(ctx, &owned, &k);
                let name = self.fresh(&format!("{}.if", ctx.base));
                let mut tctx = self.sub_ctx(ctx, &live);
                let then_body = self.lower_block(&mut tctx, &then.stmts, k.clone());
                let mut ectx = self.sub_ctx(ctx, &live);
                let else_body = match &else_block {
                    Some(e) => self.lower_block(&mut ectx, &e.stmts, k.clone()),
                    None => self.lower_block(&mut ectx, &[], k.clone()),
                };
                let body = Body::Match { scrutinee: "__c".into(), arms: vec![(Pat::Ctor("True".into(), vec![]), then_body), (Pat::Ctor("False".into(), vec![]), else_body)] };
                let result = ctx.result.clone();
                self.emit_helper(ctx, name.clone(), &live, vec![Param { name: "__c".into(), reusable: false, ty: Ty::Bool }], result, body);
                Tail::call(self.call_helper(&name, &live, vec![c]), ctx.mode)
            }
            TStmtKind::Match { subject, arms } => {
                let subj = self.lower_expr(ctx, subject);
                let sty = self.ty(&subject.ty, &ctx.inst.subst.clone(), s.line);
                let stt = self.store.substitute(&subject.ty, &ctx.inst.subst);
                let bodies: Vec<TStmt> = arms.iter().map(|a| TStmt { kind: TStmtKind::Expr(a.body.clone()), line: a.line }).collect();
                let mut live = self.live_in(ctx, &bodies, &k);
                for a in arms {
                    if let Some(g) = &a.guard {
                        for n in self.live_in_exprs(ctx, &[g], &k) {
                            if !live.contains(&n) {
                                live.push(n);
                            }
                        }
                    }
                }
                live.sort();
                let name = self.lower_match_arms(ctx, arms, &live, sty, stt, MatchKind::Stmt(k.clone()), s.line);
                Tail::call(self.call_helper(&name, &live, vec![subj]), ctx.mode)
            }
            TStmtKind::While { cond, body } => {
                // while cond: body  ==  loop { if cond { body } else { break } }
                let synthetic = TBlock { stmts: vec![TStmt { kind: TStmtKind::If { cond: cond.clone(), then: body.clone(), elifs: vec![], else_: Some(TBlock { stmts: vec![TStmt { kind: TStmtKind::Break, line: s.line }] }) }, line: s.line }] };
                self.lower_loop(ctx, &[], &synthetic, k, s.line)
            }
            TStmtKind::For { pattern, iterables, body } => {
                let iters: Vec<IterPlan> = iterables.iter().map(|it| self.plan_iterator(ctx, it)).collect();
                // the item bound by the pattern is the zipped row
                let prologue = self.iterator_prologue(ctx, &iters, pattern, s.line);
                let mut stmts = prologue;
                stmts.extend(body.stmts.iter().cloned());
                let block = TBlock { stmts };
                let iter_state: Vec<(String, Term)> = iters.iter().map(|p| (p.state_var.clone(), p.init.clone())).collect();
                self.lower_loop_with_iters(ctx, &iter_state, &iters, &block, k, s.line)
            }
            _ => unreachable!(),
        }
    }

    // -- loops ---------------------------------------------------------------

    fn lower_loop(&mut self, ctx: &mut FnCtx, iter_state: &[(String, Term)], body: &TBlock, k: Cont, line: usize) -> Tail {
        self.lower_loop_with_iters(ctx, iter_state, &[], body, k, line)
    }

    /// The loop machinery: a control type, a body def, and an `@unsafe`
    /// driver. `iter_state` are extra state variables (iterator cursors)
    /// with their initial values; `iters` describe how each iteration
    /// starts (bound before the body).
    fn lower_loop_with_iters(&mut self, ctx: &mut FnCtx, iter_state: &[(String, Term)], iters: &[IterPlan], body: &TBlock, k: Cont, line: usize) -> Tail {
        // state: assigned locals + iterator cursors
        let mut assigned = HashSet::new();
        assigned_in_block(body, &mut assigned);
        // a mutating method called on a local (or on the receiver's members)
        // rebinds it too
        {
            let member_names: Vec<String> = ctx.method.as_ref().map(|(_, names, _)| names.clone()).unwrap_or_default();
            let mut mutated: Vec<String> = Vec::new();
            {
                let records = &self.tp.records;
                let defs = &self.tp.defs;
                let store = &self.store;
                let mut check = |e: &TExpr| {
                    if let TExprKind::MethodCall { recv, name, .. } = &e.kind {
                        if let Type::Record(r, _) = store.resolve(&recv.ty) {
                            if let Some(d) = crate::infer::find_method_static(records, store, r, name) {
                                if matches!(defs[d].kind, DefKind::Method { mutates: true, .. }) {
                                    match root_local(recv) {
                                        Some(n) => mutated.push(n),
                                        None => mutated.extend(member_names.iter().cloned()),
                                    }
                                }
                            }
                        }
                    }
                };
                crate::tast::walk_block(body, &mut check);
            }
            assigned.extend(mutated);
        }
        let mut state: Vec<String> = assigned.into_iter().filter(|n| ctx.locals.contains_key(n)).collect();
        state.sort();
        for (n, init) in iter_state {
            // register the cursor as a local
            let ty = match iters.iter().find(|p| &p.state_var == n) {
                Some(p) => p.state_ty.clone(),
                None => Ty::U32,
            };
            let tt = match iters.iter().find(|p| &p.state_var == n) {
                Some(p) => p.state_tt.clone(),
                None => Type::Int,
            };
            ctx.locals.insert(n.clone(), Local { ty, tt });
            let _ = init;
            if !state.contains(n) {
                state.push(n.clone());
            }
        }
        let ctl = self.fresh("F.Ctl");
        let has_return = block_has_return(body);
        let ret_payload = ctx.fn_result.clone();
        // free variables of the body (read-only through the loop) + live after
        let live_after = self.cont_live(ctx, &k);
        let mut free_names: HashSet<String> = HashSet::new();
        for s in &body.stmts {
            free_stmt(s, &mut free_names);
        }
        for n in &live_after {
            free_names.insert(n.clone());
        }
        let mut frees: Vec<String> = free_names.into_iter().filter(|n| ctx.locals.contains_key(n) && !state.contains(n)).collect();
        for n in self.ret_live(ctx) {
            if ctx.locals.contains_key(&n) && !state.contains(&n) && !frees.contains(&n) {
                frees.push(n);
            }
        }
        frees.sort();
        // the control type
        let state_fields: Vec<(String, Ty)> = state.iter().map(|n| (Self::mangle(n), ctx.locals[n].ty.clone())).collect();
        let mut ctors = vec![(format!("{}.Next", ctl), state_fields.clone()), (format!("{}.Break", ctl), state_fields.clone())];
        if has_return {
            ctors.push((format!("{}.Return", ctl), vec![("v".into(), ret_payload.clone())]));
        }
        self.types.push(TypeDef { name: ctl.clone(), params: vec![], ctors });
        // body def: frees + state -> Ctl
        let body_name = format!("{}.loop{}.body", ctx.base, ctl.trim_start_matches("F.Ctl"));
        let mut bctx = self.sub_ctx(ctx, &frees);
        for n in &state {
            bctx.locals.insert(n.clone(), ctx.locals[n].clone());
        }
        bctx.loops.push(LoopCtx { ctl: ctl.clone(), state: state.clone(), has_return });
        bctx.result = Ty::Named(ctl.clone(), vec![]);
        bctx.base = body_name.clone();
        let mut bparams: Vec<String> = frees.clone();
        bparams.extend(state.iter().cloned());
        let bbody = self.lower_block(&mut bctx, &body.stmts, Cont::LoopNext);
        let ctl_ty = Ty::Named(ctl.clone(), vec![]);
        self.emit_helper(&bctx, body_name.clone(), &bparams, vec![], ctl_ty.clone(), bbody);
        // driver: frees + c -> result
        let driver = format!("{}.loop{}.drive", ctx.base, ctl.trim_start_matches("F.Ctl"));
        let mut dctx = self.sub_ctx(ctx, &frees);
        for n in &state {
            dctx.locals.insert(n.clone(), ctx.locals[n].clone());
        }
        let state_pat: Vec<(String, bool)> = state.iter().map(|n| (Self::mangle(n), false)).collect();
        // Break: continue with k
        let break_tail = self.apply_cont(&mut dctx, &k, None);
        let seg0 = std::mem::take(&mut dctx.seg);
        let break_body = self.make_body(&dctx, seg0, break_tail);
        // Next: loop again with the body's answer
        let mut next_args: Vec<Term> = frees.iter().map(|n| Term::Var(Self::mangle(n))).collect();
        next_args.extend(state.iter().map(|n| Term::Var(Self::mangle(n))));
        let body_call = Term::Call(body_name.clone(), next_args);
        let mut drive_args: Vec<Term> = frees.iter().map(|n| Term::Var(Self::mangle(n))).collect();
        let next_body = match ctx.mode {
            Mode::Pure => {
                drive_args.push(body_call);
                Body::term(Term::Call(driver.clone(), drive_args))
            }
            m => {
                let monad = m.wrap(ctx.result.clone());
                drive_args.push(Term::var("c2"));
                Body::Do { monad, stmts: vec![Stmt::Bind { name: "c2".into(), ty: ctl_ty.clone(), value: body_call }], tail: DoTail::Step(Term::Call(driver.clone(), drive_args)) }
            }
        };
        let mut arms = vec![(Pat::Ctor(format!("{}.Break", ctl), state_pat.clone()), break_body), (Pat::Ctor(format!("{}.Next", ctl), state_pat), next_body)];
        if has_return {
            let ret_tail = self.do_return(&mut dctx, Some((Term::var("v"), &TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line })));
            let seg1 = std::mem::take(&mut dctx.seg);
            let ret_body = self.make_body(&dctx, seg1, ret_tail);
            arms.push((Pat::Ctor(format!("{}.Return", ctl), vec![("v".into(), false)]), ret_body));
        }
        let mut dparams: Vec<Param> = frees.iter().map(|n| Param { name: Self::mangle(n), reusable: false, ty: ctx.locals[n].ty.clone() }).collect();
        dparams.push(Param { name: "__c".into(), reusable: false, ty: ctl_ty.clone() });
        let mut ddef = Def { name: driver.clone(), is_unsafe: true, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params: dparams, ret: ctx.mode.wrap(ctx.result.clone()), body: Body::Match { scrutinee: "__c".into(), arms } };
        self.finish_def(&mut ddef);
        self.emitted_defs.insert(driver.clone());
        self.defs.push(ddef);
        // enter the loop
        for (n, init) in iter_state {
            let l = ctx.locals[n].clone();
            self.bind_local(ctx, n, init.clone(), l.ty, l.tt);
        }
        let init_state: Vec<Term> = state.iter().map(|n| Term::Var(Self::mangle(n))).collect();
        let mut args: Vec<Term> = frees.iter().map(|n| Term::Var(Self::mangle(n))).collect();
        args.push(Term::Ctor(format!("{}.Next", ctl), init_state));
        Tail::call(Term::Call(driver, args), ctx.mode)
    }
}

/// Bend cannot infer the type of a bare literal, constructor, or list in a
/// pure let; annotate those.
pub fn annotate_if_needed(value: Term, ty: &Ty) -> Term {
    match &value {
        Term::U32(_) | Term::F32(_) | Term::Nat(_) | Term::Str(_) | Term::Ctor(_, _) | Term::List(_) | Term::Cons(_, _) | Term::Chr(_) => Term::Ann(Box::new(value), ty.clone()),
        _ => value,
    }
}

/// A tail position: a term, and whether it is already monadic (a call of a
/// same-mode helper) or a plain value to `return`.
#[derive(Debug, Clone)]
pub struct Tail {
    pub term: Term,
    pub monadic: bool,
}

impl Tail {
    pub fn pure(term: Term) -> Tail {
        Tail { term, monadic: false }
    }
    pub fn call(term: Term, mode: Mode) -> Tail {
        Tail { term, monadic: mode != Mode::Pure }
    }
}

/// Wrap a body in the head matches (env, self) a def starts with.
fn wrap_head_matches(heads: Vec<(String, Pat)>, body: Body) -> Body {
    let mut b = body;
    for (scrutinee, pat) in heads.into_iter().rev() {
        b = Body::Match { scrutinee, arms: vec![(pat, b)] };
    }
    b
}

/// How one iterable of a `for` loop advances.
#[derive(Debug, Clone)]
pub struct IterPlan {
    pub kind: IterKind,
    /// The cursor variable (a Fire-level synthetic name).
    pub state_var: String,
    pub state_ty: Ty,
    pub state_tt: Type,
    pub init: Term,
}

#[derive(Debug, Clone)]
pub enum IterKind {
    /// A list: the cursor is the remaining list.
    List { elem_ty: Ty, elem_tt: Type },
    /// A closed range: the cursor is the next value; `end` is a local.
    Range { end_var: String },
    /// An open range / stream: the cursor counts up; stages apply per item.
    Stream { stages: Vec<(StageOp, TExpr)>, elem_tt: Type },
}

/// Names assigned to in a block (for loop state).
pub fn assigned_in_block(b: &TBlock, out: &mut HashSet<String>) {
    for s in &b.stmts {
        match &s.kind {
            TStmtKind::Assign { name, value } => {
                out.insert(name.clone());
                assigned_in_expr(value, out);
            }
            TStmtKind::Let { value, .. } | TStmtKind::Expr(value) => assigned_in_expr(value, out),
            TStmtKind::If { then, elifs, else_, .. } => {
                assigned_in_block(then, out);
                for (_, b) in elifs {
                    assigned_in_block(b, out);
                }
                if let Some(b) = else_ {
                    assigned_in_block(b, out);
                }
            }
            TStmtKind::While { body, .. } | TStmtKind::For { body, .. } => assigned_in_block(body, out),
            TStmtKind::Match { subject, arms } => {
                assigned_in_expr(subject, out);
                for a in arms {
                    assigned_in_expr(&a.body, out);
                }
            }
            _ => {}
        }
    }
}

/// Assignments inside expression blocks (`do` bodies, if-expressions).
fn assigned_in_expr(e: &TExpr, out: &mut HashSet<String>) {
    match &e.kind {
        TExprKind::Block(b) => assigned_in_block(b, out),
        TExprKind::If { then, else_, .. } => {
            assigned_in_expr(then, out);
            assigned_in_expr(else_, out);
        }
        TExprKind::Match { arms, .. } => {
            for a in arms {
                assigned_in_expr(&a.body, out);
            }
        }
        _ => {}
    }
}

pub fn block_has_return(b: &TBlock) -> bool {
    b.stmts.iter().any(|s| match &s.kind {
        TStmtKind::Return(_) => true,
        TStmtKind::If { then, elifs, else_, .. } => {
            block_has_return(then) || elifs.iter().any(|(_, b)| block_has_return(b)) || else_.as_ref().is_some_and(block_has_return)
        }
        TStmtKind::While { body, .. } | TStmtKind::For { body, .. } => block_has_return(body),
        TStmtKind::Match { arms, .. } => arms.iter().any(|a| expr_has_return(&a.body)),
        TStmtKind::Expr(e) | TStmtKind::Let { value: e, .. } | TStmtKind::Assign { value: e, .. } => expr_has_return(e),
        _ => false,
    })
}

fn expr_has_return(e: &TExpr) -> bool {
    match &e.kind {
        TExprKind::Block(b) => block_has_return(b),
        TExprKind::If { then, else_, .. } => expr_has_return(then) || expr_has_return(else_),
        TExprKind::Match { arms, .. } => arms.iter().any(|a| expr_has_return(&a.body)),
        _ => false,
    }
}

thread_local! {
    /// Field names of every record, for `SelfValue` (which reads all the
    /// member locals of its class); set by `lower_program`.
    pub static RECORD_FIELDS: std::cell::RefCell<Vec<Vec<String>>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Free local names of a statement (over-approximate: shadowing ignored).
pub fn free_stmt(s: &TStmt, out: &mut HashSet<String>) {
    match &s.kind {
        TStmtKind::Let { value, .. } | TStmtKind::Assign { value, .. } | TStmtKind::Expr(value) => free_expr(value, out),
        TStmtKind::Return(Some(v)) => free_expr(v, out),
        TStmtKind::Return(None) | TStmtKind::Break | TStmtKind::Continue => {}
        TStmtKind::Bind { .. } => {}
        TStmtKind::If { cond, then, elifs, else_ } => {
            free_expr(cond, out);
            for s in &then.stmts {
                free_stmt(s, out);
            }
            for (c, b) in elifs {
                free_expr(c, out);
                for s in &b.stmts {
                    free_stmt(s, out);
                }
            }
            if let Some(b) = else_ {
                for s in &b.stmts {
                    free_stmt(s, out);
                }
            }
        }
        TStmtKind::Match { subject, arms } => {
            free_expr(subject, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    free_expr(g, out);
                }
                free_expr(&a.body, out);
            }
        }
        TStmtKind::While { cond, body } => {
            free_expr(cond, out);
            for s in &body.stmts {
                free_stmt(s, out);
            }
        }
        TStmtKind::For { iterables, body, .. } => {
            for i in iterables {
                free_expr(i, out);
            }
            for s in &body.stmts {
                free_stmt(s, out);
            }
        }
    }
}

pub fn free_expr(e: &TExpr, out: &mut HashSet<String>) {
    let mut go = |x: &TExpr| free_expr(x, out);
    match &e.kind {
        TExprKind::Local(n) => {
            out.insert(n.clone());
        }
        TExprKind::Lit(_) | TExprKind::EmptyMap | TExprKind::Lambda(_) | TExprKind::DefRef(_) => {}
        TExprKind::SelfValue(rec) => {
            // the receiver is rebuilt from its member locals
            RECORD_FIELDS.with(|r| {
                if let Some(fields) = r.borrow().get(*rec) {
                    for f in fields {
                        out.insert(f.clone());
                    }
                }
            });
        }
        TExprKind::List(items) | TExprKind::MakeRecord(_, items) => items.iter().for_each(go),
        TExprKind::Field(o, _, _) | TExprKind::Member(o, _) => go(o),
        TExprKind::SetField(o, _, _, v) => {
            go(o);
            go(v);
        }
        TExprKind::Call(_, args) | TExprKind::Builtin(_, args) => args.iter().for_each(go),
        TExprKind::CallValue(f, args) => {
            go(f);
            args.iter().for_each(go);
        }
        TExprKind::MethodCall { recv, args, .. } => {
            go(recv);
            args.iter().for_each(go);
        }
        TExprKind::If { cond, then, else_ } => {
            go(cond);
            go(then);
            go(else_);
        }
        TExprKind::Match { subject, arms } => {
            go(subject);
            for a in arms {
                if let Some(g) = &a.guard {
                    free_expr(g, out);
                }
                free_expr(&a.body, out);
            }
        }
        TExprKind::Block(b) => {
            for s in &b.stmts {
                free_stmt(s, out);
            }
        }
        TExprKind::And(a, b) | TExprKind::Or(a, b) | TExprKind::BinOp(_, a, b) | TExprKind::RangeList(a, b) => {
            go(a);
            go(b);
        }
        TExprKind::Not(a) | TExprKind::Neg(a) | TExprKind::MakeOk(a) | TExprKind::MakeErr(a) | TExprKind::MakeSome(a) | TExprKind::Abort(a) => go(a),
        TExprKind::Pipe { left, func } => {
            go(left);
            go(func);
        }
        TExprKind::Stage { input, func, .. } => {
            go(input);
            go(func);
        }
        TExprKind::Handle { left, handler, .. } => {
            go(left);
            go(handler);
        }
        TExprKind::Range { start, end } => {
            go(start);
            if let Some(e) = end {
                go(e);
            }
        }
        TExprKind::Comprehension { iterables, filter, body, .. } => {
            iterables.iter().for_each(&mut go);
            if let Some(f) = filter {
                go(f);
            }
            go(body);
        }
        TExprKind::FString(parts) => {
            for p in parts {
                if let FPart::Expr(x, _) = p {
                    go(x);
                }
            }
        }
    }
    // captured names of lambdas count as free (they are read where the
    // closure is built)
    if let TExprKind::Lambda(_) = &e.kind {}
}

/// Where a match is used.
#[derive(Debug, Clone)]
pub enum MatchKind {
    /// Statement: arm bodies are expressions whose value is dropped, then
    /// control continues with the continuation.
    Stmt(Cont),
    /// Expression: the helper returns the arm's value.
    Expr(Ty),
}

impl<'a> Lower<'a> {
    /// Free locals plus the captures of lambda sites (which are read where
    /// the closure is created).
    pub fn free_with_captures(&self, e: &TExpr, out: &mut HashSet<String>) {
        free_expr(e, out);
        let mut sites = Vec::new();
        collect_lambda_sites(e, &mut sites);
        for d in sites {
            for (n, _) in &self.tp.defs[d].captures {
                out.insert(n.clone());
            }
        }
    }
}

pub fn collect_lambda_sites(e: &TExpr, out: &mut Vec<DefId>) {
    let mut go = |x: &TExpr| collect_lambda_sites(x, out);
    match &e.kind {
        TExprKind::Lambda(d) => out.push(*d),
        TExprKind::List(items) | TExprKind::MakeRecord(_, items) | TExprKind::Call(_, items) | TExprKind::Builtin(_, items) => items.iter().for_each(go),
        TExprKind::Field(o, _, _) | TExprKind::Member(o, _) | TExprKind::Not(o) | TExprKind::Neg(o) | TExprKind::MakeOk(o) | TExprKind::MakeErr(o) | TExprKind::MakeSome(o) | TExprKind::Abort(o) => go(o),
        TExprKind::SetField(o, _, _, v) | TExprKind::And(o, v) | TExprKind::Or(o, v) | TExprKind::BinOp(_, o, v) | TExprKind::RangeList(o, v) => {
            go(o);
            go(v);
        }
        TExprKind::CallValue(f, args) => {
            go(f);
            args.iter().for_each(go);
        }
        TExprKind::MethodCall { recv, args, .. } => {
            go(recv);
            args.iter().for_each(go);
        }
        TExprKind::If { cond, then, else_ } => {
            go(cond);
            go(then);
            go(else_);
        }
        TExprKind::Match { subject, arms } => {
            go(subject);
            for a in arms {
                if let Some(g) = &a.guard {
                    collect_lambda_sites(g, out);
                }
                collect_lambda_sites(&a.body, out);
            }
        }
        TExprKind::Block(b) => {
            for s in &b.stmts {
                lambda_sites_stmt(s, out);
            }
        }
        TExprKind::Pipe { left, func } => {
            go(left);
            go(func);
        }
        TExprKind::Stage { input, func, .. } => {
            go(input);
            go(func);
        }
        TExprKind::Handle { left, handler, .. } => {
            go(left);
            go(handler);
        }
        TExprKind::Range { start, end } => {
            go(start);
            if let Some(e) = end {
                go(e);
            }
        }
        TExprKind::Comprehension { iterables, filter, body, .. } => {
            iterables.iter().for_each(&mut go);
            if let Some(f) = filter {
                go(f);
            }
            go(body);
        }
        TExprKind::FString(parts) => {
            for p in parts {
                if let FPart::Expr(x, _) = p {
                    go(x);
                }
            }
        }
        _ => {}
    }
}

fn lambda_sites_stmt(s: &TStmt, out: &mut Vec<DefId>) {
    match &s.kind {
        TStmtKind::Let { value, .. } | TStmtKind::Assign { value, .. } | TStmtKind::Expr(value) => collect_lambda_sites(value, out),
        TStmtKind::Return(Some(v)) => collect_lambda_sites(v, out),
        TStmtKind::Bind { def, .. } => out.push(*def),
        TStmtKind::If { cond, then, elifs, else_ } => {
            collect_lambda_sites(cond, out);
            for s in &then.stmts {
                lambda_sites_stmt(s, out);
            }
            for (c, b) in elifs {
                collect_lambda_sites(c, out);
                for s in &b.stmts {
                    lambda_sites_stmt(s, out);
                }
            }
            if let Some(b) = else_ {
                for s in &b.stmts {
                    lambda_sites_stmt(s, out);
                }
            }
        }
        TStmtKind::Match { subject, arms } => {
            collect_lambda_sites(subject, out);
            for a in arms {
                collect_lambda_sites(&a.body, out);
            }
        }
        TStmtKind::While { cond, body } => {
            collect_lambda_sites(cond, out);
            for s in &body.stmts {
                lambda_sites_stmt(s, out);
            }
        }
        TStmtKind::For { iterables, body, .. } => {
            for i in iterables {
                collect_lambda_sites(i, out);
            }
            for s in &body.stmts {
                lambda_sites_stmt(s, out);
            }
        }
        _ => {}
    }
}

/// The local at the root of a receiver path (`a.b.c` -> `a`), if any.
fn root_local(e: &TExpr) -> Option<String> {
    match &e.kind {
        TExprKind::Local(n) => Some(n.clone()),
        TExprKind::Field(inner, _, _) | TExprKind::Member(inner, _) => root_local(inner),
        _ => None,
    }
}
