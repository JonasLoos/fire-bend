// src/lower/body.rs
// Statements: Core blocks -> Bend bodies. The forms (docs/compiler.md):
//
// * a structural match (on the descending parameter or a piece of it, at
//   the head of the body) is a real Bend match; the statements before it
//   are sunk into every arm;
// * an if or match statement without an early exit is a helper def that
//   answers its live-out variables, or a Bool.pick / case eliminator over
//   thunks when a branch calls the def itself; the body stays straight;
// * an if or match statement with an early exit (return, break, continue)
//   takes the rest of the block into its non-exiting branches;
// * a for loop is a driver from the prelude over a body def that answers a
//   control value; a while loop is the unsafe driver over the same shape.

use super::expr::builtin_mode;
use super::*;
use std::collections::HashSet;

/// How a block ends.
pub enum Ans {
    /// A pure value (returned in the def's mode).
    Value(Term),
    /// A term already in the def's monad (a tail call).
    Monadic(Term),
    /// The whole remaining body is this Bend body (a structural match with
    /// the preceding statements sunk into its arms).
    Whole(Body),
}

/// What a leaf block of a match or branch answers when it falls off its
/// end.
#[derive(Clone)]
pub enum Leaf {
    /// The def's result (`nothing`, or `Next` in a loop body).
    Result,
    /// The live-out variables, packed.
    Outs(Vec<(String, Ty)>),
    /// The last expression statement is the value.
    Value,
}

#[derive(Clone)]
pub struct LoopInfo {
    pub state: Vec<(String, Ty)>,
    pub state_ty: Ty,
    pub ret_ty: Ty,
}

#[derive(Clone)]
pub struct FnCtx {
    pub def: DefId,
    pub self_def: DefId,
    pub name: String,
    pub mode: Mode,
    pub tparams: Vec<(TVar, String)>,
    pub dicts: Vec<DictParam>,
    pub template: bool,
    pub unit: DefId,
    /// The unit's parameters with their kinds (template functions).
    pub fn_params: Vec<(String, FnParamKind)>,
    /// Variables in scope, by Bend name, with their types.
    pub scope: Vec<(String, Ty)>,
    /// Variables a structural match may inspect.
    pub pieces: HashSet<String>,
    pub structural: bool,
    /// Inside a thunk: matches and branches must be terms.
    pub term_mode: bool,
    pub loop_: Option<LoopInfo>,
    /// The def's result type (unwrapped).
    pub ret: Ty,
    /// Fire types of the locals, for match compilation.
    pub local_types: HashMap<String, Type>,
}

impl FnCtx {
    pub fn new(d: DefId, img: &Image) -> FnCtx {
        FnCtx {
            def: d,
            self_def: d,
            name: img.name.clone(),
            mode: img.mode,
            tparams: img.tparams.clone(),
            dicts: img.dicts.clone(),
            template: img.template,
            unit: img.unit,
            fn_params: Vec::new(),
            scope: Vec::new(),
            pieces: HashSet::new(),
            structural: true,
            term_mode: false,
            loop_: None,
            ret: img.ret.clone(),
            local_types: HashMap::new(),
        }
    }

    pub fn law(main: DefId) -> FnCtx {
        FnCtx {
            def: main,
            self_def: usize::MAX,
            name: "law".into(),
            mode: Mode::Pure,
            tparams: vec![],
            dicts: vec![],
            template: false,
            unit: main,
            fn_params: vec![],
            scope: vec![],
            pieces: HashSet::new(),
            structural: false,
            term_mode: true,
            loop_: None,
            ret: Ty::Unit,
            local_types: HashMap::new(),
        }
    }

    /// The template kind of a unit parameter by name.
    pub fn template_param(&self, name: &str) -> Option<FnParamKind> {
        self.fn_params.iter().find(|(n, _)| n == name).and_then(|(_, k)| match k {
            FnParamKind::Template { .. } => Some(k.clone()),
            _ => None,
        })
    }

    pub fn bind(&mut self, name: &str, ty: Ty, fire: Option<&Type>) {
        self.scope.retain(|(n, _)| n != name);
        self.scope.push((name.to_string(), ty));
        if let Some(t) = fire {
            self.local_types.insert(name.to_string(), t.clone());
        }
    }

    pub fn type_of(&self, name: &str) -> Option<Ty> {
        self.scope.iter().rev().find(|(n, _)| n == name).map(|(_, t)| t.clone())
    }

    /// The monad type of a value of inner type `t` in this def.
    pub fn wrap(&self, t: Ty) -> Ty {
        self.mode.wrap(t)
    }
}

impl<'a> Lower<'a> {
    /// Some value of a Fire type, built in place: the first constructor
    /// without fields (else the first), its fields filled the same way; a
    /// type variable takes the value `vals` gives it.
    pub fn default_value(&mut self, ctx: &FnCtx, t: &Type, vals: &[(TVar, Term)], line: usize) -> Term {
        match self.store.shallow(t) {
            Type::Var(v) => match vals.iter().find(|(w, _)| *w == v) {
                Some((_, x)) => x.clone(),
                None => {
                    self.error(line, "this def recurses on an int, and Bend needs a value of its result type for the case the recursion never reaches; the result has a generic part no parameter provides: recurse on a list instead, or mark the def `unsafe def`");
                    Term::unit()
                }
            },
            Type::Int => Term::U32(0),
            Type::Float => Term::F32(0.0),
            Type::Str => Term::Str(String::new()),
            Type::Bool => Term::boolean(false),
            Type::Unit => Term::unit(),
            Type::List(_) => Term::List(vec![]),
            Type::Map(v) => {
                let vt = self.ty_in(ctx, &v, line);
                Term::call("Map.new", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(vt)])
            }
            Type::Fn(..) => {
                self.error(line, "this def recurses on an int and answers a function: Bend needs a value of the result type for the case the recursion never reaches; mark the def `unsafe def`");
                Term::unit()
            }
            Type::Data(tid, args) => {
                if tid == MAYBE {
                    return Term::ctor("None", vec![]);
                }
                let dt = self.core.types[tid].clone();
                let ci = dt.ctors.iter().position(|c| c.fields.is_empty()).unwrap_or(0);
                let fields: Vec<Type> = dt.ctors[ci].fields.iter().map(|f| f.ty.clone()).collect();
                let vals2: Vec<Term> = fields.iter().map(|ft| {
                    let ft = self.subst_field(tid, ft, &args);
                    self.default_value(ctx, &ft, vals, line)
                }).collect();
                Term::Ctor(self.ctor_name(tid, ci), vals2)
            }
        }
    }

    // -- def bodies ----------------------------------------------------------------------------

    pub fn lower_def_body(&mut self, ctx: &mut FnCtx, def: &Def, img: &Image) -> Body {
        let line = def.line;
        // the unit's function parameters and their kinds
        let unit_def = self.core.defs[img.unit].clone();
        let unit_img = self.images[img.unit].clone().unwrap();
        ctx.fn_params = unit_def.params.iter().zip(unit_img.fnp.iter()).map(|(p, k)| (p.name.clone(), k.clone())).collect();
        // parameters in scope
        for (i, p) in def.params.iter().enumerate() {
            match &img.fnp[i] {
                FnParamKind::Template { env, env_ty, .. } => ctx.bind(env, Ty::Param(env_ty.clone()), None),
                _ => ctx.bind(&local_name(&p.name), img.params[i].clone(), Some(&p.ty)),
            }
        }
        for (n, t) in &unit_def.params.iter().zip(unit_img.fnp.iter()).filter_map(|(p, k)| match k {
            FnParamKind::Template { env, env_ty, .. } => Some((env.clone(), Ty::Param(env_ty.clone()))),
            _ => None,
        }).collect::<Vec<_>>() {
            ctx.bind(n, t.clone(), None);
        }
        // captures
        let mut caps = Vec::new();
        for (n, t) in &def.captures {
            let (name, ty) = match ctx.template_param(n) {
                Some(FnParamKind::Template { env, env_ty, .. }) => (env, Ty::Param(env_ty)),
                _ => (local_name(n), self.ty_in(ctx, t, line)),
            };
            ctx.bind(&name, ty, Some(t));
            caps.push((name, false));
        }
        // members of the receiver
        let mut fields: Vec<(String, bool)> = Vec::new();
        let mut self_ctor = String::new();
        if let DefKind::Method { rec, .. } = &def.kind {
            let t = self.core.types[*rec].clone();
            let selft = def.params[0].ty.clone();
            let args = match self.store.shallow(&selft) {
                Type::Data(_, a) => a,
                _ => vec![],
            };
            for f in &t.ctors[0].fields {
                let ft = self.subst_field(*rec, &f.ty, &args);
                let bt = self.ty_in(ctx, &ft, line);
                ctx.bind(&local_name(&f.name), bt, Some(&ft));
                fields.push((local_name(&f.name), false));
            }
            self_ctor = self.ctor_name(*rec, 0);
        }
        if let Descent::Structural(order) = &def.descent {
            for &i in order {
                ctx.pieces.insert(local_name(&def.params[i].name));
            }
        }
        let stmts = def.body.stmts.clone();
        let inner = if let Descent::Fuel(_) = def.descent {
            // count a fuel down; at zero the branch is dead by the guard
            ctx.pieces.clear();
            let dflt = {
                // a type variable in the result is filled from a parameter of
                // exactly that type (any value does: the branch is dead)
                let mut vals: Vec<(TVar, Term)> = vec![];
                for (i, p) in def.params.iter().enumerate() {
                    if let (Type::Var(v), FnParamKind::Value) = (self.store.shallow(&p.ty), &img.fnp[i]) {
                        if !vals.iter().any(|(w, _)| *w == v) {
                            vals.push((v, Term::var(&local_name(&p.name))));
                        }
                    }
                }
                let t = self.default_value(ctx, &def.ret, &vals, line);
                let rty = ctx.ret.clone();
                self.lift_mode(t, Mode::Pure, ctx.mode, &rty)
            };
            let zero = self.finish_body(ctx, vec![], Ans::Monadic(dflt));
            let body = self.lower_block_body(ctx, &stmts, Leaf::Result);
            Body::Match { scrutinee: "fuel".into(), arms: vec![(ir::Pat::Zero, zero), (ir::Pat::Succ("fuel_".into()), body)] }
        } else {
            self.lower_block_body(ctx, &stmts, Leaf::Result)
        };
        // open the receiver and the environment at the head
        let inner = if fields.is_empty() { inner } else { Body::Match { scrutinee: local_name("self"), arms: vec![(ir::Pat::Ctor(self_ctor, fields), inner)] } };
        if caps.is_empty() {
            inner
        } else {
            let (tn, _) = img.env.clone().unwrap();
            Body::Match { scrutinee: "env".into(), arms: vec![(ir::Pat::Ctor(tn, caps), inner)] }
        }
    }

    /// A field's type of a data type instantiated at `args`.
    pub fn subst_field(&mut self, tid: TypeId, fty: &Type, args: &[Type]) -> Type {
        let params = self.core.types[tid].params.clone();
        let subst: Vec<(TVar, Type)> = params.iter().cloned().zip(args.iter().cloned()).collect();
        self.store.substitute(fty, &subst)
    }

    /// The field types of a constructor at the type's arguments.
    pub fn field_types(&mut self, tid: TypeId, ci: usize, args: &[Type]) -> Vec<Type> {
        let fields: Vec<Type> = self.core.types[tid].ctors[ci].fields.iter().map(|f| f.ty.clone()).collect();
        fields.iter().map(|t| self.subst_field(tid, t, args)).collect()
    }

    // -- blocks --------------------------------------------------------------------------------

    /// Lower a block into a body in the def's mode.
    pub fn lower_block_body(&mut self, ctx: &mut FnCtx, stmts: &[Stmt], leaf: Leaf) -> Body {
        let mut out = Vec::new();
        let saved_scope = ctx.scope.clone();
        let ans = self.lower_stmts_into(ctx, stmts, &mut out, &leaf);
        let ans = match ans {
            Some(a) => a,
            None => self.fall_off(ctx, &leaf, &mut out),
        };
        ctx.scope = saved_scope;
        self.finish_body(ctx, out, ans)
    }

    /// What a block answers when it ends without an exit.
    fn fall_off(&mut self, ctx: &mut FnCtx, leaf: &Leaf, out: &mut Vec<ir::Stmt>) -> Ans {
        match leaf {
            Leaf::Result => match ctx.loop_.clone() {
                Some(l) => {
                    let s = self.pack_state(ctx, &l);
                    Ans::Value(Term::ctor("F.Next", vec![s]))
                }
                None => Ans::Value(Term::unit()),
            },
            Leaf::Outs(vars) => {
                let terms: Vec<Term> = vars.iter().map(|(n, _)| Term::var(n)).collect();
                let tys: Vec<Ty> = vars.iter().map(|(_, t)| t.clone()).collect();
                Ans::Value(self.pack(terms, &tys))
            }
            Leaf::Value => {
                let _ = out;
                Ans::Value(Term::unit())
            }
        }
    }

    pub fn finish_body(&mut self, ctx: &mut FnCtx, out: Vec<ir::Stmt>, ans: Ans) -> Body {
        match ans {
            Ans::Whole(b) => b,
            Ans::Value(t) => match ctx.mode {
                Mode::Pure => Body::Block { stmts: out, tail: t },
                _ => Body::Do { monad: ctx.wrap(self.tail_ty(ctx)), stmts: out, tail: ir::DoTail::Return(t) },
            },
            Ans::Monadic(t) => match ctx.mode {
                Mode::Pure => Body::Block { stmts: out, tail: t },
                _ => Body::Do { monad: ctx.wrap(self.tail_ty(ctx)), stmts: out, tail: ir::DoTail::Step(t) },
            },
        }
    }

    /// The inner result type of the body being lowered (the do-block's
    /// type parameter): tracked in the context by the caller.
    fn tail_ty(&self, ctx: &FnCtx) -> Ty {
        ctx.ret.clone()
    }

    /// A block as a single term in the def's mode.
    pub fn block_term(&mut self, ctx: &mut FnCtx, stmts: &[Stmt], leaf: Leaf, ret: &Ty) -> Term {
        let mut sub = ctx.clone();
        sub.term_mode = true;
        sub.structural = false;
        sub.ret = ret.clone();
        let body = self.lower_block_body(&mut sub, stmts, leaf);
        self.body_to_term(ctx, body, ret)
    }

    /// An expression as a single term in the def's mode.
    pub fn expr_as_term(&mut self, ctx: &mut FnCtx, e: &Expr, mode: Mode) -> Term {
        let line = e.line;
        let rty = self.ty_in(ctx, &e.ty, line);
        let mut sub = ctx.clone();
        sub.term_mode = true;
        sub.structural = false;
        sub.mode = mode;
        sub.ret = rty.clone();
        let mut out = Vec::new();
        let ans = self.expr_tail(&mut sub, e, &mut out);
        let body = self.finish_body(&mut sub, out, ans);
        self.body_to_term(&mut sub, body, &rty)
    }

    /// A body as a term: lets become applications, binds become `M.bind`.
    pub fn body_to_term(&mut self, ctx: &mut FnCtx, body: Body, ret: &Ty) -> Term {
        match body {
            Body::Block { stmts, tail } => {
                let mut t = tail;
                for s in stmts.into_iter().rev() {
                    t = self.stmt_around(ctx, s, t, ret, false);
                }
                t
            }
            Body::Do { stmts, tail, .. } => {
                let mut t = match tail {
                    ir::DoTail::Return(v) => self.lift_mode(v, Mode::Pure, ctx.mode, ret),
                    ir::DoTail::Step(m) => m,
                };
                for s in stmts.into_iter().rev() {
                    t = self.stmt_around(ctx, s, t, ret, true);
                }
                t
            }
            Body::Match { .. } => {
                self.error(0, "internal: a match cannot be a term");
                Term::unit()
            }
        }
    }

    fn stmt_around(&mut self, ctx: &mut FnCtx, s: ir::Stmt, rest: Term, ret: &Ty, monadic: bool) -> Term {
        match s {
            ir::Stmt::Let { name, value, .. } => Term::App(Box::new(Term::Lam(vec![name], Box::new(rest))), vec![value]),
            ir::Stmt::Bind { name, ty, value, .. } => self.bind_term(ctx, name, ty, value, rest, ret),
            ir::Stmt::Step(m) => {
                let _ = monadic;
                self.bind_term(ctx, "_".into(), Ty::Unit, m, rest, ret)
            }
            ir::Stmt::Destructure { ctor, fields, value } => {
                // (K{a, b} = v; rest) as a match through a lambda is not a
                // term; use the projections instead
                let _ = (ctor, fields, value);
                rest
            }
            ir::Stmt::TupleLet { .. } | ir::Stmt::ParLet { .. } => rest,
        }
    }

    /// `M.bind(A, R, m, x => rest)`.
    fn bind_term(&mut self, ctx: &mut FnCtx, name: String, ty: Ty, m: Term, rest: Term, ret: &Ty) -> Term {
        let k = Term::Lam(vec![name], Box::new(rest));
        match ctx.mode {
            Mode::Io => Term::call("IO.bind", vec![Term::TyArg(ty), Term::TyArg(ret.clone()), m, k]),
            Mode::Result => Term::call("Result.bind", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(Ty::Param("&2".into())), Term::TyArg(Ty::Str), Term::TyArg(ty), Term::TyArg(ret.clone()), m, k]),
            Mode::Pure => Term::App(Box::new(k), vec![m]),
        }
    }

    /// Lower statements, appending to `out`. Answers Some when a statement
    /// ended the block (an exit, or a structural match that took the rest).
    pub fn lower_stmts_into(&mut self, ctx: &mut FnCtx, stmts: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf) -> Option<Ans> {
        let mut i = 0;
        while i < stmts.len() {
            let s = &stmts[i];
            let rest = &stmts[i + 1..];
            let line = s.line;
            match &s.kind {
                StmtKind::Let { name, value } | StmtKind::Assign { name, value } => {
                    let t = self.expr(ctx, value, out);
                    let ty = self.ty_in(ctx, &value.ty, line);
                    let n = local_name(name);
                    out.push(ir::Stmt::Let { name: n.clone(), reusable: false, ty: Some(ty.clone()), value: t });
                    ctx.bind(&n, ty, Some(&value.ty));
                    ctx.structural = ctx.structural && true;
                }
                StmtKind::Bind { name, def } => {
                    let e = Expr { kind: ExprKind::Lambda(*def), ty: self.core.defs[*def].scheme.ty.clone(), line };
                    let t = self.expr(ctx, &e, out);
                    let ty = self.ty_in(ctx, &e.ty, line);
                    out.push(ir::Stmt::Let { name: name.clone(), reusable: false, ty: Some(ty.clone()), value: t });
                    ctx.bind(name, ty, Some(&e.ty));
                }
                StmtKind::Expr(e) => {
                    // the last expression of a value leaf is the answer
                    if i + 1 == stmts.len() {
                        if let Leaf::Value = leaf {
                            return Some(self.expr_tail(ctx, e, out));
                        }
                    }
                    self.expr_stmt(ctx, e, out);
                }
                StmtKind::Return(e) => {
                    return Some(self.return_of(ctx, e, out));
                }
                StmtKind::Break => {
                    let l = ctx.loop_.clone().expect("a loop");
                    let s = self.pack_state(ctx, &l);
                    return Some(Ans::Value(Term::ctor("F.Break", vec![s])));
                }
                StmtKind::Continue => {
                    let l = ctx.loop_.clone().expect("a loop");
                    let s = self.pack_state(ctx, &l);
                    return Some(Ans::Value(Term::ctor("F.Next", vec![s])));
                }
                StmtKind::If { cond, then, else_ } => {
                    ctx.structural = false;
                    if let Some(a) = self.lower_if(ctx, cond, then, else_, rest, out, leaf, line) {
                        return Some(a);
                    }
                }
                StmtKind::Match { subject, arms } => {
                    if let Some(a) = self.lower_match_stmt(ctx, subject, arms, rest, out, leaf, line) {
                        return Some(a);
                    }
                    ctx.structural = false;
                }
                StmtKind::For { patterns, iters, body } => {
                    ctx.structural = false;
                    if let Some(a) = self.lower_for(ctx, patterns, iters, body, rest, out, leaf, line) {
                        return Some(a);
                    }
                }
                StmtKind::While { cond, body } => {
                    ctx.structural = false;
                    if let Some(a) = self.lower_while(ctx, cond, body, rest, out, leaf, line) {
                        return Some(a);
                    }
                }
            }
            i += 1;
        }
        None
    }

    /// `return e`: the def's answer, or a `Return` control value in a loop.
    fn return_of(&mut self, ctx: &mut FnCtx, e: &Expr, out: &mut Vec<ir::Stmt>) -> Ans {
        if ctx.loop_.is_some() {
            let t = self.expr(ctx, e, out);
            return Ans::Value(Term::ctor("F.Return", vec![t]));
        }
        self.expr_tail(ctx, e, out)
    }

    /// An expression in tail position: a call in the def's own monad is
    /// the tail itself, anything else a value.
    pub fn expr_tail(&mut self, ctx: &mut FnCtx, e: &Expr, out: &mut Vec<ir::Stmt>) -> Ans {
        let line = e.line;
        // a match on a parameter (or a piece of one) as the value: a real
        // match, so that recursion under it descends structurally
        if let ExprKind::Match(subject, arms) = &e.kind {
            if self.match_is_structural(ctx, subject, arms) {
                if let Some(ans) = self.lower_match_stmt(ctx, subject, arms, &[], out, &Leaf::Value, line) {
                    return ans;
                }
            }
        }
        if ctx.mode != Mode::Pure && ctx.loop_.is_none() {
            let mode = self.expr_mode(ctx, e);
            if mode == ctx.mode {
                if let ExprKind::Call { .. } | ExprKind::CallClosure(..) | ExprKind::Builtin(..) | ExprKind::Abort(_) = &e.kind {
                    // lower without binding the outermost call
                    let mut sub = Vec::new();
                    let t = self.expr(ctx, e, &mut sub);
                    // the last statement is the bind of the call itself
                    if let Some(ir::Stmt::Bind { name, value, .. }) = sub.last().cloned() {
                        if matches!(&t, Term::Var(v) if *v == name) {
                            sub.pop();
                            out.extend(sub);
                            let _ = line;
                            return Ans::Monadic(value);
                        }
                    }
                    out.extend(sub);
                    return Ans::Value(t);
                }
            }
        }
        let t = self.expr(ctx, e, out);
        Ans::Value(t)
    }

    /// The mode of what an expression does.
    fn expr_mode(&self, ctx: &FnCtx, e: &Expr) -> Mode {
        match &e.kind {
            ExprKind::Call { def, .. } => {
                if *def == ctx.self_def { ctx.mode } else { Mode::of(self.core.defs[*def].effect) }
            }
            ExprKind::CallClosure(f, _) => match self.store.shallow(&f.ty) {
                Type::Fn(_, _, c) => self.closure_mode(c),
                _ => Mode::Pure,
            },
            ExprKind::Builtin(n, _) => builtin_mode(n),
            ExprKind::Abort(_) => if ctx.mode == Mode::Io { Mode::Io } else { Mode::Result },
            ExprKind::Dict { id, .. } => self.dict_mode(*id),
            _ => Mode::Pure,
        }
    }

    /// An expression statement: a monadic call is a step, anything else is
    /// evaluated for its binds and dropped.
    fn expr_stmt(&mut self, ctx: &mut FnCtx, e: &Expr, out: &mut Vec<ir::Stmt>) {
        let mode = self.expr_mode(ctx, e);
        if mode != Mode::Pure && ctx.mode != Mode::Pure {
            let mut sub = Vec::new();
            let t = self.expr(ctx, e, &mut sub);
            // a unit action is a step of the do-block; a value is bound and dropped
            let unit = matches!(self.store.shallow(&e.ty), Type::Unit);
            if let Some(ir::Stmt::Bind { name, value, .. }) = sub.last().cloned() {
                if unit && matches!(&t, Term::Var(v) if *v == name) {
                    sub.pop();
                    out.extend(sub);
                    out.push(ir::Stmt::Step(value));
                    return;
                }
            }
            out.extend(sub);
            return;
        }
        let mut sub = Vec::new();
        let _ = self.expr(ctx, e, &mut sub);
        out.extend(sub);
    }

    // -- packing ---------------------------------------------------------------------------------

    /// Several values as one: nothing, the value itself, or an out record.
    pub fn pack(&mut self, terms: Vec<Term>, tys: &[Ty]) -> Term {
        match terms.len() {
            0 => Term::unit(),
            1 => terms.into_iter().next().unwrap(),
            n => {
                let name = self.out_type(n);
                let _ = tys;
                Term::Ctor(name, terms)
            }
        }
    }

    pub fn pack_ty(&mut self, tys: &[Ty]) -> Ty {
        match tys.len() {
            0 => Ty::Unit,
            1 => tys[0].clone(),
            n => {
                let name = self.out_type(n);
                Ty::Named(name, tys.to_vec())
            }
        }
    }

    /// The i-th value of a packed term.
    pub fn unpack(&mut self, packed: Term, tys: &[Ty], i: usize) -> Term {
        match tys.len() {
            1 => packed,
            n => {
                let name = self.out_type(n);
                let mut args: Vec<Term> = tys.iter().map(|t| Term::TyArg(t.clone())).collect();
                args.push(packed);
                Term::Call(format!("{}.v{}", name, i), args)
            }
        }
    }

    fn pack_state(&mut self, ctx: &mut FnCtx, l: &LoopInfo) -> Term {
        let _ = ctx;
        let terms: Vec<Term> = l.state.iter().map(|(n, _)| Term::var(n)).collect();
        let tys: Vec<Ty> = l.state.iter().map(|(_, t)| t.clone()).collect();
        self.pack(terms, &tys)
    }

    /// Bind the values of a packed term to the variables, in `out`.
    fn unpack_into(&mut self, ctx: &mut FnCtx, packed: &str, vars: &[(String, Ty)], out: &mut Vec<ir::Stmt>) {
        let tys: Vec<Ty> = vars.iter().map(|(_, t)| t.clone()).collect();
        for (i, (n, t)) in vars.iter().enumerate() {
            let v = self.unpack(Term::var(packed), &tys, i);
            out.push(ir::Stmt::Let { name: n.clone(), reusable: false, ty: Some(t.clone()), value: v });
            ctx.bind(n, t.clone(), None);
        }
    }

    // -- analysis ---------------------------------------------------------------------------------

    /// Variables assigned in a block that exist in the scope.
    fn live_outs(&self, ctx: &FnCtx, blocks: &[&Block]) -> Vec<(String, Ty)> {
        let mut names: Vec<String> = Vec::new();
        for b in blocks {
            for_each_stmt(b, &mut |s: &Stmt| {
                if let StmtKind::Assign { name, .. } = &s.kind {
                    let n = local_name(name);
                    if !names.contains(&n) {
                        names.push(n);
                    }
                }
            });
        }
        names.into_iter().filter_map(|n| ctx.type_of(&n).map(|t| (n, t))).collect()
    }

    /// Variables of the scope that a block reads.
    fn live_ins(&self, ctx: &FnCtx, blocks: &[&Block], extra: &[&Expr]) -> Vec<(String, Ty)> {
        let mut used: HashSet<String> = HashSet::new();
        let mut note = |e: &Expr| {
            if let ExprKind::Var(v) = &e.kind {
                match ctx.template_param(v) {
                    Some(FnParamKind::Template { env, .. }) => {
                        used.insert(env);
                    }
                    _ => {
                        used.insert(local_name(v));
                    }
                }
            }
            if let ExprKind::SelfValue(tid) = &e.kind {
                for f in &self.core.types[*tid].ctors[0].fields {
                    used.insert(local_name(&f.name));
                }
            }
            if let ExprKind::Lambda(d) = &e.kind {
                for (n, _) in &self.core.defs[*d].captures {
                    match ctx.template_param(n) {
                        Some(FnParamKind::Template { env, .. }) => {
                            used.insert(env);
                        }
                        _ => {
                            used.insert(local_name(n));
                        }
                    }
                }
            }
        };
        for b in blocks {
            walk_block(b, &mut note);
        }
        for e in extra {
            walk_expr(e, &mut note);
        }
        for b in blocks {
            for_each_stmt(b, &mut |s: &Stmt| match &s.kind {
                StmtKind::Bind { def, .. } => {
                    for (n, _) in &self.core.defs[*def].captures {
                        used.insert(local_name(n));
                    }
                }
                // a variable assigned on some path keeps its value on the others
                StmtKind::Assign { name, .. } => {
                    used.insert(local_name(name));
                }
                _ => {}
            });
        }
        ctx.scope.iter().filter(|(n, _)| used.contains(n)).cloned().collect()
    }

    fn block_has_self_call(&self, ctx: &FnCtx, b: &Block) -> bool {
        let mut found = false;
        walk_block(b, &mut |e: &Expr| {
            if let ExprKind::Call { def, .. } = &e.kind {
                if *def == ctx.self_def {
                    found = true;
                }
            }
        });
        found
    }

    /// Whether a block may leave the enclosing body early.
    fn block_exits(&self, b: &Block) -> bool {
        let mut found = false;
        for_each_stmt(b, &mut |s: &Stmt| {
            if matches!(s.kind, StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue) {
                found = true;
            }
        });
        found
    }

    fn block_always_exits(&self, b: &Block) -> bool {
        match b.stmts.last() {
            Some(Stmt { kind: StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue, .. }) => true,
            Some(Stmt { kind: StmtKind::If { then, else_, .. }, .. }) => !else_.stmts.is_empty() && self.block_always_exits(then) && self.block_always_exits(else_),
            _ => false,
        }
    }

    // -- helper defs -----------------------------------------------------------------------------

    /// The arguments forwarding the unit's template parameters to a helper.
    pub fn forward_args(&mut self, ctx: &FnCtx) -> Vec<Term> {
        let mut args = Vec::new();
        if ctx.template {
            for (_, n) in &ctx.tparams {
                args.push(Term::TmplTy(Ty::Param(n.clone())));
            }
        }
        for (_, k) in &ctx.fn_params {
            if let FnParamKind::Template { env_ty, .. } = k {
                args.push(Term::TmplTy(Ty::Param(env_ty.clone())));
            }
        }
        for dp in &ctx.dicts {
            args.push(Term::TmplRef(dp.name.clone()));
        }
        for (_, k) in &ctx.fn_params {
            if let FnParamKind::Template { code, .. } = k {
                args.push(Term::TmplRef(code.clone()));
            }
        }
        if !ctx.template {
            for (_, n) in &ctx.tparams {
                args.push(Term::TyArg(Ty::Param(n.clone())));
            }
        }
        args
    }

    /// Emit a helper def of the current unit with value parameters and a
    /// body, answering `ret` in the def's mode. Returns its name.
    pub fn emit_helper(&mut self, ctx: &FnCtx, hint: &str, params: Vec<(String, Ty)>, ret: Ty, body: Body) -> String {
        self.counter += 1;
        let name = format!("{}.F.{}{}", ctx.name, hint, self.counter);
        let mut tmpl_types = Vec::new();
        let mut erased = Vec::new();
        for (_, n) in &ctx.tparams {
            if ctx.template {
                tmpl_types.push(n.clone());
            } else {
                erased.push(n.clone());
            }
        }
        let mut tmpl_funcs = Vec::new();
        for dp in &ctx.dicts {
            tmpl_funcs.push((dp.name.clone(), dp.ty.clone()));
        }
        let unit_def = self.core.defs[ctx.unit].clone();
        for (i, (_, k)) in ctx.fn_params.iter().enumerate() {
            if let FnParamKind::Template { code, env_ty, .. } = k {
                tmpl_types.push(env_ty.clone());
                let fty = self.template_code_ty_pub(&unit_def.params[i].ty, env_ty, &ctx.tparams.clone(), unit_def.line);
                tmpl_funcs.push((code.clone(), fty));
            }
        }
        let mut d = IrDef {
            name: name.clone(),
            is_unsafe: false,
            tmpl_types,
            tmpl_funcs,
            erased,
            params: params.into_iter().map(|(n, t)| IrParam { name: n, reusable: false, ty: t }).collect(),
            ret: ctx.wrap(ret),
            body,
        };
        self.mark_reusable(&mut d);
        self.defs.push(d);
        name
    }

    pub fn template_code_ty_pub(&mut self, fty: &Type, env_ty: &str, names: &[(TVar, String)], line: usize) -> Ty {
        match self.store.shallow(fty) {
            Type::Fn(ps, r, c) => {
                let mut params = vec![Ty::Param(env_ty.to_string())];
                for p in &ps {
                    params.push(self.ty(p, names, line));
                }
                let mode = self.closure_mode(c);
                let r = self.ty(&r, names, line);
                Ty::func(params, mode.wrap(r))
            }
            _ => Ty::Unit,
        }
    }

    /// Bind the answer of a helper call or a pick.
    fn bind_answer(&mut self, ctx: &mut FnCtx, t: Term, ty: &Ty, monadic: bool, out: &mut Vec<ir::Stmt>) -> String {
        let r = self.fresh("r");
        if monadic && ctx.mode != Mode::Pure {
            out.push(ir::Stmt::Bind { name: r.clone(), reusable: false, ty: ty.clone(), value: t });
        } else {
            out.push(ir::Stmt::Let { name: r.clone(), reusable: false, ty: Some(ty.clone()), value: t });
        }
        r
    }

    /// `Bool.pick(Unit -> M<T>, c, _ => a, _ => b)(Unit{})`.
    fn pick_thunks(&mut self, c: Term, a: Term, b: Term, mty: Ty) -> Term {
        let pick = Term::call("Bool.pick", vec![Term::TyArg(Ty::func(vec![Ty::Unit], mty)), c, Term::Lam(vec!["_".into()], Box::new(a)), Term::Lam(vec!["_".into()], Box::new(b))]);
        Term::App(Box::new(pick), vec![Term::unit()])
    }

    // -- if -----------------------------------------------------------------------------------------

    fn lower_if(&mut self, ctx: &mut FnCtx, cond: &Expr, then: &Block, else_: &Block, rest: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf, line: usize) -> Option<Ans> {
        let c = self.expr(ctx, cond, out);
        let exits = self.block_exits(then) || self.block_exits(else_);
        if exits || matches!(leaf, Leaf::Value) && !rest.is_empty() {
            // the rest of the block goes into the branches that fall through
            let mut then2 = then.stmts.clone();
            let mut else2 = else_.stmts.clone();
            if !self.block_always_exits(then) {
                then2.extend(rest.iter().cloned());
            }
            if !self.block_always_exits(else_) {
                else2.extend(rest.iter().cloned());
            }
            let ret = self.leaf_ty(ctx, leaf);
            let a = self.block_term(ctx, &then2, leaf.clone(), &ret);
            let b = self.block_term(ctx, &else2, leaf.clone(), &ret);
            let t = self.pick_thunks(c, a, b, ctx.wrap(ret));
            return Some(Ans::Monadic(t));
        }
        let outs = self.live_outs(ctx, &[then, else_]);
        let tys: Vec<Ty> = outs.iter().map(|(_, t)| t.clone()).collect();
        let out_ty = self.pack_ty(&tys);
        let self_call = self.block_has_self_call(ctx, then) || self.block_has_self_call(ctx, else_);
        let t = if self_call || ctx.term_mode {
            let a = self.block_term(ctx, &then.stmts, Leaf::Outs(outs.clone()), &out_ty);
            let b = self.block_term(ctx, &else_.stmts, Leaf::Outs(outs.clone()), &out_ty);
            self.pick_thunks(c, a, b, ctx.wrap(out_ty.clone()))
        } else {
            // a helper matching the condition
            let ins = self.live_ins(ctx, &[then, else_], &[]);
            let mut sub = ctx.clone();
            sub.structural = false;
            sub.ret = out_ty.clone();
            sub.scope = ins.clone();
            let ta = self.lower_block_body(&mut sub, &then.stmts, Leaf::Outs(outs.clone()));
            let mut sub2 = ctx.clone();
            sub2.structural = false;
            sub2.ret = out_ty.clone();
            sub2.scope = ins.clone();
            let tb = self.lower_block_body(&mut sub2, &else_.stmts, Leaf::Outs(outs.clone()));
            let mut params = ins.clone();
            params.push(("__c".into(), Ty::Bool));
            let body = Body::Match { scrutinee: "__c".into(), arms: vec![(ir::Pat::Ctor("True".into(), vec![]), ta), (ir::Pat::Ctor("False".into(), vec![]), tb)] };
            let name = self.emit_helper(ctx, "if", params, out_ty.clone(), body);
            let mut args = self.forward_args(ctx);
            for (n, _) in &ins {
                args.push(Term::var(n));
            }
            args.push(c);
            Term::Call(name, args)
        };
        let _ = line;
        if outs.is_empty() {
            if ctx.mode == Mode::Pure {
                // nothing to do
            } else {
                out.push(ir::Stmt::Step(t));
            }
            return None;
        }
        let r = self.bind_answer(ctx, t, &out_ty, true, out);
        self.unpack_into(ctx, &r, &outs, out);
        None
    }

    /// The inner type a leaf answers.
    fn leaf_ty(&mut self, ctx: &FnCtx, leaf: &Leaf) -> Ty {
        match leaf {
            Leaf::Result => match &ctx.loop_ {
                Some(l) => Ty::Named("F.Ctl".into(), vec![l.state_ty.clone(), l.ret_ty.clone()]),
                None => ctx.ret.clone(),
            },
            Leaf::Outs(vars) => {
                let tys: Vec<Ty> = vars.iter().map(|(_, t)| t.clone()).collect();
                self.pack_ty(&tys)
            }
            Leaf::Value => ctx.ret.clone(),
        }
    }

    // -- match ----------------------------------------------------------------------------------------

    /// A pattern built only from constructors and binders.
    fn constructor_shaped(&self, p: &Pat) -> bool {
        match p {
            Pat::Bind(_) | Pat::Wild => true,
            Pat::Lit(Lit::Bool(_)) => true,
            Pat::Lit(_) => false,
            Pat::Con(_, _, subs) => subs.iter().all(|s| self.constructor_shaped(s)),
            Pat::List(items, _) => items.iter().all(|s| self.constructor_shaped(s)),
        }
    }

    /// A match that becomes a real Bend match: on a parameter or a piece of
    /// one, in a def body (not inside a term), with constructor patterns only.
    fn match_is_structural(&self, ctx: &FnCtx, subject: &Expr, arms: &[Arm]) -> bool {
        let subject_var = match &subject.kind {
            ExprKind::Var(v) => Some(local_name(v)),
            _ => None,
        };
        ctx.structural && !ctx.term_mode && subject_var.as_ref().is_some_and(|v| ctx.pieces.contains(v)) && arms.iter().all(|a| a.guard.is_none() && self.constructor_shaped(&a.pat))
    }

    fn lower_match_stmt(&mut self, ctx: &mut FnCtx, subject: &Expr, arms: &[Arm], rest: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf, line: usize) -> Option<Ans> {
        let subject_var = match &subject.kind {
            ExprKind::Var(v) => Some(local_name(v)),
            _ => None,
        };
        let structural = self.match_is_structural(ctx, subject, arms);
        // arm bodies as statement lists
        let arm_stmts: Vec<Vec<Stmt>> = arms.iter().map(|a| arm_block(a)).collect();
        if structural {
            // a real match: the statements so far are sunk into every arm,
            // and the rest of the block follows each arm
            let sunk = std::mem::take(out);
            let rows: Vec<Row> = arms.iter().zip(arm_stmts.iter()).map(|(a, b)| {
                let mut stmts = b.clone();
                if !self.block_always_exits(&Block { stmts: b.clone() }) {
                    stmts.extend(rest.iter().cloned());
                }
                Row { pats: vec![a.pat.clone()], guard: None, body: stmts, binds: vec![] }
            }).collect();
            let sv = subject_var.unwrap();
            let sty = subject.ty.clone();
            let body = self.compile_rows(ctx, vec![(sv, sty)], rows, true, leaf, &sunk, line);
            return Some(Ans::Whole(body));
        }
        let exits = arm_stmts.iter().any(|b| self.block_exits(&Block { stmts: b.clone() }));
        let value_leaf = matches!(leaf, Leaf::Value) && !rest.is_empty();
        if exits || value_leaf {
            let rows: Vec<Row> = arms.iter().zip(arm_stmts.iter()).map(|(a, b)| {
                let mut stmts = b.clone();
                if !self.block_always_exits(&Block { stmts: b.clone() }) {
                    stmts.extend(rest.iter().cloned());
                }
                Row { pats: vec![a.pat.clone()], guard: a.guard.clone(), body: stmts, binds: vec![] }
            }).collect();
            let ret = self.leaf_ty(ctx, leaf);
            let t = self.match_term(ctx, subject, rows, leaf, &ret, out, line);
            return Some(Ans::Monadic(t));
        }
        let blocks: Vec<Block> = arm_stmts.iter().map(|b| Block { stmts: b.clone() }).collect();
        let refs: Vec<&Block> = blocks.iter().collect();
        let outs = self.live_outs(ctx, &refs);
        let tys: Vec<Ty> = outs.iter().map(|(_, t)| t.clone()).collect();
        let out_ty = self.pack_ty(&tys);
        let rows: Vec<Row> = arms.iter().zip(arm_stmts.iter()).map(|(a, b)| Row { pats: vec![a.pat.clone()], guard: a.guard.clone(), body: b.clone(), binds: vec![] }).collect();
        let self_call = blocks.iter().any(|b| self.block_has_self_call(ctx, b));
        let t = if self_call || ctx.term_mode {
            self.match_term(ctx, subject, rows, &Leaf::Outs(outs.clone()), &out_ty, out, line)
        } else {
            self.match_helper(ctx, subject, rows, &Leaf::Outs(outs.clone()), &out_ty, &refs, out, line)
        };
        if outs.is_empty() {
            if ctx.mode != Mode::Pure {
                out.push(ir::Stmt::Step(t));
            }
            return None;
        }
        let r = self.bind_answer(ctx, t, &out_ty, true, out);
        self.unpack_into(ctx, &r, &outs, out);
        None
    }

    /// A match as a value.
    pub fn lower_match_expr(&mut self, ctx: &mut FnCtx, subject: &Expr, arms: &[Arm], ty: &Type, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let rty = self.ty_in(ctx, ty, line);
        let rows: Vec<Row> = arms.iter().map(|a| Row { pats: vec![a.pat.clone()], guard: a.guard.clone(), body: vec![Stmt { kind: StmtKind::Expr(a.body.clone()), line: a.line }], binds: vec![] }).collect();
        let blocks: Vec<Block> = rows.iter().map(|r| Block { stmts: r.body.clone() }).collect();
        let refs: Vec<&Block> = blocks.iter().collect();
        let self_call = blocks.iter().any(|b| self.block_has_self_call(ctx, b));
        let t = if self_call || ctx.term_mode {
            self.match_term(ctx, subject, rows, &Leaf::Value, &rty, pre, line)
        } else {
            self.match_helper(ctx, subject, rows, &Leaf::Value, &rty, &refs, pre, line)
        };
        let r = self.bind_answer(ctx, t, &rty, true, pre);
        Term::var(&r)
    }

    /// A match through a helper def whose parameter is the scrutinee.
    fn match_helper(&mut self, ctx: &mut FnCtx, subject: &Expr, rows: Vec<Row>, leaf: &Leaf, ret: &Ty, blocks: &[&Block], out: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let s = self.expr(ctx, subject, out);
        let guards: Vec<Expr> = rows.iter().filter_map(|r| r.guard.clone()).collect();
        let grefs: Vec<&Expr> = guards.iter().collect();
        let ins = self.live_ins(ctx, blocks, &grefs);
        let sv = self.fresh("x");
        let sty = self.ty_in(ctx, &subject.ty, line);
        let mut sub = ctx.clone();
        sub.structural = false;
        sub.ret = ret.clone();
        sub.scope = ins.clone();
        sub.bind(&sv, sty.clone(), Some(&subject.ty));
        let body = self.compile_rows(&mut sub, vec![(sv.clone(), subject.ty.clone())], rows, true, leaf, &[], line);
        let mut params = ins.clone();
        params.push((sv, sty));
        let name = self.emit_helper(ctx, "m", params, ret.clone(), body);
        let mut args = self.forward_args(ctx);
        for (n, _) in &ins {
            args.push(Term::var(n));
        }
        args.push(s);
        Term::Call(name, args)
    }

    /// A match as a term: eliminators over thunks.
    fn match_term(&mut self, ctx: &mut FnCtx, subject: &Expr, rows: Vec<Row>, leaf: &Leaf, ret: &Ty, out: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let s = self.expr(ctx, subject, out);
        let sv = self.fresh("x");
        let sty = self.ty_in(ctx, &subject.ty, line);
        out.push(ir::Stmt::Let { name: sv.clone(), reusable: false, ty: Some(sty.clone()), value: s });
        let mut sub = ctx.clone();
        sub.term_mode = true;
        sub.structural = false;
        sub.ret = ret.clone();
        sub.bind(&sv, sty, Some(&subject.ty));
        let body = self.compile_rows(&mut sub, vec![(sv, subject.ty.clone())], rows, false, leaf, &[], line);
        self.body_to_term(&mut sub, body, ret)
    }

    /// Compile rows of patterns over scrutinee columns into a body: a real
    /// Bend match tree when `real`, a term of eliminator calls otherwise.
    /// `sunk` are statements that precede every leaf.
    fn compile_rows(&mut self, ctx: &mut FnCtx, cols: Vec<(String, Type)>, rows: Vec<Row>, real: bool, leaf: &Leaf, sunk: &[ir::Stmt], line: usize) -> Body {
        if rows.is_empty() {
            let msg = Term::Str("match: no arm matched".into());
            let t = match ctx.mode {
                Mode::Io => Term::call("IO.die", vec![Term::TyArg(self.leaf_ty(ctx, leaf)), Term::U32(1), msg]),
                Mode::Result => Term::ctor("Fail", vec![msg]),
                // the checker found the match exhaustive: this leaf is
                // dead, and any value of the type fills it
                Mode::Pure => {
                    let ty = self.leaf_ty(ctx, leaf);
                    self.default_of_ty(&ty, line)
                }
            };
            return self.finish_body(ctx, sunk.to_vec(), Ans::Monadic(t));
        }
        // a column every row binds or ignores: drop it, recording the binds
        if cols.is_empty() {
            let first = rows[0].clone();
            if let Some(g) = first.guard.clone() {
                return self.guarded(ctx, first, g, rows[1..].to_vec(), real, leaf, sunk, line);
            }
            return self.leaf_body(ctx, first, leaf, sunk);
        }
        let all_bind = rows.iter().all(|r| matches!(r.pats[0], Pat::Bind(_) | Pat::Wild));
        if all_bind {
            let (sv, sty) = cols[0].clone();
            let rest_cols: Vec<(String, Type)> = cols[1..].to_vec();
            let rows2: Vec<Row> = rows.into_iter().map(|mut r| {
                let p = r.pats.remove(0);
                if let Pat::Bind(n) = p {
                    r.binds.push((local_name(&n), sv.clone(), sty.clone()));
                }
                r
            }).collect();
            return self.compile_rows(ctx, rest_cols, rows2, real, leaf, sunk, line);
        }
        let (sv, sty) = cols[0].clone();
        let st = self.store.shallow(&sty);
        // literal columns: a chain of picks on equality
        if rows.iter().any(|r| matches!(&r.pats[0], Pat::Lit(l) if !matches!(l, Lit::Bool(_)))) {
            return self.literal_column(ctx, cols, rows, leaf, sunk, line);
        }
        // constructors of the column's type
        let (tid, args): (TypeId, Vec<Type>) = match &st {
            Type::Data(tid, args) => (*tid, args.clone()),
            Type::List(e) => (usize::MAX, vec![(**e).clone()]),
            Type::Bool => (usize::MAX - 1, vec![]),
            _ => {
                self.error(line, "cannot match on a value of this type");
                return self.finish_body(ctx, sunk.to_vec(), Ans::Value(Term::unit()));
            }
        };
        let ctors: Vec<(String, Vec<Type>)> = if tid == usize::MAX {
            vec![("Nil".into(), vec![]), ("Con".into(), vec![args[0].clone(), Type::list(args[0].clone())])]
        } else if tid == usize::MAX - 1 {
            vec![("False".into(), vec![]), ("True".into(), vec![])]
        } else {
            (0..self.core.types[tid].ctors.len()).map(|ci| (self.ctor_name(tid, ci), self.field_types(tid, ci, &args))).collect()
        };
        let mut arms: Vec<(ir::Pat, Body)> = Vec::new();
        let mut elim_thunks: Vec<Term> = Vec::new();
        for (ci, (cname, ftys)) in ctors.iter().enumerate() {
            // fresh binders for the fields
            let binders: Vec<String> = (0..ftys.len()).map(|_| self.fresh("f")).collect();
            let mut sub_rows: Vec<Row> = Vec::new();
            for r in &rows {
                let head = r.pats[0].clone();
                let subs: Option<Vec<Pat>> = match head {
                    Pat::Bind(n) => {
                        let mut r2 = r.clone();
                        r2.binds.push((local_name(&n), sv.clone(), sty.clone()));
                        let mut ps: Vec<Pat> = ftys.iter().map(|_| Pat::Wild).collect();
                        ps.extend(r2.pats[1..].iter().cloned());
                        r2.pats = ps;
                        sub_rows.push(r2);
                        continue;
                    }
                    Pat::Wild => Some(ftys.iter().map(|_| Pat::Wild).collect()),
                    Pat::Lit(Lit::Bool(b)) => {
                        if (b && ci == 1) || (!b && ci == 0) { Some(vec![]) } else { None }
                    }
                    Pat::Con(_, pci, subs) => if pci == ci { Some(subs) } else { None },
                    Pat::List(items, rest) => {
                        if ci == 0 {
                            // Nil: `[]` or `[...rest]`
                            if items.is_empty() {
                                if let Some(Some(n)) = &rest {
                                    let mut r2 = r.clone();
                                    r2.binds.push((local_name(n), sv.clone(), sty.clone()));
                                    r2.pats = r2.pats[1..].to_vec();
                                    sub_rows.push(r2);
                                    continue;
                                }
                                Some(vec![])
                            } else {
                                None
                            }
                        } else if items.is_empty() {
                            // Con: only `[...rest]` (the whole list) matches
                            match rest {
                                Some(Some(n)) => {
                                    let mut r2 = r.clone();
                                    r2.binds.push((local_name(&n), sv.clone(), sty.clone()));
                                    let mut ps: Vec<Pat> = vec![Pat::Wild, Pat::Wild];
                                    ps.extend(r2.pats[1..].iter().cloned());
                                    r2.pats = ps;
                                    sub_rows.push(r2);
                                    continue;
                                }
                                Some(None) => Some(vec![Pat::Wild, Pat::Wild]),
                                None => None,
                            }
                        } else {
                            let head = items[0].clone();
                            let tail = Pat::List(items[1..].to_vec(), rest);
                            let tail = match (&tail, ) {
                                (Pat::List(is, Some(Some(n))),) if is.is_empty() => Pat::Bind(n.clone()),
                                (Pat::List(is, Some(None)),) if is.is_empty() => Pat::Wild,
                                _ => tail,
                            };
                            Some(vec![head, tail])
                        }
                    }
                    Pat::Lit(_) => None,
                };
                if let Some(subs) = subs {
                    let mut r2 = r.clone();
                    let mut ps = subs;
                    ps.extend(r2.pats[1..].iter().cloned());
                    r2.pats = ps;
                    sub_rows.push(r2);
                }
            }
            let mut sub_cols: Vec<(String, Type)> = binders.iter().cloned().zip(ftys.iter().cloned()).collect();
            sub_cols.extend(cols[1..].iter().cloned());
            let mut sub = ctx.clone();
            for (b, t) in binders.iter().zip(ftys.iter()) {
                let bt = self.ty_in(ctx, t, line);
                sub.bind(b, bt, Some(t));
                if ctx.pieces.contains(&sv) {
                    sub.pieces.insert(b.clone());
                }
            }
            let body = self.compile_rows(&mut sub, sub_cols, sub_rows, real, leaf, sunk, line);
            if real {
                arms.push((ir::Pat::Ctor(cname.clone(), binders.iter().map(|b| (b.clone(), false)).collect()), body));
            } else {
                let ret = self.leaf_ty(ctx, leaf);
                let t = self.body_to_term(&mut sub, body, &ret);
                let params = if binders.is_empty() { vec!["_".to_string()] } else { binders.clone() };
                elim_thunks.push(Term::Lam(params, Box::new(t)));
            }
        }
        if real {
            return Body::Match { scrutinee: sv, arms };
        }
        // the eliminator call
        let ret = self.leaf_ty(ctx, leaf);
        let rty = ctx.wrap(ret);
        let call = if tid == usize::MAX {
            let et = self.ty_in(ctx, &args[0], line);
            Term::call("F.list.case", vec![Term::TyArg(et), Term::TyArg(rty), Term::var(&sv), elim_thunks[0].clone(), elim_thunks[1].clone()])
        } else if tid == usize::MAX - 1 {
            let f = Term::Lam(vec!["_".into()], match &elim_thunks[0] { Term::Lam(_, b) => b.clone(), other => Box::new(other.clone()) });
            let t = Term::Lam(vec!["_".into()], match &elim_thunks[1] { Term::Lam(_, b) => b.clone(), other => Box::new(other.clone()) });
            let pick = Term::call("Bool.pick", vec![Term::TyArg(Ty::func(vec![Ty::Unit], rty)), Term::var(&sv), t, f]);
            Term::App(Box::new(pick), vec![Term::unit()])
        } else {
            let name = self.eliminator(tid);
            let mut call_args = self.type_args_of(ctx, &sty, tid, line);
            call_args.push(Term::TyArg(rty));
            call_args.push(Term::var(&sv));
            call_args.extend(elim_thunks);
            Term::Call(name, call_args)
        };
        Body::term(call)
    }

    /// A column of literal patterns: a chain of picks, one per literal in
    /// row order, each continuing with the rows that accept that literal
    /// (the literal itself or a catch-all); values none of them name go on
    /// with the catch-all rows.
    fn literal_column(&mut self, ctx: &mut FnCtx, cols: Vec<(String, Type)>, rows: Vec<Row>, leaf: &Leaf, sunk: &[ir::Stmt], line: usize) -> Body {
        let (sv, sty) = cols[0].clone();
        let ret = self.leaf_ty(ctx, leaf);
        let rty = ctx.wrap(ret.clone());
        let mut lits: Vec<Lit> = Vec::new();
        for r in &rows {
            if let Pat::Lit(l) = &r.pats[0] {
                if !lits.contains(l) {
                    lits.push(l.clone());
                }
            }
        }
        // the rows accepting a value: `Some(l)` a literal, `None` any other
        let accept = |want: Option<&Lit>| -> Vec<Row> {
            rows.iter().filter_map(|r| {
                let mut r2 = r.clone();
                let head = r2.pats.remove(0);
                match head {
                    Pat::Lit(l) => if Some(&l) == want { Some(r2) } else { None },
                    Pat::Bind(n) => {
                        r2.binds.push((local_name(&n), sv.clone(), sty.clone()));
                        Some(r2)
                    }
                    _ => Some(r2),
                }
            }).collect()
        };
        let mut sub = ctx.clone();
        sub.term_mode = true;
        let default_rows = accept(None);
        let default_body = self.compile_rows(&mut sub, cols[1..].to_vec(), default_rows, false, leaf, sunk, line);
        let mut t = self.body_to_term(&mut sub, default_body, &ret);
        for l in lits.iter().rev() {
            let lit = match l {
                Lit::Int(i) => Term::U32(*i as i32 as u32),
                Lit::Float(f) => Term::F32(*f as f32),
                Lit::Str(s) => Term::Str(s.clone()),
                Lit::Bool(b) => Term::boolean(*b),
                Lit::Nothing => Term::unit(),
            };
            let eq = match self.store.shallow(&sty) {
                Type::Int => Term::call("U32.is_eq", vec![Term::var(&sv), lit]),
                Type::Float => Term::call("F32.is_eq", vec![Term::var(&sv), lit]),
                Type::Str => Term::call("String.eq", vec![Term::var(&sv), lit]),
                Type::Bool => Term::call("F.bool.eq", vec![Term::var(&sv), lit]),
                _ => Term::boolean(true),
            };
            let then_body = self.compile_rows(&mut sub, cols[1..].to_vec(), accept(Some(l)), false, leaf, sunk, line);
            let a = self.body_to_term(&mut sub, then_body, &ret);
            t = self.pick_thunks(eq, a, t, rty.clone());
        }
        Body::term(t)
    }

    /// A row with a guard: pick between its body and the remaining rows.
    fn guarded(&mut self, ctx: &mut FnCtx, mut first: Row, guard: Expr, others: Vec<Row>, real: bool, leaf: &Leaf, sunk: &[ir::Stmt], line: usize) -> Body {
        let _ = real;
        first.guard = None;
        let ret = self.leaf_ty(ctx, leaf);
        let rty = ctx.wrap(ret.clone());
        let mut sub = ctx.clone();
        sub.term_mode = true;
        // the binds are in scope for the guard
        let mut pre = Vec::new();
        for (n, from, t) in &first.binds {
            let bt = self.ty_in(&sub, t, line);
            pre.push(ir::Stmt::Let { name: n.clone(), reusable: false, ty: Some(bt.clone()), value: Term::var(from) });
            sub.bind(n, bt, Some(t));
        }
        let mut gpre = Vec::new();
        let g = self.expr(&mut sub, &guard, &mut gpre);
        let then_body = self.leaf_body(&mut sub, first.clone(), leaf, sunk);
        let a = self.body_to_term(&mut sub, then_body, &ret);
        let else_body = self.compile_rows(&mut sub, vec![], others, false, leaf, sunk, line);
        let b = self.body_to_term(&mut sub, else_body, &ret);
        let pick = self.pick_thunks(g, a, b, rty);
        // the guard's binds wrap the pick
        let mut t = pick;
        for s in gpre.into_iter().rev() {
            t = self.stmt_around(&mut sub, s, t, &ret, true);
        }
        for s in pre.into_iter().rev() {
            t = self.stmt_around(&mut sub, s, t, &ret, true);
        }
        Body::term(t)
    }

    /// The body of a matched row: its binds, the sunk statements, its
    /// statements, and the leaf's answer.
    fn leaf_body(&mut self, ctx: &mut FnCtx, row: Row, leaf: &Leaf, sunk: &[ir::Stmt]) -> Body {
        let mut sub = ctx.clone();
        let mut out: Vec<ir::Stmt> = sunk.to_vec();
        for (n, from, t) in &row.binds {
            let bt = self.ty_in(&sub, t, 0);
            out.push(ir::Stmt::Let { name: n.clone(), reusable: false, ty: Some(bt.clone()), value: Term::var(from) });
            sub.bind(n, bt, Some(t));
            if sub.pieces.contains(from) {
                sub.pieces.insert(n.clone());
            }
        }
        let ans = self.lower_stmts_into(&mut sub, &row.body, &mut out, leaf);
        let ans = match ans {
            Some(a) => a,
            None => self.fall_off(&mut sub, leaf, &mut out),
        };
        match ans {
            Ans::Whole(b) => {
                // a nested structural match already holds the sunk statements
                b
            }
            other => self.finish_body(&mut sub, out, other),
        }
    }

    // -- loops ---------------------------------------------------------------------------------------

    /// The list a loop runs over, or the count for a range.
    fn loop_source(&mut self, ctx: &mut FnCtx, iters: &[Iter], out: &mut Vec<ir::Stmt>, line: usize) -> (LoopSource, Type) {
        // one iterable
        if iters.len() == 1 {
            match &iters[0] {
                Iter::Items(e, cid) => {
                    let c = self.store.constraints[*cid].clone();
                    let elem = match &c.class {
                        Class::Iter(t) => t.clone(),
                        _ => Type::Unit,
                    };
                    let subject = self.store.shallow(&c.subject);
                    let forwarded = ctx.dicts.iter().any(|d| d.id == *cid) || matches!(c.solution, Some(Solution::Param(_)));
                    if forwarded {
                        let f = self.dict_term(ctx, *cid, line);
                        let t = self.expr(ctx, e, out);
                        return (LoopSource::List(apply_term(f, vec![t])), elem);
                    }
                    match subject {
                        Type::Data(RANGE, _) => {
                            let t = self.expr(ctx, e, out);
                            return (LoopSource::Range(t), Type::Int);
                        }
                        Type::List(_) => {
                            let t = self.expr(ctx, e, out);
                            return (LoopSource::List(t), elem);
                        }
                        Type::Str => {
                            let t = self.expr(ctx, e, out);
                            return (LoopSource::List(Term::call("F.str.chars", vec![t])), elem);
                        }
                        Type::Map(v) => {
                            let vt = self.ty_in(ctx, &v, line);
                            let t = self.expr(ctx, e, out);
                            return (LoopSource::List(Term::call("F.map.entries", vec![Term::TyArg(vt), t])), elem);
                        }
                        _ => {
                            let t = self.expr(ctx, e, out);
                            return (LoopSource::List(t), elem);
                        }
                    }
                }
                Iter::Counter(_) => unreachable!("checked"),
            }
        }
        // several: zip pairwise, counters enumerate
        let mut acc: Option<(Term, Type)> = None;
        for it in iters {
            let (t, ty) = match it {
                Iter::Counter(start) => {
                    // pairs the next finite source with indices
                    let s = self.expr(ctx, start, out);
                    match acc.take() {
                        None => (Term::var("__counter"), Type::Int),
                        Some((prev, pt)) => {
                            let et = self.ty_in(ctx, &pt, line);
                            let _ = s.clone();
                            (Term::call("F.list.enumerate_from", vec![Term::TyArg(et), prev, s]), Type::pair(Type::Int, pt))
                        }
                    }
                }
                Iter::Items(e, cid) => {
                    let c = self.store.constraints[*cid].clone();
                    let elem = match &c.class {
                        Class::Iter(t) => t.clone(),
                        _ => Type::Unit,
                    };
                    let (src, _) = self.loop_source(ctx, std::slice::from_ref(it), out, line);
                    let list = match src {
                        LoopSource::List(t) => t,
                        LoopSource::Range(r) => Term::call("F.range.to_list", vec![r]),
                    };
                    match acc.take() {
                        None => (list, elem),
                        Some((prev, pt)) => {
                            if let Term::Var(v) = &prev {
                                if v == "__counter" {
                                    // a counter before this source
                                    let et = self.ty_in(ctx, &elem, line);
                                    let start = self.counter_start(ctx, iters, out);
                                    acc = Some((Term::call("F.list.enumerate_from", vec![Term::TyArg(et), list, start]), Type::pair(Type::Int, elem)));
                                    continue;
                                }
                            }
                            let at = self.ty_in(ctx, &pt, line);
                            let bt = self.ty_in(ctx, &elem, line);
                            (Term::call("F.list.zip", vec![Term::TyArg(at), Term::TyArg(bt), prev, list]), Type::pair(pt, elem))
                        }
                    }
                }
            };
            acc = Some((t, ty));
        }
        let (t, ty) = acc.unwrap();
        (LoopSource::List(t), ty)
    }

    fn counter_start(&mut self, ctx: &mut FnCtx, iters: &[Iter], out: &mut Vec<ir::Stmt>) -> Term {
        for it in iters {
            if let Iter::Counter(s) = it {
                return self.expr(ctx, s, out);
            }
        }
        Term::U32(0)
    }

    fn lower_for(&mut self, ctx: &mut FnCtx, patterns: &[Pat], iters: &[Iter], body: &Block, rest: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf, line: usize) -> Option<Ans> {
        let (source, elem_ty) = self.loop_source(ctx, iters, out, line);
        // the element pattern: several iterables nest as pairs
        let pat = if patterns.len() == 1 {
            patterns[0].clone()
        } else {
            let mut ps = patterns.to_vec();
            let mut p = ps.pop().unwrap();
            // counters pair as (index, item)
            while let Some(prev) = ps.pop() {
                p = Pat::Con(PAIR, 0, vec![prev, p]);
            }
            p
        };
        self.lower_loop(ctx, LoopKind::For { source, elem_ty, pat }, body, rest, out, leaf, line)
    }

    fn lower_while(&mut self, ctx: &mut FnCtx, cond: &Expr, body: &Block, rest: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf, line: usize) -> Option<Ans> {
        // the body checks the condition first and breaks when it fails
        let guarded = Block { stmts: vec![Stmt { kind: StmtKind::If { cond: cond.clone(), then: body.clone(), else_: Block { stmts: vec![Stmt { kind: StmtKind::Break, line }] } }, line }] };
        self.lower_loop(ctx, LoopKind::While, &guarded, rest, out, leaf, line)
    }

    fn lower_loop(&mut self, ctx: &mut FnCtx, kind: LoopKind, body: &Block, rest: &[Stmt], out: &mut Vec<ir::Stmt>, leaf: &Leaf, line: usize) -> Option<Ans> {
        // state: variables the body assigns; live-ins: what it reads
        let state = self.live_outs(ctx, &[body]);
        let returns = {
            let mut f = false;
            for_each_stmt(body, &mut |s: &Stmt| {
                if matches!(s.kind, StmtKind::Return(_)) {
                    f = true;
                }
            });
            f
        };
        // a `return` inside carries the def's own result out of every loop
        let def_ret = match &ctx.loop_ {
            Some(l) => l.ret_ty.clone(),
            None => ctx.ret.clone(),
        };
        let ret_ty = if returns { def_ret } else { Ty::Unit };
        let state_tys: Vec<Ty> = state.iter().map(|(_, t)| t.clone()).collect();
        let state_ty = self.pack_ty(&state_tys);
        let ctl_ty = Ty::Named("F.Ctl".into(), vec![state_ty.clone(), ret_ty.clone()]);
        let ins: Vec<(String, Ty)> = self.live_ins(ctx, &[body], &[]).into_iter().filter(|(n, _)| !state.iter().any(|(s, _)| s == n)).collect();
        let in_tys: Vec<Ty> = ins.iter().map(|(_, t)| t.clone()).collect();
        let env_ty = self.pack_ty(&in_tys);
        // the body def
        let (elem_param, elem_bind): (Vec<(String, Ty)>, Vec<Stmt>) = match &kind {
            LoopKind::For { elem_ty, pat, .. } => {
                let et = self.ty_in(ctx, elem_ty, line);
                (vec![("__x".to_string(), et)], vec![])
            }
            LoopKind::While => (vec![], vec![]),
        };
        let _ = elem_bind;
        let mut sub = ctx.clone();
        sub.structural = false;
        sub.term_mode = false;
        sub.scope = ins.clone();
        for (n, t) in &state {
            sub.bind(n, t.clone(), None);
        }
        sub.loop_ = Some(LoopInfo { state: state.clone(), state_ty: state_ty.clone(), ret_ty: ret_ty.clone() });
        sub.ret = ctl_ty.clone();
        let inner = match &kind {
            LoopKind::For { pat, elem_ty, .. } => {
                sub.bind("__x", self.ty_in(ctx, elem_ty, line), Some(elem_ty));
                if let Pat::Bind(n) = pat {
                    // a plain name: rename the parameter
                    let row = Row { pats: vec![], guard: None, body: body.stmts.clone(), binds: vec![(local_name(n), "__x".into(), elem_ty.clone())] };
                    self.leaf_body(&mut sub, row, &Leaf::Result, &[])
                } else {
                    let rows = vec![Row { pats: vec![pat.clone()], guard: None, body: body.stmts.clone(), binds: vec![] }];
                    self.compile_rows(&mut sub, vec![("__x".into(), elem_ty.clone())], rows, true, &Leaf::Result, &[], line)
                }
            }
            LoopKind::While => self.lower_block_body(&mut sub, &body.stmts, Leaf::Result),
        };
        let mut params: Vec<(String, Ty)> = ins.clone();
        params.extend(state.iter().cloned());
        params.extend(elem_param.clone());
        let body_name = self.emit_helper(ctx, "loop", params, ctl_ty.clone(), inner);
        // the template code: unpack env and state, call the body def
        let mut call_args = self.forward_args(ctx);
        for (i, _) in ins.iter().enumerate() {
            let v = self.unpack(Term::var("__e"), &in_tys, i);
            call_args.push(v);
        }
        for (i, _) in state.iter().enumerate() {
            let v = self.unpack(Term::var("__s"), &state_tys, i);
            call_args.push(v);
        }
        if !elem_param.is_empty() {
            call_args.push(Term::var("__x"));
        }
        let mut lam_params = vec!["+__e".to_string(), "+__s".to_string()];
        if !elem_param.is_empty() {
            lam_params.push("__x".into());
        }
        let code = Term::Lam(lam_params, Box::new(Term::Call(body_name, call_args)));
        let env_terms: Vec<Term> = ins.iter().map(|(n, _)| Term::var(n)).collect();
        let env = self.pack(env_terms, &in_tys);
        let s0_terms: Vec<Term> = state.iter().map(|(n, _)| Term::var(n)).collect();
        let s0 = self.pack(s0_terms, &state_tys);
        let suffix = match ctx.mode {
            Mode::Pure => "",
            Mode::Result => "_res",
            Mode::Io => "_io",
        };
        let call = match &kind {
            LoopKind::For { source: LoopSource::List(xs), elem_ty, .. } => {
                let et = self.ty_in(ctx, elem_ty, line);
                Term::Call(format!("F.for_list{}", suffix), vec![Term::TmplTy(state_ty.clone()), Term::TmplTy(ret_ty.clone()), Term::TmplTy(et), Term::TmplTy(env_ty.clone()), tmpl_arg(code), env, xs.clone(), Term::ctor("F.Next", vec![s0.clone()])])
            }
            LoopKind::For { source: LoopSource::Range(r), .. } => {
                Term::Call(format!("F.for_range{}", suffix), vec![Term::TmplTy(state_ty.clone()), Term::TmplTy(ret_ty.clone()), Term::TmplTy(env_ty.clone()), tmpl_arg(code), env, r.clone(), Term::ctor("F.Next", vec![s0.clone()])])
            }
            LoopKind::While => Term::Call(format!("F.loop{}", suffix), vec![Term::TmplTy(state_ty.clone()), Term::TmplTy(ret_ty.clone()), Term::TmplTy(env_ty.clone()), tmpl_arg(code), env, Term::ctor("F.Next", vec![s0.clone()])]),
        };
        let c = self.bind_answer(ctx, call, &ctl_ty, true, out);
        if returns {
            // Return{v} leaves the block; the state continues with the rest
            let ret_inner = self.leaf_ty(ctx, leaf);
            let ret_term = {
                let mut sub = ctx.clone();
                sub.term_mode = true;
                let ans = if ctx.loop_.is_some() { Ans::Value(Term::ctor("F.Return", vec![Term::var("__r")])) } else { Ans::Value(Term::var("__r")) };
                let b = self.finish_body(&mut sub, vec![], ans);
                self.body_to_term(&mut sub, b, &ret_inner)
            };
            let cont = {
                let mut sub = ctx.clone();
                sub.term_mode = true;
                sub.structural = false;
                let mut pre = Vec::new();
                sub.bind("__s", state_ty.clone(), None);
                self.unpack_into(&mut sub, "__s", &state, &mut pre);
                let ans = self.lower_stmts_into(&mut sub, rest, &mut pre, leaf);
                let ans = match ans {
                    Some(a) => a,
                    None => self.fall_off(&mut sub, leaf, &mut pre),
                };
                let b = self.finish_body(&mut sub, pre, ans);
                self.body_to_term(&mut sub, b, &ret_inner)
            };
            let t = Term::call("F.ctl.case", vec![Term::TyArg(state_ty), Term::TyArg(ret_ty), Term::TyArg(ctx.wrap(ret_inner)), Term::var(&c), Term::Lam(vec!["__r".into()], Box::new(ret_term)), Term::Lam(vec!["__s".into()], Box::new(cont))]);
            return Some(Ans::Monadic(t));
        }
        if !state.is_empty() {
            let s = self.fresh("s");
            let st = Term::call("F.ctl.state", vec![Term::TyArg(state_ty.clone()), Term::TyArg(ret_ty), Term::var(&c), s0]);
            out.push(ir::Stmt::Let { name: s.clone(), reusable: false, ty: Some(state_ty.clone()), value: st });
            self.unpack_into(ctx, &s, &state, out);
        }
        None
    }
}

/// A row of the match compiler: the remaining patterns (one per column),
/// a guard, the arm's statements, and the binds made so far (name, from,
/// type).
#[derive(Clone)]
pub struct Row {
    pub pats: Vec<Pat>,
    pub guard: Option<Expr>,
    pub body: Vec<Stmt>,
    pub binds: Vec<(String, String, Type)>,
}

pub enum LoopSource {
    List(Term),
    Range(Term),
}

pub enum LoopKind {
    For { source: LoopSource, elem_ty: Type, pat: Pat },
    While,
}

/// An arm's body as statements: a block's statements, or the expression.
fn arm_block(a: &Arm) -> Vec<Stmt> {
    match &a.body.kind {
        ExprKind::Block(b) => b.stmts.clone(),
        _ => vec![Stmt { kind: StmtKind::Expr(a.body.clone()), line: a.line }],
    }
}
