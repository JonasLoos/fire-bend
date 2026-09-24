// src/lower/expr.rs
// Expressions: Core -> Bend terms. A monadic sub-expression (a call of a
// def with effects, an abort) is bound to a temporary in the enclosing
// do-block; everything else is a term. Also the builtin table, the
// implementations of solved constraints, closure values and calls.

use super::body::{FnCtx, Leaf};
use super::*;

/// A function value ready to be called or passed as code plus environment.
pub struct FnVal {
    /// A closed term usable as a `~` argument: `~f` or `~(e => x => ...)`.
    pub code: Term,
    pub env: Term,
    pub env_ty: Ty,
    pub mode: Mode,
}

impl<'a> Lower<'a> {
    /// Lower an expression to a term. Monadic pieces are bound in `pre`
    /// (statements to run before the term), which needs a do-block.
    pub fn expr(&mut self, ctx: &mut FnCtx, e: &Expr, pre: &mut Vec<ir::Stmt>) -> Term {
        let line = e.line;
        match &e.kind {
            ExprKind::Var(v) => {
                if let Some(FnParamKind::Template { env, .. }) = ctx.template_param(v) {
                    // a template function parameter used as a value: its environment
                    return Term::Var(env);
                }
                Term::var(&local_name(v))
            }
            ExprKind::Lit(l) => match l {
                Lit::Int(i) => Term::U32(*i as i32 as u32),
                Lit::Float(f) => Term::F32(*f as f32),
                Lit::Str(s) => Term::Str(s.clone()),
                Lit::Bool(b) => Term::boolean(*b),
                Lit::Nothing => Term::unit(),
            },
            ExprKind::List(items) => {
                let ts: Vec<Term> = items.iter().map(|i| self.expr(ctx, i, pre)).collect();
                Term::List(ts)
            }
            ExprKind::EmptyMap => {
                let vt = match self.store.shallow(&e.ty) {
                    Type::Map(v) => self.ty_in(ctx, &v, line),
                    _ => Ty::Unit,
                };
                Term::call("Map.new", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(vt)])
            }
            ExprKind::Con(tid, ci, args) => {
                let ts: Vec<Term> = args.iter().map(|a| self.expr(ctx, a, pre)).collect();
                Term::Ctor(self.ctor_name(*tid, *ci), ts)
            }
            ExprKind::Field(obj, tid, idx) => {
                let o = self.expr(ctx, obj, pre);
                let g = self.getter(*tid, *idx);
                let mut args = self.type_args_of(ctx, &obj.ty, *tid, line);
                args.push(o);
                Term::Call(g, args)
            }
            ExprKind::SetField(obj, tid, idx, v) => {
                let o = self.expr(ctx, obj, pre);
                let val = self.expr(ctx, v, pre);
                let s = self.setter(*tid, *idx);
                let mut args = self.type_args_of(ctx, &obj.ty, *tid, line);
                args.push(o);
                args.push(val);
                Term::Call(s, args)
            }
            ExprKind::Call { def, targs, dicts, args } => self.lower_call(ctx, *def, targs, dicts, args, &e.ty, pre, line),
            ExprKind::CallClosure(f, args) => {
                let fv = self.fn_value(ctx, f, pre);
                let ts: Vec<Term> = args.iter().map(|a| self.expr(ctx, a, pre)).collect();
                let mut call_args = vec![fv.env];
                call_args.extend(ts);
                let t = apply_term(fv.code, call_args);
                let rty = self.ty_in(ctx, &e.ty, line);
                self.bind_monadic(ctx, t, fv.mode, &rty, pre, line)
            }
            ExprKind::Dict { id, args } => self.lower_dict_call(ctx, *id, args, &e.ty, pre, line),
            ExprKind::Lambda(d) => self.closure_value(ctx, *d, &e.ty, line),
            ExprKind::DefRef { def, .. } => self.def_as_value(*def, &e.ty, line),
            ExprKind::Builtin(name, args) => self.lower_builtin(ctx, name, args, &e.ty, pre, line),
            ExprKind::If(c, t, el) => {
                let cond = self.expr(ctx, c, pre);
                let rty = self.ty_in(ctx, &e.ty, line);
                // both branches cheap and pure: an eager pick
                if self.is_cheap(t) && self.is_cheap(el) {
                    let a = self.expr(ctx, t, pre);
                    let b = self.expr(ctx, el, pre);
                    return Term::call("Bool.pick", vec![Term::TyArg(rty), cond, a, b]);
                }
                let mode = ctx.mode;
                let a = self.expr_as_term(ctx, t, mode);
                let b = self.expr_as_term(ctx, el, mode);
                let t = self.pick_thunks(cond, a, b, mode.wrap(rty.clone()));
                self.bind_monadic(ctx, t, mode, &rty, pre, line)
            }
            ExprKind::Match(subject, arms) => self.lower_match_expr(ctx, subject, arms, &e.ty, pre, line),
            ExprKind::Block(b) => {
                // the statements run before the value
                let mut block = b.clone();
                let last = block.stmts.pop();
                self.lower_stmts_into(ctx, &block.stmts, pre, &Leaf::Result);
                match last {
                    Some(Stmt { kind: StmtKind::Expr(v), .. }) => self.expr(ctx, &v, pre),
                    Some(other) => {
                        self.lower_stmts_into(ctx, &[other], pre, &Leaf::Result);
                        Term::unit()
                    }
                    None => Term::unit(),
                }
            }
            ExprKind::And(a, b) => {
                let x = self.expr(ctx, a, pre);
                if self.is_pure_expr(b) {
                    let y = self.expr(ctx, b, pre);
                    return Term::And(Box::new(x), Box::new(y));
                }
                let mode = ctx.mode;
                let y = self.expr_as_term(ctx, b, mode);
                let f = self.lift_mode(Term::boolean(false), Mode::Pure, mode, &Ty::Bool);
                let t = self.pick_thunks(x, y, f, mode.wrap(Ty::Bool));
                self.bind_monadic(ctx, t, mode, &Ty::Bool, pre, line)
            }
            ExprKind::Or(a, b) => {
                let x = self.expr(ctx, a, pre);
                if self.is_pure_expr(b) {
                    let y = self.expr(ctx, b, pre);
                    return Term::Or(Box::new(x), Box::new(y));
                }
                let mode = ctx.mode;
                let y = self.expr_as_term(ctx, b, mode);
                let t_ = self.lift_mode(Term::boolean(true), Mode::Pure, mode, &Ty::Bool);
                let t = self.pick_thunks(x, t_, y, mode.wrap(Ty::Bool));
                self.bind_monadic(ctx, t, mode, &Ty::Bool, pre, line)
            }
            ExprKind::Not(x) => {
                let t = self.expr(ctx, x, pre);
                Term::call("Bool.not", vec![t])
            }
            ExprKind::Abort(msg) => {
                let m = self.expr(ctx, msg, pre);
                let m = if line == 0 { m } else { Term::cat(Term::Str(format!("line {}: ", line)), m) };
                let rty = self.ty_in(ctx, &e.ty, line);
                match ctx.mode {
                    Mode::Io => {
                        let t = Term::call("IO.die", vec![Term::TyArg(rty.clone()), Term::U32(1), m]);
                        self.bind_monadic(ctx, t, Mode::Io, &rty, pre, line)
                    }
                    _ => {
                        let t = Term::ctor("Fail", vec![m]);
                        self.bind_monadic(ctx, t, Mode::Result, &rty, pre, line)
                    }
                }
            }
            ExprKind::FString(parts) => {
                let pieces: Vec<Term> = parts.iter().map(|p| match p {
                    FPart::Text(t) => Term::Str(t.clone()),
                    FPart::Expr(x, spec) => {
                        let s = self.expr(ctx, x, pre);
                        match spec {
                            Some(pad) => self.pad(s, pad),
                            None => s,
                        }
                    }
                }).collect();
                pieces.into_iter().reduce(Term::cat).unwrap_or(Term::Str(String::new()))
            }
            ExprKind::SelfValue(tid) => {
                let t = self.core.types[*tid].clone();
                let args: Vec<Term> = t.ctors[0].fields.iter().map(|f| Term::var(&local_name(&f.name))).collect();
                Term::Ctor(self.ctor_name(*tid, 0), args)
            }
        }
    }

    /// A Fire type in the current def's naming.
    pub fn ty_in(&mut self, ctx: &FnCtx, t: &Type, line: usize) -> Ty {
        let names = ctx.tparams.clone();
        self.ty(t, &names, line)
    }

    /// The type arguments of a data type occurrence, as erased arguments.
    pub fn type_args_of(&mut self, ctx: &FnCtx, t: &Type, tid: TypeId, line: usize) -> Vec<Term> {
        let args = match self.store.shallow(t) {
            Type::Data(_, a) => a,
            _ => vec![],
        };
        self.eff_actuals(tid, &args).iter().map(|a| Term::TyArg(self.ty_in(ctx, a, line))).collect()
    }

    /// The element type of a list type (`Unit` for anything else).
    fn list_elem_ty(&mut self, ctx: &FnCtx, t: &Type, line: usize) -> Ty {
        match self.store.shallow(t) {
            Type::List(e) => self.ty_in(ctx, &e, line),
            _ => Ty::Unit,
        }
    }

    /// Bind an operation that may fail right here (an index, a conversion,
    /// an unwrap): its failure names the source line.
    pub fn bind_failing(&mut self, ctx: &mut FnCtx, t: Term, ty: &Ty, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let t = if line == 0 { t } else { Term::call("F.at", vec![Term::TyArg(ty.clone()), Term::Str(format!("line {}: ", line)), t]) };
        self.bind_monadic(ctx, t, Mode::Result, ty, pre, line)
    }

    /// Bind a term of mode `mode` to a temporary when it is monadic,
    /// lifting it into the def's mode; a pure term is returned as is.
    pub fn bind_monadic(&mut self, ctx: &mut FnCtx, t: Term, mode: Mode, ty: &Ty, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        if mode == Mode::Pure {
            return t;
        }
        if ctx.mode == Mode::Pure {
            self.error(line, "internal: an effect inside a pure def");
            return t;
        }
        let lifted = self.lift_mode(t, mode, ctx.mode, ty);
        let tmp = self.fresh("t");
        pre.push(ir::Stmt::Bind { name: tmp.clone(), reusable: false, ty: ty.clone(), value: lifted });
        Term::var(&tmp)
    }

    /// Whether an expression is a cheap, pure, total term (a variable, a
    /// literal, a constructor of such), safe to evaluate eagerly.
    pub fn is_cheap(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::SelfValue(_) => true,
            ExprKind::List(items) | ExprKind::Con(_, _, items) => items.iter().all(|i| self.is_cheap(i)),
            ExprKind::Not(x) => self.is_cheap(x),
            ExprKind::Field(o, _, _) => self.is_cheap(o),
            _ => false,
        }
    }

    /// Whether lowering an expression produces no binds and no self-calls.
    pub fn is_pure_expr(&self, e: &Expr) -> bool {
        let mut pure = true;
        walk_expr(e, &mut |x: &Expr| match &x.kind {
            ExprKind::Call { def, .. } => {
                if !self.core.defs[*def].effect.is_pure() {
                    pure = false;
                }
            }
            ExprKind::CallClosure(f, _) => {
                if let Type::Fn(_, _, c) = self.store.shallow(&f.ty)
                    && self.closure_mode(c) != Mode::Pure {
                        pure = false;
                    }
            }
            ExprKind::Dict { id, .. } => {
                if self.dict_mode(*id) != Mode::Pure {
                    pure = false;
                }
            }
            ExprKind::Builtin(name, _) => {
                if builtin_mode(name) != Mode::Pure {
                    pure = false;
                }
            }
            ExprKind::Abort(_) => pure = false,
            ExprKind::Block(_) | ExprKind::Match(..) => pure = false,
            _ => {}
        });
        pure
    }

    /// Whether an expression contains a call of the def being lowered.
    pub fn has_self_call(&self, ctx: &FnCtx, e: &Expr) -> bool {
        let mut found = false;
        let me = ctx.self_def;
        walk_expr(e, &mut |x: &Expr| {
            if let ExprKind::Call { def, .. } = &x.kind
                && *def == me {
                    found = true;
                }
        });
        found
    }

    // -- calls --------------------------------------------------------------------------------

    fn lower_call(&mut self, ctx: &mut FnCtx, d: DefId, targs: &[Type], dicts: &[ConstraintId], args: &[Expr], ret_ty: &Type, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let img = self.images[d].clone().unwrap();
        let def = self.core.defs[d].clone();
        let recursive = d == ctx.self_def || (targs.is_empty() && !img.tparams.is_empty());
        // type arguments
        let mut call_args: Vec<Term> = Vec::new();
        let type_terms: Vec<Ty> = if recursive || targs.len() != img.tparams.len() {
            img.tparams.iter().map(|(_, n)| Ty::Param(n.clone())).collect()
        } else {
            targs.iter().map(|t| self.ty_in(ctx, t, line)).collect()
        };
        // template types: the def's own, then the env types of its template fn params
        let mut fn_vals: Vec<Option<FnVal>> = Vec::new();
        for (i, a) in args.iter().enumerate() {
            match img.fnp.get(i) {
                Some(FnParamKind::Template { .. }) => fn_vals.push(Some(self.fn_value(ctx, a, pre))),
                _ => fn_vals.push(None),
            }
        }
        if img.template {
            for t in &type_terms {
                call_args.push(Term::TmplTy(t.clone()));
            }
        }
        for fv in fn_vals.iter().flatten() {
            call_args.push(Term::TmplTy(fv.env_ty.clone()));
        }
        // dictionaries
        if recursive {
            for dp in &img.dicts {
                call_args.push(Term::TmplRef(dp.name.clone()));
            }
        } else {
            let ds = self.dict_args(ctx, &img, dicts, line);
            call_args.extend(ds);
        }
        // template function codes
        for fv in fn_vals.iter().flatten() {
            call_args.push(tmpl_arg(fv.code.clone()));
        }
        // erased types
        if !img.template {
            for t in &type_terms {
                call_args.push(Term::TyArg(t.clone()));
            }
        }
        // fuel
        if img.fuel
            && let Descent::Fuel(i) = def.descent {
                if d == ctx.self_def {
                    call_args.push(Term::var("__fuel_"));
                } else {
                    let p = self.expr(ctx, &args[i], pre);
                    call_args.push(Term::call("F.i32.fuel", vec![p]));
                }
            }
        // environment: the captured locals, which the caller has too
        if img.env.is_some() {
            let e = self.env_record(ctx, d);
            call_args.push(e);
        }
        // values in image order
        let mut value_terms: Vec<Option<Term>> = args.iter().map(|_| None).collect();
        for (i, a) in args.iter().enumerate() {
            match img.fnp.get(i) {
                Some(FnParamKind::Template { .. }) => {}
                _ => value_terms[i] = Some(self.expr(ctx, a, pre)),
            }
        }
        for &i in &img.order {
            match img.fnp.get(i) {
                Some(FnParamKind::Template { .. }) => call_args.push(fn_vals[i].as_ref().unwrap().env.clone()),
                _ => call_args.push(value_terms[i].take().unwrap_or(Term::unit())),
            }
        }
        let t = Term::Call(img.name.clone(), call_args);
        let rty = self.ty_in(ctx, ret_ty, line);
        // a recursive call's mode is the def's own mode
        self.bind_monadic(ctx, t, img.mode, &rty, pre, line)
    }

    /// A function-typed expression as code plus environment.
    pub fn fn_value(&mut self, ctx: &mut FnCtx, e: &Expr, pre: &mut Vec<ir::Stmt>) -> FnVal {
        let line = e.line;
        match &e.kind {
            ExprKind::Var(v) => {
                if let Some(FnParamKind::Template { code, env_ty, env }) = ctx.template_param(v) {
                    let mode = match self.store.shallow(&e.ty) {
                        Type::Fn(_, _, c) => self.closure_mode(c),
                        _ => Mode::Pure,
                    };
                    return FnVal { code: Term::TmplRef(code), env: Term::var(&env), env_ty: Ty::Param(env_ty), mode };
                }
            }
            ExprKind::Lambda(d) => return self.lambda_fn_value(ctx, *d, Some(&e.ty), line),
            ExprKind::DefRef { def, targs, dicts } => return self.defref_fn_value(ctx, *def, targs, dicts, line),
            _ => {}
        }
        // a value of a closure type: its representation decides the code
        let t = self.expr(ctx, e, pre);
        let (set, mode) = match self.store.shallow(&e.ty) {
            Type::Fn(_, _, c) => (self.store.clos_set(c).into_iter().collect::<Vec<_>>(), self.closure_mode(c)),
            _ => (vec![], Mode::Pure),
        };
        let env_ty = self.ty_in(ctx, &e.ty, line);
        match set.len() {
            0 => FnVal { code: Term::TmplRef("F.never".into()), env: t, env_ty, mode },
            1 => {
                let fv = self.lambda_fn_value(ctx, set[0], Some(&e.ty), line);
                FnVal { code: fv.code, env: t, env_ty, mode }
            }
            _ => {
                let name = self.sum_type(&set, line);
                FnVal { code: Term::TmplRef(format!("{}.call", name)), env: t, env_ty, mode }
            }
        }
    }

    /// The code and environment of a lambda (or nested def): inside its unit
    /// the code forwards the unit's template parameters; elsewhere (a
    /// closure value that left its def) they are fixed by the type at the
    /// use site.
    fn lambda_fn_value(&mut self, ctx: &mut FnCtx, d: DefId, use_ty: Option<&Type>, line: usize) -> FnVal {
        let img = self.images[d].clone().unwrap();
        let def = self.core.defs[d].clone();
        let env_ty = self.env_ty(d, use_ty, &ctx.tparams.clone(), line);
        let env = self.env_record(ctx, d);
        let code = if ctx.unit == def.unit { self.code_term(ctx, &img, &def) } else { self.code_term_at(ctx, &img, &def, use_ty, line) };
        FnVal { code, env, env_ty, mode: img.mode }
    }

    /// The environment record of a def with captures, from the locals in
    /// scope (a captured template function parameter contributes its
    /// environment).
    pub fn env_record(&mut self, ctx: &FnCtx, d: DefId) -> Term {
        let def = self.core.defs[d].clone();
        if def.captures.is_empty() {
            return Term::unit();
        }
        let fields: Vec<Term> = def.captures.iter().map(|(n, _)| match ctx.template_param(n) {
            Some(FnParamKind::Template { env, .. }) => Term::var(&env),
            _ => Term::var(&local_name(n)),
        }).collect();
        Term::Ctor(format!("F.Env.{}", self.def_names[d]), fields)
    }

    /// The code term of a closure outside its unit: the unit's type
    /// parameters and dictionaries come from the use-site type.
    fn code_term_at(&mut self, ctx: &mut FnCtx, img: &Image, def: &Def, use_ty: Option<&Type>, line: usize) -> Term {
        let bindings = self.closure_bindings(def.id, use_ty);
        let unit_img = self.images[img.unit].clone().unwrap();
        let mut type_terms = Vec::new();
        for (v, _) in &unit_img.tparams {
            let t = bindings.get(v).cloned().unwrap_or(Type::Unit);
            type_terms.push(self.ty_in(ctx, &t, line));
        }
        if unit_img.fnp.iter().any(|k| matches!(k, FnParamKind::Template { .. })) {
            self.error(line, format!("a function value made inside {} cannot be called outside it, because {} takes a function as a template; pass the function on instead", self.core.defs[img.unit].name, self.core.defs[img.unit].name));
        }
        let subst: Vec<(TVar, Type)> = bindings.iter().map(|(v, t)| (*v, t.clone())).collect();
        let mut dict_terms = Vec::new();
        for dp in &img.dicts {
            let c = self.store.constraints[dp.id].clone();
            let class = self.store.substitute_class(&c.class, &subst);
            let subject = self.store.substitute(&c.subject, &subst);
            let t = self.dict_for(ctx, class, subject, line);
            dict_terms.push(tmpl_arg(t));
        }
        let args = image_prefix(img, &type_terms, dict_terms);
        self.code_lambda(img, def.id, args)
    }

    /// `~(e => x => name(<forwarded template args>, e, x))`: the closed
    /// code term of a def, forwarding the current def's template
    /// parameters (the same unit's).
    fn code_term(&mut self, ctx: &FnCtx, img: &Image, def: &Def) -> Term {
        let args = self.forward_args(ctx);
        self.code_lambda(img, def.id, args)
    }

    /// `__e => __a0 => .. => name(args, __e, __a0, ..)`: the code of a def
    /// as a lambda over its environment and its values (a def without
    /// captures ignores the environment). A def counting down an int
    /// starts its fuel in a forwarder: the code is inlined where it is
    /// called, so it may use each argument once.
    fn code_lambda(&mut self, img: &Image, d: DefId, mut args: Vec<Term>) -> Term {
        let params: Vec<String> = (0..self.core.defs[d].params.len()).map(|i| format!("__a{}", i)).collect();
        let callee = if img.fuel { self.fuel_entry(d) } else { img.name.clone() };
        if img.env.is_some() {
            args.push(Term::var("__e"));
        }
        for &i in &img.order {
            args.push(Term::var(&params[i]));
        }
        let mut lam_params = vec!["__e".to_string()];
        lam_params.extend(params);
        Term::Lam(lam_params, Box::new(Term::Call(callee, args)))
    }

    /// The dictionary arguments of a call of an image, from the call's
    /// solved constraints.
    fn dict_args(&mut self, ctx: &FnCtx, img: &Image, dicts: &[ConstraintId], line: usize) -> Vec<Term> {
        (0..img.dicts.len()).map(|k| match dicts.get(k) {
            Some(cid) => tmpl_arg(self.dict_term(ctx, *cid, line)),
            None => tmpl_arg(Term::unit()),
        }).collect()
    }

    /// A top-level def used as a value.
    fn defref_fn_value(&mut self, ctx: &mut FnCtx, d: DefId, targs: &[Type], dicts: &[ConstraintId], line: usize) -> FnVal {
        let img = self.images[d].clone().unwrap();
        if img.fnp.iter().any(|k| matches!(k, FnParamKind::Template { .. })) {
            self.error(line, format!("{} takes a function as a template and cannot be used as a value; wrap it in a lambda", self.core.defs[d].name));
        }
        let type_terms: Vec<Ty> = targs.iter().map(|t| self.ty_in(ctx, t, line)).collect();
        let dict_terms = self.dict_args(ctx, &img, dicts, line);
        let args = image_prefix(&img, &type_terms, dict_terms);
        let code = self.code_lambda(&img, d, args);
        let env = self.env_record(ctx, d);
        let env_ty = self.env_ty(d, None, &ctx.tparams.clone(), line);
        FnVal { code, env, env_ty, mode: img.mode }
    }

    /// A closure as a value: its environment record, wrapped in the sum
    /// constructor when several closures share the type.
    fn closure_value(&mut self, ctx: &mut FnCtx, d: DefId, ty: &Type, line: usize) -> Term {
        let fv = self.lambda_fn_value(ctx, d, Some(ty), line);
        self.wrap_in_sum(fv.env, d, ty, line)
    }

    /// A top-level def stored as a value (in a list, a record, a variable
    /// that several functions flow into): its environment in the sum. The
    /// sum's `call` def calls it without type arguments, so a def that
    /// needs operations on its types cannot be stored this way.
    fn def_as_value(&mut self, d: DefId, ty: &Type, line: usize) -> Term {
        let img = self.images[d].clone().unwrap();
        if img.template {
            let name = self.core.defs[d].name.clone();
            self.error(line, format!("{} is generic in operations its callers supply and cannot be stored as a value; store a lambda that calls it (`x => {}(x)`)", name, name));
        }
        self.wrap_in_sum(Term::unit(), d, ty, line)
    }

    fn wrap_in_sum(&mut self, env: Term, d: DefId, ty: &Type, line: usize) -> Term {
        let set: Vec<DefId> = match self.store.shallow(ty) {
            Type::Fn(_, _, c) => self.store.clos_set(c).into_iter().collect(),
            _ => vec![],
        };
        if set.len() > 1 {
            let name = self.sum_type(&set, line);
            return Term::Ctor(format!("{}.{}", name, self.def_names[d].replace('.', "_")), vec![env]);
        }
        env
    }

    // -- dictionaries ----------------------------------------------------------------------------

    /// The mode of what a constraint's operation does at this use.
    pub fn dict_mode(&self, id: ConstraintId) -> Mode {
        let c = &self.store.constraints[id];
        match &c.solution {
            Some(Solution::Method(m, _, _)) => Mode::of(self.core.defs[*m].effect),
            Some(Solution::Concrete(_)) => {
                let subject = self.store.shallow(&c.subject);
                match (&c.class, &subject) {
                    (Class::Index(..), Type::List(_) | Type::Str | Type::Data(RANGE, _)) => Mode::Result,
                    (Class::IndexSet(..), Type::List(_)) => Mode::Result,
                    (Class::Method(n, _, _), Type::Str) if matches!(n.as_str(), "to_int" | "to_float") => Mode::Result,
                    // `reduce` with no initial value fails on an empty list
                    (Class::Method(n, a, _), Type::List(_)) if matches!(n.as_str(), "min" | "max" | "pop") || (n == "reduce" && a.len() == 1) => Mode::Result,
                    (Class::Method(n, _, _), Type::Data(RANGE, _)) if matches!(n.as_str(), "min" | "max" | "first" | "last") => Mode::Result,
                    (Class::Convert(_, _), Type::Str) => Mode::Result,
                    _ => Mode::Pure,
                }
            }
            Some(Solution::Param(_)) | None => {
                // a forwarded dictionary answers a result for a fallible class
                if c.class.fallible() { Mode::Result } else { Mode::Pure }
            }
            Some(Solution::Field(..)) => Mode::Pure,
        }
    }

    /// Apply a constraint's operation to arguments.
    fn lower_dict_call(&mut self, ctx: &mut FnCtx, id: ConstraintId, args: &[Expr], ret_ty: &Type, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let c = self.store.constraints[id].clone();
        // a forwarded dictionary parameter: call it; its answer is in the
        // shape the parameter type promises (result for fallible classes)
        let forwarded = ctx.dicts.iter().any(|d| d.id == id) || matches!(c.solution, Some(Solution::Param(_)));
        // higher-order builtin methods take their function as code plus environment
        let hof = matches!(&c.class, Class::Method(n, _, _) if is_hof_method(n));
        let mut terms: Vec<Term> = Vec::new();
        let mut fnvals: Vec<FnVal> = Vec::new();
        for (i, a) in args.iter().enumerate() {
            if i > 0 && hof && matches!(self.store.shallow(&a.ty), Type::Fn(..)) {
                fnvals.push(self.fn_value(ctx, a, pre));
            } else {
                terms.push(self.expr(ctx, a, pre));
            }
        }
        let rty = self.ty_in(ctx, ret_ty, line);
        if forwarded {
            let f = self.dict_term(ctx, id, line);
            let t = apply_term(f, terms);
            if c.class.fallible() {
                return self.bind_failing(ctx, t, &rty, pre, line);
            }
            return t;
        }
        let mut mode = self.dict_mode(id);
        let t = match c.solution.clone() {
            Some(Solution::Method(m, targs, dicts)) => {
                // a class method through a constraint: a direct call
                return self.lower_call(ctx, m, &targs, &dicts, args, ret_ty, pre, line);
            }
            Some(Solution::Field(path)) => match &c.class {
                Class::Field(..) => {
                    let o = terms.remove(0);
                    self.field_path_get(ctx, &path, &args[0].ty, o, line)
                }
                _ => {
                    let v = terms.pop().unwrap_or(Term::unit());
                    let o = terms.remove(0);
                    self.field_path_set(ctx, &path, &args[0].ty, o, v, line)
                }
            },
            Some(Solution::Concrete(subs)) => {
                let (t, m) = self.concrete_op(ctx, id, &subs, terms, fnvals, line);
                mode = m;
                t
            }
            _ => {
                self.error(line, format!("unresolved operation: {}", crate::check::describe_class(&c.class)));
                Term::unit()
            }
        };
        // a builtin operation that fails here (an index, a conversion); a
        // callback that fails names its own line
        if mode == Mode::Result && self.dict_mode(id) == Mode::Result {
            return self.bind_failing(ctx, t, &rty, pre, line);
        }
        self.bind_monadic(ctx, t, mode, &rty, pre, line)
    }

    /// The implementation of a class method as a dictionary term.
    pub fn method_dict(&mut self, ctx: &FnCtx, m: DefId, targs: &[Type], dicts: &[ConstraintId], line: usize) -> Term {
        let img = self.images[m].clone().unwrap();
        let params: Vec<String> = (0..self.core.defs[m].params.len()).map(|i| format!("__a{}", i)).collect();
        let type_terms: Vec<Ty> = targs.iter().map(|t| self.ty(t, &ctx.tparams.clone(), line)).collect();
        let dict_terms = self.dict_args(ctx, &img, dicts, line);
        let mut args = image_prefix(&img, &type_terms, dict_terms);
        for &i in &img.order {
            args.push(Term::var(&params[i]));
        }
        let body = Term::Call(img.name.clone(), args);
        // the dictionary shape answers a result
        let body = match img.mode {
            Mode::Pure => Term::ctor("Done", vec![body]),
            _ => body,
        };
        Term::Lam(params, Box::new(body))
    }

    pub fn field_dict(&mut self, path: &[(TypeId, usize)], c: &Constraint, ctx: &FnCtx, line: usize) -> Term {
        let body = self.field_path_get(ctx, path, &c.subject.clone(), Term::var("__x"), line);
        Term::Lam(vec!["__x".into()], Box::new(body))
    }

    pub fn set_field_dict(&mut self, path: &[(TypeId, usize)], c: &Constraint, ctx: &FnCtx, line: usize) -> Term {
        let body = self.field_path_set(ctx, path, &c.subject.clone(), Term::var("__x"), Term::var("__v"), line);
        let x = if path.len() > 1 { "+__x" } else { "__x" };
        Term::Lam(vec![x.into(), "__v".into()], Box::new(body))
    }

    /// The Fire type of a field of a value of type `subject`.
    fn field_type_of(&mut self, tid: TypeId, idx: usize, subject: &Type) -> Type {
        let args = match self.store.shallow(subject) {
            Type::Data(_, a) => a,
            _ => vec![],
        };
        let fty = self.core.types[tid].ctors[0].fields[idx].ty.clone();
        self.subst_field(tid, &fty, &args)
    }

    /// Read a field along (type, field) steps (through adopted parents).
    pub fn field_path_get(&mut self, ctx: &FnCtx, path: &[(TypeId, usize)], subject: &Type, obj: Term, line: usize) -> Term {
        let mut obj = obj;
        let mut sty = subject.clone();
        for (tid, idx) in path {
            let g = self.getter(*tid, *idx);
            let mut a = self.type_args_of(ctx, &sty, *tid, line);
            a.push(obj);
            obj = Term::Call(g, a);
            sty = self.field_type_of(*tid, *idx, &sty);
        }
        obj
    }

    /// Replace a field along (type, field) steps: the objects on the way
    /// are rebuilt.
    pub fn field_path_set(&mut self, ctx: &FnCtx, path: &[(TypeId, usize)], subject: &Type, obj: Term, v: Term, line: usize) -> Term {
        let (tid, idx) = path[0];
        let s = self.setter(tid, idx);
        let mut a = self.type_args_of(ctx, subject, tid, line);
        let new_inner = if path.len() == 1 {
            v
        } else {
            let inner_ty = self.field_type_of(tid, idx, subject);
            let g = self.getter(tid, idx);
            let mut ga = self.type_args_of(ctx, subject, tid, line);
            ga.push(obj.clone());
            self.field_path_set(ctx, &path[1..], &inner_ty, Term::Call(g, ga), v, line)
        };
        a.push(obj);
        a.push(new_inner);
        Term::Call(s, a)
    }

    /// A solved concrete constraint as a closed function term (for passing
    /// as a dictionary).
    pub fn concrete_dict(&mut self, ctx: &FnCtx, id: ConstraintId, subs: &[ConstraintId], line: usize) -> Term {
        let c = &self.store.constraints[id].clone();
        if let Class::Zero = &c.class {
            // a value, not an operation
            let mut tmp_ctx = ctx.clone();
            let subject = self.store.resolve(&c.subject);
            return self.zero_of(&mut tmp_ctx, &subject, &[], line);
        }
        let arity = match &c.class {
            Class::Show | Class::Len | Class::Iter(_) | Class::Convert(..) | Class::Arith(ArithOp::Neg) | Class::Field(..) => 1,
            Class::Method(_, args, _) => 1 + args.len(),
            Class::IndexSet(..) => 3,
            _ => 2,
        };
        let params: Vec<String> = (0..arity).map(|i| format!("__d{}", i)).collect();
        let terms: Vec<Term> = params.iter().map(|p| Term::var(p)).collect();
        let mut tmp_ctx = ctx.clone();
        let (body, mode) = self.concrete_op(&mut tmp_ctx, id, subs, terms, vec![], line);
        // fallible classes answer a result in dictionary form
        let body = match mode {
            Mode::Pure if c.class.fallible() => Term::ctor("Done", vec![body]),
            Mode::Io => {
                self.error(line, "an operation that performs IO cannot be passed through a generic def");
                body
            }
            _ => body,
        };
        Term::Lam(params, Box::new(body))
    }

    /// The Bend term for a solved concrete constraint applied to arguments,
    /// and the mode it answers in (a higher-order method's function may
    /// add to the class's own).
    fn concrete_op(&mut self, ctx: &mut FnCtx, id: ConstraintId, subs: &[ConstraintId], mut terms: Vec<Term>, fnvals: Vec<FnVal>, line: usize) -> (Term, Mode) {
        let c = self.store.constraints[id].clone();
        let base = self.dict_mode(id);
        self.hof_mode = None;
        let subject = self.store.resolve(&c.subject);
        let st = self.ty_in(ctx, &subject, line);
        let sub_terms: Vec<Term> = subs.iter().map(|s| self.dict_term(ctx, *s, line)).collect();
        let t = match (&c.class, &subject) {
            (Class::Eq | Class::Ord | Class::Show, _) => {
                let kind = match c.class {
                    Class::Eq => "eq",
                    Class::Ord => "lt",
                    _ => "show",
                };
                let f = self.derived_op(ctx, kind, &subject, subs, line);
                apply_term(f, terms)
            }
            (Class::Arith(op), Type::Int) => {
                let (a, b) = arith_args(op, &mut terms);
                match (op, b) {
                    (ArithOp::Add, Some(b)) => Term::op(a, "+", b, Ty::U32),
                    (ArithOp::Sub, Some(b)) => Term::op(a, "-", b, Ty::U32),
                    (ArithOp::Mul, Some(b)) => Term::op(a, "*", b, Ty::U32),
                    (ArithOp::Div, Some(b)) => Term::call("F.i32.div", vec![a, b]),
                    (ArithOp::Mod, Some(b)) => Term::call("F.i32.mod", vec![a, b]),
                    (ArithOp::Pow, Some(b)) => Term::call("F.i32.pow", vec![a, b]),
                    (ArithOp::Neg, None) => Term::op(Term::U32(0), "-", a, Ty::U32),
                    _ => Term::unit(),
                }
            }
            (Class::Arith(op), Type::Float) => {
                let (a, b) = arith_args(op, &mut terms);
                match (op, b) {
                    (ArithOp::Add, Some(b)) => Term::op(a, "+", b, Ty::F32),
                    (ArithOp::Sub, Some(b)) => Term::op(a, "-", b, Ty::F32),
                    (ArithOp::Mul, Some(b)) => Term::op(a, "*", b, Ty::F32),
                    (ArithOp::Div, Some(b)) => Term::op(a, "/", b, Ty::F32),
                    (ArithOp::Mod, Some(b)) => Term::op(a, "%", b, Ty::F32),
                    (ArithOp::Pow, Some(b)) => Term::call("F32.pow", vec![a, b]),
                    (ArithOp::Neg, None) => Term::call("F32.neg", vec![a]),
                    _ => Term::unit(),
                }
            }
            (Class::Arith(ArithOp::Add), Type::Str) => {
                let b = terms.pop().unwrap();
                let a = terms.pop().unwrap();
                Term::cat(a, b)
            }
            (Class::Arith(ArithOp::Add), Type::List(e)) => {
                let et = self.ty_in(ctx, e, line);
                let b = terms.pop().unwrap();
                let a = terms.pop().unwrap();
                Term::call("List.append", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(et), a, b])
            }
            (Class::OrElse(..), Type::Bool) => {
                let b = terms.pop().unwrap();
                let a = terms.pop().unwrap();
                Term::Or(Box::new(a), Box::new(b))
            }
            (Class::OrElse(..), Type::Data(MAYBE, args)) => {
                let et = self.ty_in(ctx, &args[0], line);
                let b = terms.pop().unwrap();
                let a = terms.pop().unwrap();
                Term::call("F.maybe.or", vec![Term::TyArg(et), a, b])
            }
            (Class::Len, Type::List(e)) => {
                let et = self.ty_in(ctx, e, line);
                Term::call("F.list.len", vec![Term::TyArg(et), terms.remove(0)])
            }
            (Class::Len, Type::Str) => Term::call("F.str.len", vec![terms.remove(0)]),
            (Class::Len, Type::Map(v)) => {
                let vt = self.ty_in(ctx, v, line);
                Term::call("F.map.size", vec![Term::TyArg(vt), terms.remove(0)])
            }
            (Class::Len, Type::Data(RANGE, _)) => Term::call("F.range.len", vec![terms.remove(0)]),
            (Class::Iter(_), Type::List(_)) => terms.remove(0),
            (Class::Iter(_), Type::Data(RANGE, _)) => Term::call("F.range.to_list", vec![terms.remove(0)]),
            (Class::Iter(_), Type::Str) => Term::call("F.str.chars", vec![terms.remove(0)]),
            (Class::Iter(_), Type::Map(v)) => {
                let vt = self.ty_in(ctx, v, line);
                Term::call("F.map.entries", vec![Term::TyArg(vt), terms.remove(0)])
            }
            (Class::Index(..), Type::List(e)) => {
                let et = self.ty_in(ctx, e, line);
                let i = terms.pop().unwrap();
                Term::call("F.list.index", vec![Term::TyArg(et), terms.remove(0), i])
            }
            (Class::Index(..), Type::Str) => {
                let i = terms.pop().unwrap();
                Term::call("F.str.index", vec![terms.remove(0), i])
            }
            (Class::Index(..), Type::Data(RANGE, _)) => {
                let i = terms.pop().unwrap();
                Term::call("F.range.index", vec![terms.remove(0), i])
            }
            (Class::Index(..), Type::Map(v)) => {
                let vt = self.ty_in(ctx, v, line);
                let k = terms.pop().unwrap();
                Term::call("F.map.lookup", vec![Term::TyArg(vt), terms.remove(0), k])
            }
            (Class::IndexSet(..), Type::List(e)) => {
                let et = self.ty_in(ctx, e, line);
                let v = terms.pop().unwrap();
                let i = terms.pop().unwrap();
                Term::call("F.list.set", vec![Term::TyArg(et), terms.remove(0), i, v])
            }
            (Class::IndexSet(..), Type::Map(v)) => {
                let vt = self.ty_in(ctx, v, line);
                let val = terms.pop().unwrap();
                let k = terms.pop().unwrap();
                Term::call("Map.set", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(vt), terms.remove(0), k, val])
            }
            (Class::Convert(to, _), _) => {
                let x = terms.remove(0);
                match (*to, &subject) {
                    ("int", Type::Int) | ("float", Type::Float) => x,
                    ("int", Type::Float) => Term::call("F.f32.to_i32", vec![x]),
                    ("int", Type::Bool) => Term::call("Bool.to_u32", vec![x]),
                    ("int", Type::Str) => Term::call("F.i32.parse_or_abort", vec![x]),
                    ("float", Type::Int) => Term::call("F.i32.to_f32", vec![x]),
                    ("float", Type::Str) => Term::call("F.f32.parse_or_abort", vec![x]),
                    _ => x,
                }
            }
            (Class::Method(name, margs, mret), _) => {
                let mret = mret.clone();
                let margs = margs.clone();
                self.builtin_method(ctx, name, &subject, &st, terms, fnvals, &sub_terms, &margs, &mret, base, line)
            }
            _ => {
                self.error(line, format!("no implementation of {} on {:?}", crate::check::describe_class(&c.class), self.store.resolve(&c.subject)));
                Term::unit()
            }
        };
        let mode = self.hof_mode.take().unwrap_or(base);
        (t, mode)
    }

    /// The derived operation of a type as a closed term, given the solved
    /// sub-constraints for its parts.
    fn derived_op(&mut self, ctx: &mut FnCtx, kind: &str, t: &Type, subs: &[ConstraintId], line: usize) -> Term {
        // `repr` is `show` for a string inside a container (quoted)
        let base = if kind == "repr" { "show" } else { kind };
        let ty = self.store.shallow(t);
        match &ty {
            Type::Int => prim_op("F.i32", base),
            Type::Float => prim_op("F.f32", base),
            Type::Str => prim_op("F.str", kind),
            Type::Bool => prim_op("F.bool", base),
            Type::Unit => prim_op("F.unit", base),
            Type::Var(_) => {
                // the subject stayed generic: a dictionary of the def
                let names = ctx.tparams.clone();
                let ops: Vec<(String, String)> = ctx.dicts.iter().filter_map(|d| {
                    let c = &self.store.constraints[d.id];
                    let want = match kind {
                        "eq" => matches!(c.class, Class::Eq),
                        "lt" => matches!(c.class, Class::Ord),
                        _ => matches!(c.class, Class::Show),
                    };
                    if !want {
                        return None;
                    }
                    let n = match self.store.shallow(&c.subject) {
                        Type::Var(v) => names.iter().find(|(w, _)| *w == v).map(|(_, n)| n.clone()),
                        _ => None,
                    }?;
                    Some((n, d.name.clone()))
                }).collect();
                self.derived_term(kind, t, &names, &ops, line)
            }
            Type::List(e) | Type::Map(e) => {
                let et = self.ty_in(ctx, e, line);
                let sub = match (base, self.store.shallow(e), subs.first()) {
                    ("show", Type::Str, _) => prim_op("F.str", "repr"),
                    (_, _, Some(s)) => self.dict_term(ctx, *s, line),
                    _ => self.derived_op(ctx, if base == "show" { "repr" } else { base }, e, &[], line),
                };
                let prefix = if matches!(ty, Type::List(_)) { "F.list" } else { "F.map" };
                lambda_over(if base == "show" { 1 } else { 2 }, Term::Call(format!("{}.{}", prefix, base), vec![Term::TmplTy(et), tmpl_arg(sub)]))
            }
            Type::Fn(..) => {
                self.error(line, format!("cannot {} a function", kind));
                Term::unit()
            }
            Type::Data(id, args) => {
                let id = *id;
                let name = self.derived_def(base, id, line);
                let actuals = self.eff_actuals(id, args);
                let mut call_args: Vec<Term> = actuals.iter().map(|a| Term::TmplTy(self.ty_in(ctx, a, line))).collect();
                let inner = component_kind(id, kind);
                for (actual, (_, i)) in actuals.iter().zip(self.eff_params[id].clone()) {
                    // the sub-constraint for this argument position (a string
                    // inside a container shows quoted, so derive that one)
                    let quoted = inner == "repr" && matches!(self.store.shallow(actual), Type::Str);
                    let sub = match subs.get(i) {
                        Some(s) if !quoted => self.dict_term(ctx, *s, line),
                        _ => self.derived_op(ctx, inner, actual, &[], line),
                    };
                    call_args.push(tmpl_arg(sub));
                }
                let arity = if base == "show" { 1 } else { 2 };
                lambda_over(arity, Term::Call(name, call_args))
            }
        }
    }

    /// Builtin methods on builtin types, mapped onto the prelude and Base.
    fn builtin_method(&mut self, ctx: &mut FnCtx, name: &str, subject: &Type, st: &Ty, mut terms: Vec<Term>, mut fnvals: Vec<FnVal>, subs: &[Term], margs: &[Type], mret: &Type, base: Mode, line: usize) -> Term {
        let recv = terms.remove(0);
        let elem_ty = |lw: &mut Lower, ctx: &FnCtx| -> Ty {
            match lw.store.shallow(subject) {
                Type::List(e) => lw.ty_in(ctx, &e, line),
                Type::Map(v) => lw.ty_in(ctx, &v, line),
                _ => Ty::U32,
            }
        };
        let arg = |terms: &mut Vec<Term>, i: usize| -> Term { terms.get(i).cloned().unwrap_or(Term::unit()) };
        let ta = |t: Ty| Term::TyArg(t);
        match (name, self.store.shallow(subject)) {
            // strings
            ("length", Type::Str) => Term::call("F.str.len", vec![recv]),
            ("upper", Type::Str) => Term::call("String.to_upper", vec![recv]),
            ("lower", Type::Str) => Term::call("String.to_lower", vec![recv]),
            ("trim", Type::Str) => Term::call("String.trim", vec![recv]),
            ("trim_start", Type::Str) => Term::call("String.trim_start", vec![recv]),
            ("trim_end", Type::Str) => Term::call("String.trim_end", vec![recv]),
            ("split", Type::Str) => {
                if terms.is_empty() { Term::call("F.str.split_ws", vec![recv]) } else { Term::call("F.str.split", vec![recv, arg(&mut terms, 0)]) }
            }
            ("lines", Type::Str) => Term::call("String.lines", vec![recv]),
            ("replace", Type::Str) => Term::call("F.str.replace", vec![recv, arg(&mut terms, 0), arg(&mut terms, 1)]),
            ("contains", Type::Str) => Term::call("String.contains", vec![recv, arg(&mut terms, 0)]),
            ("starts_with", Type::Str) => Term::call("String.starts_with", vec![recv, arg(&mut terms, 0)]),
            ("ends_with", Type::Str) => Term::call("String.ends_with", vec![recv, arg(&mut terms, 0)]),
            ("index_of", Type::Str) => Term::call("F.str.index_of", vec![recv, arg(&mut terms, 0)]),
            ("chars", Type::Str) => Term::call("F.str.chars", vec![recv]),
            ("repeat", Type::Str) => Term::call("F.str.repeat", vec![recv, arg(&mut terms, 0)]),
            ("to_int", Type::Str) => Term::call("F.i32.parse_or_abort", vec![recv]),
            ("to_float", Type::Str) => Term::call("F.f32.parse_or_abort", vec![recv]),
            ("parse_int", Type::Str) => Term::call("F.i32.parse_result", vec![recv]),
            ("parse_float", Type::Str) => Term::call("F.f32.parse_result", vec![recv]),
            ("is_empty", Type::Str) => Term::call("String.is_empty", vec![recv]),
            ("reverse" | "reversed", Type::Str) => Term::call("String.reverse", vec![recv]),
            ("join", Type::Str) => Term::call("String.join", vec![arg(&mut terms, 0), recv]),
            ("to_str", Type::Str) => recv,
            ("char_code", Type::Str) => Term::call("F.str.char_code", vec![recv]),
            ("take", Type::Str) => Term::call("F.str.take", vec![recv, arg(&mut terms, 0)]),
            ("drop", Type::Str) => Term::call("F.str.drop", vec![recv, arg(&mut terms, 0)]),
            ("slice", Type::Str) => Term::call("F.str.slice_range", vec![recv, arg(&mut terms, 0)]),
            // ints
            ("abs", Type::Int) => Term::call("F.i32.abs", vec![recv]),
            ("to_str", Type::Int) => Term::call("F.i32.show", vec![recv]),
            ("to_float", Type::Int) => Term::call("F.i32.to_f32", vec![recv]),
            ("to_int", Type::Int) => recv,
            ("sqrt", Type::Int) => Term::call("F32.sqrt", vec![Term::call("F.i32.to_f32", vec![recv])]),
            ("floor" | "ceil" | "round", Type::Int) => recv,
            // floats
            ("abs", Type::Float) => Term::call("F32.abs", vec![recv]),
            ("floor", Type::Float) => Term::call("F32.floor", vec![recv]),
            ("ceil", Type::Float) => Term::call("F32.ceil", vec![recv]),
            ("sqrt", Type::Float) => Term::call("F32.sqrt", vec![recv]),
            ("round", Type::Float) => {
                if terms.is_empty() { Term::call("F32.round", vec![recv]) } else { Term::call("F.f32.round_digits", vec![recv, arg(&mut terms, 0)]) }
            }
            ("to_str", Type::Float) => Term::call("F.f32.show", vec![recv]),
            ("to_int", Type::Float) => Term::call("F.f32.to_i32", vec![recv]),
            ("to_float", Type::Float) => recv,
            ("to_str", Type::Bool) => Term::call("F.bool.show", vec![recv]),
            // lists
            ("length", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.len", vec![ta(et), recv])
            }
            ("map", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let bt = self.list_elem_ty(ctx, mret, line);
                let f = fnvals.remove(0);
                let driver = hof_driver("map", f.mode);
                let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), Term::TmplTy(bt), tmpl_arg(f.code), f.env, recv]);
                self.note_hof_mode(t, f.mode.join(base))
            }
            ("filter", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let f = fnvals.remove(0);
                let driver = hof_driver("filter", f.mode);
                let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), tmpl_arg(f.code), f.env, recv]);
                self.note_hof_mode(t, f.mode.join(base))
            }
            ("each", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let f = fnvals.remove(0);
                let rt = match self.store.shallow(&margs[0]) {
                    Type::Fn(_, r, _) => self.ty_in(ctx, &r, line),
                    _ => Ty::Unit,
                };
                let driver = hof_driver("each", f.mode);
                let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), Term::TmplTy(rt), tmpl_arg(f.code), f.env, recv]);
                self.note_hof_mode(t, f.mode.join(base))
            }
            ("reduce", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let f = fnvals.remove(0);
                if terms.is_empty() {
                    let driver = hof_driver("reduce1", f.mode);
                    let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), tmpl_arg(f.code), f.env, recv]);
                    self.note_hof_mode(t, f.mode.join(base))
                } else {
                    let at = self.ty_in(ctx, mret, line);
                    let driver = hof_driver("foldl", f.mode);
                    let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), Term::TmplTy(at), tmpl_arg(f.code), f.env, recv, arg(&mut terms, 0)]);
                    self.note_hof_mode(t, f.mode.join(base))
                }
            }
            ("any" | "all" | "count" | "find", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let f = fnvals.remove(0);
                let driver = hof_driver(name, f.mode);
                let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), tmpl_arg(f.code), f.env, recv]);
                self.note_hof_mode(t, f.mode.join(base))
            }
            ("sum", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let add = subs.first().cloned().unwrap_or(prim_op("F.i32", "add"));
                let zero = self.zero_of(ctx, mret, subs.get(1..).unwrap_or(&[]), line);
                Term::call("F.list.sum", vec![Term::TmplTy(et), tmpl_arg(add), recv, zero])
            }
            ("min" | "max", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let lt = self.elem_op(ctx, subs, subject, "lt", line);
                Term::call(if name == "min" { "F.list.min" } else { "F.list.max" }, vec![Term::TmplTy(et), tmpl_arg(lt), recv])
            }
            ("join", Type::List(_)) => Term::call("String.join", vec![recv, arg(&mut terms, 0)]),
            ("contains", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let eq = self.elem_op(ctx, subs, subject, "eq", line);
                Term::call("F.list.contains", vec![Term::TmplTy(et), tmpl_arg(eq), recv, arg(&mut terms, 0)])
            }
            ("index_of", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let eq = self.elem_op(ctx, subs, subject, "eq", line);
                Term::call("F.list.index_of", vec![Term::TmplTy(et), tmpl_arg(eq), recv, arg(&mut terms, 0)])
            }
            ("first", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.first", vec![ta(et), recv])
            }
            ("last", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.last", vec![ta(et), recv])
            }
            ("reverse" | "reversed", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("List.reverse", vec![ta(Ty::Param("&2".into())), ta(et), recv])
            }
            ("sort" | "sorted", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                if fnvals.is_empty() {
                    let lt = self.elem_op(ctx, subs, subject, "lt", line);
                    Term::call("F.list.sort", vec![Term::TmplTy(et), tmpl_arg(lt), recv])
                } else {
                    let f = fnvals.remove(0);
                    let kt = match self.store.shallow(&margs[0]) {
                        Type::Fn(_, k, _) => self.ty_in(ctx, &k, line),
                        _ => Ty::U32,
                    };
                    let lt = self.elem_op(ctx, subs, subject, "lt", line);
                    let driver = hof_driver("sort_by_key", f.mode);
                    let t = Term::Call(driver, vec![Term::TmplTy(f.env_ty.clone()), Term::TmplTy(et), Term::TmplTy(kt), tmpl_arg(f.code), tmpl_arg(lt), f.env, recv]);
                    self.note_hof_mode(t, f.mode.join(base))
                }
            }
            ("push", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                let mut acc = recv;
                for t in terms {
                    acc = Term::call("F.list.push", vec![ta(et.clone()), acc, t]);
                }
                acc
            }
            ("pop", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.pop", vec![ta(et), recv])
            }
            ("drop_last", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.drop_last", vec![ta(et), recv])
            }
            ("take", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.take", vec![ta(et), recv, arg(&mut terms, 0)])
            }
            ("drop", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.drop", vec![ta(et), recv, arg(&mut terms, 0)])
            }
            ("slice", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.slice_range", vec![ta(et), recv, arg(&mut terms, 0)])
            }
            ("to_list", Type::List(_)) => recv,
            ("is_empty", Type::List(_)) => {
                let et = elem_ty(self, ctx);
                Term::call("F.list.is_empty", vec![ta(et), recv])
            }
            ("flatten", Type::List(_)) => {
                let it = self.list_elem_ty(ctx, mret, line);
                Term::call("F.list.flatten", vec![ta(it), recv])
            }
            // ranges
            ("to_list", Type::Data(RANGE, _)) => Term::call("F.range.to_list", vec![recv]),
            ("reverse" | "reversed", Type::Data(RANGE, _)) => Term::call("List.reverse", vec![ta(Ty::Param("&2".into())), ta(Ty::U32), Term::call("F.range.to_list", vec![recv])]),
            ("sum", Type::Data(RANGE, _)) => Term::call("F.list.sum", vec![Term::TmplTy(Ty::U32), tmpl_arg(prim_op("F.i32", "add")), Term::call("F.range.to_list", vec![recv]), Term::U32(0)]),
            ("length", Type::Data(RANGE, _)) => Term::call("F.range.len", vec![recv]),
            ("contains", Type::Data(RANGE, _)) => Term::call("F.range.contains", vec![recv, arg(&mut terms, 0)]),
            ("min" | "first", Type::Data(RANGE, _)) => Term::call("F.range.first", vec![recv]),
            ("max" | "last", Type::Data(RANGE, _)) => Term::call("F.range.last", vec![recv]),
            ("take", Type::Data(RANGE, _)) => Term::call("F.list.take", vec![ta(Ty::U32), Term::call("F.range.to_list", vec![recv]), arg(&mut terms, 0)]),
            ("drop", Type::Data(RANGE, _)) => Term::call("F.list.drop", vec![ta(Ty::U32), Term::call("F.range.to_list", vec![recv]), arg(&mut terms, 0)]),
            ("slice", Type::Data(RANGE, _)) => Term::call("F.range.slice_range", vec![recv, arg(&mut terms, 0)]),
            ("map" | "filter" | "each" | "reduce", Type::Data(RANGE, _)) => {
                // through the list
                let list = Term::call("F.range.to_list", vec![recv]);
                let mut all = vec![list];
                all.extend(terms);
                let lsub = Type::list(Type::Int);
                let lst = Ty::list(Ty::U32);
                self.builtin_method(ctx, name, &lsub, &lst, all, fnvals, subs, margs, mret, base, line)
            }
            // dictionaries
            ("keys", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("Map.keys", vec![ta(Ty::Param("&2".into())), ta(vt), recv])
            }
            ("values", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("F.map.values", vec![ta(vt), recv])
            }
            ("entries", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("F.map.entries", vec![ta(vt), recv])
            }
            ("has", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("F.map.has", vec![ta(vt), recv, arg(&mut terms, 0)])
            }
            ("length" | "size", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("F.map.size", vec![ta(vt), recv])
            }
            ("get", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("F.map.lookup", vec![ta(vt), recv, arg(&mut terms, 0)])
            }
            ("set", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("Map.set", vec![ta(Ty::Param("&2".into())), ta(vt), recv, arg(&mut terms, 0), arg(&mut terms, 1)])
            }
            ("remove" | "delete", Type::Map(_)) => {
                let vt = elem_ty(self, ctx);
                Term::call("Map.del", vec![ta(Ty::Param("&2".into())), ta(vt), recv, arg(&mut terms, 0)])
            }
            _ => {
                self.error(line, format!("no implementation of .{}() on {}", name, st.render()));
                Term::unit()
            }
        }
    }

    /// A higher-order builtin's answer comes out in its function's mode
    /// joined with the method's own; `concrete_op` reads it back.
    fn note_hof_mode(&mut self, t: Term, mode: Mode) -> Term {
        self.hof_mode = Some(mode);
        t
    }

    /// The operation `kind` on the elements of a list: the solved
    /// sub-constraint when the checker recorded one, else derived.
    fn elem_op(&mut self, ctx: &mut FnCtx, subs: &[Term], subject: &Type, kind: &str, line: usize) -> Term {
        if let Some(s) = subs.first() {
            return s.clone();
        }
        let e = match self.store.shallow(subject) {
            Type::List(e) => *e,
            _ => Type::Int,
        };
        self.derived_op(ctx, kind, &e, &[], line)
    }

    /// The zero of a summable type (for a generic one, the `Zero`
    /// dictionary the checker raised, passed in `given`).
    fn zero_of(&mut self, ctx: &mut FnCtx, t: &Type, given: &[Term], line: usize) -> Term {
        if let Some(z) = given.first() {
            return z.clone();
        }
        match self.store.shallow(t) {
            Type::Int => Term::U32(0),
            Type::Float => Term::F32(0.0),
            Type::Str => Term::Str(String::new()),
            Type::List(_) => Term::List(vec![]),
            other => {
                let names = ctx.tparams.clone();
                let ops: Vec<(String, String)> = vec![];
                self.derived_term("default", &other, &names, &ops, line)
            }
        }
    }

    /// Fixed-signature builtins.
    fn lower_builtin(&mut self, ctx: &mut FnCtx, name: &str, args: &[Expr], ret_ty: &Type, pre: &mut Vec<ir::Stmt>, line: usize) -> Term {
        let ts: Vec<Term> = args.iter().map(|a| self.expr(ctx, a, pre)).collect();
        let rty = self.ty_in(ctx, ret_ty, line);
        let a = |i: usize| ts.get(i).cloned().unwrap_or(Term::unit());
        
        match name {
            "print" => {
                let text = ts.iter().cloned().reduce(|x, y| Term::cat(Term::cat(x, Term::Str(" ".into())), y)).unwrap_or(Term::Str(String::new()));
                let t = Term::call("IO.print", vec![text]);
                self.bind_monadic(ctx, t, Mode::Io, &Ty::Unit, pre, line)
            }
            "assert" => {
                let t = Term::call("F.assert", vec![a(0), a(1)]);
                self.bind_failing(ctx, t, &Ty::Unit, pre, line)
            }
            "maybe.or" => {
                let et = rty.clone();
                Term::call("F.maybe.or", vec![Term::TyArg(et), a(0), a(1)])
            }
            "maybe.unwrap" => {
                let t = Term::call("F.maybe.unwrap", vec![Term::TyArg(rty.clone()), a(0)]);
                self.bind_failing(ctx, t, &rty, pre, line)
            }
            "result.unwrap_ok" => {
                let et = match self.store.shallow(&args[0].ty) {
                    Type::Data(RESULT, r) => self.ty_in(ctx, &r[0], line),
                    _ => Ty::Str,
                };
                let t = Term::call("F.result.unwrap_ok", vec![Term::TyArg(et), Term::TyArg(rty.clone()), a(0)]);
                self.bind_failing(ctx, t, &rty, pre, line)
            }
            "result.unwrap_err" => {
                let at = match self.store.shallow(&args[0].ty) {
                    Type::Data(RESULT, r) => self.ty_in(ctx, &r[1], line),
                    _ => Ty::Str,
                };
                let t = Term::call("F.result.unwrap_err", vec![Term::TyArg(rty.clone()), Term::TyArg(at), a(0)]);
                self.bind_failing(ctx, t, &rty, pre, line)
            }
            "list.at" => {
                let et = rty.clone();
                let t = Term::call("F.list.index", vec![Term::TyArg(et), a(0), a(1)]);
                self.bind_failing(ctx, t, &rty, pre, line)
            }
            "list.drop" => {
                let et = self.list_elem_ty(ctx, &args[0].ty, line);
                Term::call("F.list.drop", vec![Term::TyArg(et), a(0), a(1)])
            }
            "list.need_exactly" | "list.need_at_least" => {
                let et = self.list_elem_ty(ctx, &args[0].ty, line);
                let f = if name == "list.need_exactly" { "F.list.need_exactly" } else { "F.list.need_at_least" };
                let t = Term::call(f, vec![Term::TyArg(et), a(0), a(1)]);
                self.bind_failing(ctx, t, &Ty::Unit, pre, line)
            }
            "float.fixed" => Term::call("F.f32.show_fixed", vec![a(0), a(1)]),
            "int.and" => Term::call("U32.and", vec![a(0), a(1)]),
            "int.or" => Term::call("U32.or", vec![a(0), a(1)]),
            "int.xor" => Term::call("U32.xor", vec![a(0), a(1)]),
            "int.shl" => Term::call("U32.shln", vec![a(0), Term::call("U32.to_nat", vec![a(1)])]),
            "int.shr" => Term::call("F.i32.shr", vec![a(0), Term::call("U32.to_nat", vec![a(1)])]),
            "int.ushr" => Term::call("U32.shrn", vec![a(0), Term::call("U32.to_nat", vec![a(1)])]),
            "math.pi" => Term::call("F32.pi", vec![]),
            "math.e" => Term::F32(std::f32::consts::E),
            "math.tau" => Term::F32(std::f32::consts::TAU),
            "math.inf" => Term::call("F.f32.inf", vec![]),
            "math.sqrt" => Term::call("F32.sqrt", vec![a(0)]),
            "math.sin" => Term::call("F32.sin", vec![a(0)]),
            "math.cos" => Term::call("F32.cos", vec![a(0)]),
            "math.tan" => Term::call("F32.tan", vec![a(0)]),
            "math.asin" => Term::call("F32.asin", vec![a(0)]),
            "math.acos" => Term::call("F32.acos", vec![a(0)]),
            "math.atan" => Term::call("F32.atan", vec![a(0)]),
            "math.atan2" => Term::call("F32.atan2", vec![a(0), a(1)]),
            "math.exp" => Term::call("F32.exp", vec![a(0)]),
            "math.log" => {
                if ts.len() == 1 { Term::call("F32.log", vec![a(0)]) } else { Term::call("F.f32.log_base", vec![a(0), a(1)]) }
            }
            "math.log2" => Term::call("F32.log2", vec![a(0)]),
            "math.log10" => Term::call("F32.log10", vec![a(0)]),
            "math.floor" => Term::call("F32.floor", vec![a(0)]),
            "math.ceil" => Term::call("F32.ceil", vec![a(0)]),
            "math.abs" => Term::call("F32.abs", vec![a(0)]),
            "math.pow" => Term::call("F32.pow", vec![a(0), a(1)]),
            "math.min" => Term::call("F32.min", vec![a(0), a(1)]),
            "math.max" => Term::call("F32.max", vec![a(0), a(1)]),
            "strings.join" => {
                if ts.len() == 1 { Term::call("String.join", vec![a(0), Term::Str(String::new())]) } else { Term::call("String.join", vec![a(0), a(1)]) }
            }
            "strings.char_code" => Term::call("F.str.char_code", vec![a(0)]),
            "strings.from_char_code" => Term::call("F.str.from_char_code", vec![a(0)]),
            "lists.flatten" => {
                let it = self.list_elem_ty(ctx, ret_ty, line);
                Term::call("F.list.flatten", vec![Term::TyArg(it), a(0)])
            }
            "lists.repeat" => {
                let et = self.ty_in(ctx, &args[0].ty, line);
                Term::call("F.list.repeat", vec![Term::TyArg(et), a(0), a(1)])
            }
            "io.read_file" => {
                let t = Term::call("F.io.read_file", vec![a(0)]);
                self.bind_monadic(ctx, t, Mode::Io, &rty, pre, line)
            }
            "io.write_file" => {
                let t = Term::call("F.io.write_file", vec![a(0), a(1)]);
                self.bind_monadic(ctx, t, Mode::Io, &rty, pre, line)
            }
            "time.now" => {
                let t = Term::call("F.time.now", vec![]);
                self.bind_monadic(ctx, t, Mode::Io, &rty, pre, line)
            }
            other => {
                self.error(line, format!("unknown builtin {}", other));
                Term::unit()
            }
        }
    }

    /// Apply a format spec to a rendered value.
    /// A value shown as text, padded to a width.
    fn pad(&mut self, s: Term, pad: &Pad) -> Term {
        let width = Term::U32(pad.width);
        let f = match pad.align {
            Align::Zeros => return Term::call("F.fmt.pad_zero", vec![s, width]),
            Align::Left => "F.fmt.pad_right",
            Align::Right => "F.fmt.pad_left",
            Align::Center => "F.fmt.pad_center",
        };
        Term::call(f, vec![s, width, Term::Chr(pad.fill)])
    }
}

/// The list driver of a higher-order method in its callback's mode:
/// `F.list.map_env`, `F.list.map_res_env`, `F.list.map_io_env`.
fn hof_driver(name: &str, mode: Mode) -> String {
    format!("F.list.{}{}_env", name, mode.suffix())
}

/// The leading arguments of a call of an image: its type arguments
/// (templates or erased) around its dictionaries.
fn image_prefix(img: &Image, types: &[Ty], dicts: Vec<Term>) -> Vec<Term> {
    let mut args: Vec<Term> = if img.template { types.iter().map(|t| Term::TmplTy(t.clone())).collect() } else { vec![] };
    args.extend(dicts);
    if !img.template {
        args.extend(types.iter().map(|t| Term::TyArg(t.clone())));
    }
    args
}

/// Builtin methods whose function argument is passed as code plus
/// environment.
pub fn is_hof_method(n: &str) -> bool {
    matches!(n, "map" | "filter" | "each" | "reduce" | "any" | "all" | "find" | "count" | "sort" | "sorted")
}

/// How the components of a data type show: quoted strings inside any
/// container except `T | nothing`, which shows as its value.
pub fn component_kind(tid: TypeId, kind: &str) -> &str {
    match kind {
        "show" | "repr" if tid == MAYBE => kind,
        "show" | "repr" => "repr",
        other => other,
    }
}

/// The operands of an arithmetic operation: one for negation.
fn arith_args(op: &ArithOp, terms: &mut Vec<Term>) -> (Term, Option<Term>) {
    if matches!(op, ArithOp::Neg) {
        return (terms.pop().unwrap_or(Term::unit()), None);
    }
    let b = terms.pop();
    let a = terms.pop().unwrap_or(Term::unit());
    (a, b)
}

pub fn builtin_mode(name: &str) -> Mode {
    match name {
        "print" | "io.read_file" | "io.write_file" | "time.now" => Mode::Io,
        "assert" | "maybe.unwrap" | "result.unwrap_ok" | "result.unwrap_err" | "list.at" | "list.need_exactly" | "list.need_at_least" => Mode::Result,
        _ => Mode::Pure,
    }
}
