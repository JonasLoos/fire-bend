// src/check/expr.rs
// Expression inference: every AST expression becomes a Core expression
// with a type. Pipelines, `$`, keyword arguments, defaults, records,
// operators (constraints), f-strings, comprehensions, lambdas.

use super::*;

/// Global builtins by name, when the name is not shadowed by a binding.
const GLOBALS: &[&str] = &[
    "print", "len", "sum", "min", "max", "abs", "round", "sorted", "reversed", "range", "error", "assert", "str", "int", "float",
];

impl Checker {
    pub(crate) fn expr(&mut self, kind: ExprKind, ty: Type) -> Expr {
        Expr { kind, ty, line: self.line }
    }

    pub(crate) fn lit(&mut self, l: Lit) -> Expr {
        let ty = match &l {
            Lit::Int(_) => Type::Int,
            Lit::Float(_) => Type::Float,
            Lit::Str(_) => Type::Str,
            Lit::Bool(_) => Type::Bool,
            Lit::Nothing => Type::Unit,
        };
        self.expr(ExprKind::Lit(l), ty)
    }

    pub(crate) fn var(&mut self, name: &str, ty: Type) -> Expr {
        self.expr(ExprKind::Var(name.to_string()), ty)
    }

    /// A fresh local name for a hoisted or synthesized value.
    pub(crate) fn temp(&mut self, hint: &str) -> String {
        self.lambda_counter += 1;
        format!("__{}{}", hint, self.lambda_counter)
    }

    pub(crate) fn check_expr(&mut self, e: &ast::Expression, expected: Option<&Type>) -> Expr {
        #[cfg(not(target_arch = "wasm32"))]
        let x = stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.check_expr_inner(e, expected));
        #[cfg(target_arch = "wasm32")]
        let x = self.check_expr_inner(e, expected);
        match expected {
            Some(t) => self.fit(x, t),
            None => x,
        }
    }

    /// A value where a `T | nothing` is expected: a plain value lifts into
    /// it and `nothing` becomes the absent value; anything else is left to
    /// unification.
    pub(crate) fn fit(&mut self, x: Expr, expected: &Type) -> Expr {
        let Type::Data(MAYBE, args) = self.shallow(expected) else { return x };
        let inner = args[0].clone();
        if matches!(x.kind, ExprKind::Lit(Lit::Nothing)) {
            return self.expr(ExprKind::Con(MAYBE, 0, vec![]), Type::maybe(inner));
        }
        match self.shallow(&x.ty) {
            Type::Data(MAYBE, _) | Type::Var(_) => x,
            _ => {
                let line = self.line;
                self.unify(&inner, &x.ty, line);
                self.some(x)
            }
        }
    }

    fn check_expr_inner(&mut self, e: &ast::Expression, expected: Option<&Type>) -> Expr {
        let line = self.line;
        match e {
            ast::Expression::Identifier(name) => self.check_identifier(name, expected),
            ast::Expression::Import(m) => {
                self.error(line, format!("`${}` is a module: use `${}.name` or destructure it (`{{sqrt}} = $math`)", m, m));
                let t = self.fresh();
                self.var("__bad", t)
            }
            ast::Expression::Number(n) => self.check_number(n, expected),
            ast::Expression::Str(s) | ast::Expression::TString(s) => self.lit(Lit::Str(s.clone())),
            ast::Expression::FString(parts) => self.check_fstring(parts),
            ast::Expression::Boolean(b) => self.lit(Lit::Bool(*b)),
            ast::Expression::Nothing => {
                if let Some(t) = expected
                    && let Type::Data(MAYBE, args) = self.shallow(t) {
                        let t = Type::maybe(args[0].clone());
                        return self.expr(ExprKind::Con(MAYBE, 0, vec![]), t);
                    }
                self.lit(Lit::Nothing)
            }
            ast::Expression::Ellipsis => {
                self.error(line, "`...` is only valid inside a list pattern");
                self.lit(Lit::Nothing)
            }
            ast::Expression::PreviousResult => match self.frame_ref().piped.last().cloned() {
                Some(t) => {
                    let name = format!("__pipe{}", self.frame_ref().piped.len());
                    self.var(&name, t)
                }
                None => {
                    self.error(line, "`$` is only valid on the right of a pipeline operator");
                    let t = self.fresh();
                    self.var("__bad", t)
                }
            },
            ast::Expression::List(items) => {
                let elem = match expected.map(|t| self.shallow(t)) {
                    Some(Type::List(e)) => *e,
                    _ => self.fresh(),
                };
                let mut out = Vec::new();
                for it in items {
                    if let ast::Expression::UnaryOp { op: ast::UnaryOperator::Spread, .. } = it {
                        self.error(line, "spreading into a list literal is not supported; use `+` to concatenate");
                        continue;
                    }
                    let x = self.check_expr(it, Some(&elem));
                    self.unify(&elem, &x.ty, line);
                    out.push(x);
                }
                self.expr(ExprKind::List(out), Type::list(elem))
            }
            ast::Expression::Object(entries) => self.check_object(entries, expected),
            ast::Expression::BinaryOp { left, op, right } => self.check_binary(left, *op, right, expected),
            ast::Expression::UnaryOp { op, operand } => match op {
                ast::UnaryOperator::Not => {
                    let x = self.check_expr(operand, Some(&Type::Bool));
                    self.unify(&Type::Bool, &x.ty, line);
                    self.expr(ExprKind::Not(Box::new(x)), Type::Bool)
                }
                ast::UnaryOperator::Plus => self.check_expr(operand, expected),
                ast::UnaryOperator::Minus => {
                    if let ast::Expression::Number(n) = &**operand {
                        let x = self.check_number(n, expected);
                        return match x.kind {
                            ExprKind::Lit(Lit::Int(i)) => self.lit(Lit::Int(-i)),
                            ExprKind::Lit(Lit::Float(f)) => self.lit(Lit::Float(-f)),
                            _ => x,
                        };
                    }
                    let x = self.check_expr(operand, expected);
                    let t = x.ty.clone();
                    self.dict(Class::Arith(ArithOp::Neg), t.clone(), vec![x], t, line)
                }
                ast::UnaryOperator::Spread => {
                    self.error(line, "`...` is only valid inside a list pattern");
                    self.lit(Lit::Nothing)
                }
            },
            ast::Expression::Lambda { params, body } => self.check_lambda(params, body),
            ast::Expression::Block(stmts) => self.check_block_expr(stmts, expected),
            ast::Expression::Call { function, args, named_args } => self.check_call(function, args, named_args, expected),
            ast::Expression::MemberAccess { object, member } => self.check_member(object, member),
            ast::Expression::SpreadMember { .. } => {
                self.error(line, "`.{...}` is only valid as `self.{...} = parent`");
                self.lit(Lit::Nothing)
            }
            ast::Expression::Index { object, index } => self.check_index(object, index),
            ast::Expression::IfExpr { condition, then_branch, elif_branches, else_branch } => {
                self.check_if_expr(condition, then_branch, elif_branches, else_branch.as_deref(), expected)
            }
            ast::Expression::Comprehension { clauses, body } => self.check_comprehension(clauses, body),
            ast::Expression::TypeCheck { expression, type_expr } => {
                let t = self.annotation(type_expr, line);
                let x = self.check_expr(expression, Some(&t));
                self.unify(&t, &x.ty, line);
                x
            }
            ast::Expression::Range { start, end } => {
                let s = match start {
                    Some(s) => self.check_expr(s, Some(&Type::Int)),
                    None => self.lit(Lit::Int(0)),
                };
                self.unify(&Type::Int, &s.ty, line);
                match end {
                    Some(en) => {
                        let en = self.check_expr(en, Some(&Type::Int));
                        self.unify(&Type::Int, &en.ty, line);
                        self.expr(ExprKind::Con(RANGE, 0, vec![s, en]), Type::range())
                    }
                    None => {
                        self.error(line, "an open range `a..` only counts alongside a finite iterable in a `for` loop");
                        self.expr(ExprKind::Con(RANGE, 0, vec![s.clone(), s]), Type::range())
                    }
                }
            }
            ast::Expression::Pipeline { left, op, right } => self.check_pipeline(left, *op, right),
        }
    }

    fn check_identifier(&mut self, name: &str, expected: Option<&Type>) -> Expr {
        let line = self.line;
        if name == "self" {
            if let FrameKind::Ctor(tid) | FrameKind::Method(tid) = self.frame_ref().kind {
                let t = self.class_self_type(tid);
                return self.expr(ExprKind::SelfValue(tid), t);
            }
            self.error(line, "`self` is only valid inside a class");
            let t = self.fresh();
            return self.var("__bad", t);
        }
        match self.lookup(name) {
            Some(Binding::Local { ty, .. }) => self.var(name, ty),
            Some(b @ Binding::Member { .. }) => self.member_expr(&b),
            Some(Binding::Func(d)) => self.def_value(d, name),
            Some(Binding::Class(tid)) => {
                let d = match self.types[tid].kind {
                    DataKind::Class { ctor, .. } => ctor,
                    _ => unreachable!(),
                };
                self.def_value(d, name)
            }
            Some(Binding::Ctor(tid, ci)) => {
                let (t, subst) = self.instantiate_type(tid);
                let fields = self.types[tid].ctors[ci].fields.len();
                if fields > 0 {
                    self.error(line, format!("the constructor {} takes {} field(s): call it", name, fields));
                }
                let _ = subst;
                if let Some(e) = expected {
                    self.unify(e, &t, line);
                }
                self.expr(ExprKind::Con(tid, ci, vec![]), t)
            }
            Some(Binding::ModuleMember(m, n)) => self.module_value(&m, &n),
            None => {
                if GLOBALS.contains(&name) {
                    return self.global_value(name);
                }
                self.error(line, format!("unknown name '{}'", name));
                let t = self.fresh();
                self.var("__bad", t)
            }
        }
    }

    /// A def used as a value.
    /// A def that captures bindings of the program's top level needs them
    /// from whoever calls it: the caller captures them too.
    pub(crate) fn capture_through(&mut self, d: DefId) {
        if self.defs[d].unit != d || self.defs[d].state != State::Done {
            return;
        }
        let caps: Vec<String> = self.defs[d].captures.iter().map(|(n, _)| n.clone()).collect();
        for n in caps {
            let _ = self.lookup(&n);
        }
    }

    fn def_value(&mut self, d: DefId, name: &str) -> Expr {
        let line = self.line;
        self.ensure_def(d, line);
        self.capture_through(d);
        let nested = self.defs[d].unit != d && !matches!(self.defs[d].kind, DefKind::Method { .. });
        if nested && !self.defs[d].captures.is_empty() {
            // a nested def with captures is a closure bound at its statement
            match self.lookup(&format!("__def_{}", name)) {
                Some(Binding::Local { ty, .. }) => return self.var(&format!("__def_{}", name), ty),
                _ => {
                    self.error(line, format!("'{}' is used before its definition", name));
                }
            }
        }
        let (t, targs, dicts) = self.instantiate_def_type(d, line);
        self.note_call(d, line);
        self.expr(ExprKind::DefRef { def: d, targs, dicts }, t)
    }

    fn check_number(&mut self, n: &ast::NumberLiteral, expected: Option<&Type>) -> Expr {
        let line = self.line;
        let float_wanted = matches!(expected.map(|t| self.shallow(t)), Some(Type::Float));
        match n {
            ast::NumberLiteral::Decimal(s) => {
                if s.contains('.') {
                    match s.parse::<f64>() {
                        Ok(f) => self.lit(Lit::Float(f)),
                        Err(_) => {
                            self.error(line, format!("bad number {}", s));
                            self.lit(Lit::Float(0.0))
                        }
                    }
                } else {
                    match s.parse::<i64>() {
                        Ok(i) if float_wanted => self.lit(Lit::Float(i as f64)),
                        Ok(i) => self.lit(Lit::Int(i)),
                        Err(_) => {
                            self.error(line, format!("bad number {}", s));
                            self.lit(Lit::Int(0))
                        }
                    }
                }
            }
            ast::NumberLiteral::Hex(s) => {
                let v = i64::from_str_radix(s.trim_start_matches("0x"), 16).unwrap_or(0);
                self.lit(Lit::Int(v))
            }
            ast::NumberLiteral::Binary(s) => {
                let v = i64::from_str_radix(s.trim_start_matches("0b"), 2).unwrap_or(0);
                self.lit(Lit::Int(v))
            }
            ast::NumberLiteral::Scientific(s) => {
                let f = s.parse::<f64>().unwrap_or(0.0);
                self.lit(Lit::Float(f))
            }
        }
    }

    /// Render a value to text through its Show dictionary.
    pub(crate) fn show(&mut self, x: Expr) -> Expr {
        let line = self.line;
        if let Type::Str = self.shallow(&x.ty) {
            return x;
        }
        let t = x.ty.clone();
        self.dict(Class::Show, t, vec![x], Type::Str, line)
    }

    fn check_fstring(&mut self, parts: &[ast::FStringPart]) -> Expr {
        let mut out = Vec::new();
        for p in parts {
            match p {
                ast::FStringPart::Text(t) => out.push(FPart::Text(t.clone())),
                ast::FStringPart::Expression(e, spec) => {
                    let x = self.check_expr(e, None);
                    let numeric = matches!(self.shallow(&x.ty), Type::Int | Type::Float);
                    let shown = match spec {
                        // numeric specs format the number itself
                        Some(s) if s.contains('f') && matches!(self.shallow(&x.ty), Type::Float | Type::Int) => {
                            let t = x.ty.clone();
                            let x = if let Type::Int = self.shallow(&t) { self.convert("float", x) } else { x };
                            let digits = s.rsplit('.').next().and_then(|d| d.trim_end_matches('f').parse::<i64>().ok()).unwrap_or(6);
                            let d = self.lit(Lit::Int(digits));
                            self.expr(ExprKind::Builtin("float.fixed".into(), vec![x, d]), Type::Str)
                        }
                        _ => self.show(x),
                    };
                    // numbers align right by default
                    let spec = spec.as_ref().map(|sp| {
                        let has_align = sp.chars().take(2).any(|c| matches!(c, '<' | '>' | '^'));
                        if numeric && !has_align && !sp.is_empty() { format!(">{}", sp) } else { sp.clone() }
                    });
                    out.push(FPart::Expr(shown, spec));
                }
            }
        }
        self.expr(ExprKind::FString(out), Type::Str)
    }

    /// `str(x)`, `int(x)`, `float(x)` through the Convert constraint.
    pub(crate) fn convert(&mut self, to: &'static str, x: Expr) -> Expr {
        let line = self.line;
        let ret = match to {
            "str" => Type::Str,
            "int" => Type::Int,
            _ => Type::Float,
        };
        if to == "str" {
            return self.show(x);
        }
        let t = x.ty.clone();
        self.dict(Class::Convert(to, ret.clone()), t, vec![x], ret, line)
    }

    fn check_object(&mut self, entries: &[ast::ObjectEntry], expected: Option<&Type>) -> Expr {
        let line = self.line;
        if entries.is_empty() {
            let v = match expected.map(|t| self.shallow(t)) {
                Some(Type::Map(v)) => *v,
                _ => self.fresh(),
            };
            return self.expr(ExprKind::EmptyMap, Type::map(v));
        }
        // {ok: v} / {err: e} build results
        if entries.len() == 1 {
            let (key, value) = match &entries[0] {
                ast::ObjectEntry::KeyValue { key, value } => (key.clone(), Some(value.clone())),
                ast::ObjectEntry::Shorthand(n) => (n.clone(), None),
                ast::ObjectEntry::Spread => ("".into(), None),
            };
            if key == "ok" || key == "err" {
                let (exp_e, exp_a) = match expected.map(|t| self.shallow(t)) {
                    Some(Type::Data(RESULT, args)) => (args[0].clone(), args[1].clone()),
                    _ => (self.fresh(), self.fresh()),
                };
                let inner_expected = if key == "ok" { exp_a.clone() } else { exp_e.clone() };
                let x = match value {
                    Some(v) => self.check_expr(&v, Some(&inner_expected)),
                    None => self.check_identifier(&key, Some(&inner_expected)),
                };
                self.unify(&inner_expected, &x.ty, line);
                let ci = if key == "ok" { 1 } else { 0 };
                return self.expr(ExprKind::Con(RESULT, ci, vec![x]), Type::result(exp_e, exp_a));
            }
        }
        let mut names = Vec::new();
        let mut values = Vec::new();
        for en in entries {
            match en {
                ast::ObjectEntry::KeyValue { key, value } => {
                    let x = self.check_expr(value, None);
                    names.push(key.clone());
                    values.push(x);
                }
                ast::ObjectEntry::Shorthand(n) => {
                    let x = self.check_identifier(n, None);
                    names.push(n.clone());
                    values.push(x);
                }
                ast::ObjectEntry::Spread => {
                    self.error(line, "spreading into a record literal is not supported");
                }
            }
        }
        let id = self.record_shape(names.clone(), line);
        let (t, subst) = self.instantiate_type(id);
        // order the values by the shape's (sorted) field order
        let dt = self.types[id].clone();
        let mut ordered: Vec<Option<Expr>> = (0..dt.ctors[0].fields.len()).map(|_| None).collect();
        for (n, x) in names.iter().zip(values.into_iter()) {
            let idx = dt.field_index(n).unwrap();
            let param = dt.params[idx];
            let fv = subst.iter().find(|(v, _)| *v == param).map(|(_, t)| t.clone()).unwrap();
            self.unify(&fv, &x.ty, line);
            if ordered[idx].is_some() {
                self.error(line, format!("duplicate field {}", n));
            }
            ordered[idx] = Some(x);
        }
        let values: Vec<Expr> = ordered.into_iter().map(|x| x.unwrap()).collect();
        self.expr(ExprKind::Con(id, 0, values), t)
    }

    fn check_binary(&mut self, left: &ast::Expression, op: ast::BinaryOperator, right: &ast::Expression, expected: Option<&Type>) -> Expr {
        use ast::BinaryOperator as B;
        let line = self.line;
        match op {
            B::And | B::Or => {
                let a = self.check_expr(left, None);
                if op == B::And {
                    self.unify(&Type::Bool, &a.ty, line);
                    let b = self.check_expr(right, Some(&Type::Bool));
                    self.unify(&Type::Bool, &b.ty, line);
                    return self.expr(ExprKind::And(Box::new(a), Box::new(b)), Type::Bool);
                }
                // `or`: logical on bools, the default on a maybe
                match self.shallow(&a.ty) {
                    Type::Bool => {
                        let b = self.check_expr(right, Some(&Type::Bool));
                        self.unify(&Type::Bool, &b.ty, line);
                        self.expr(ExprKind::Or(Box::new(a), Box::new(b)), Type::Bool)
                    }
                    Type::Data(MAYBE, args) => {
                        let inner = args[0].clone();
                        let b = self.check_expr(right, Some(&inner));
                        self.unify(&inner, &b.ty, line);
                        self.expr(ExprKind::Builtin("maybe.or".into(), vec![a, b]), inner)
                    }
                    _ => {
                        let b = self.check_expr(right, None);
                        let ret = self.fresh();
                        let t = a.ty.clone();
                        self.dict(Class::OrElse(b.ty.clone(), ret.clone()), t, vec![a, b], ret, line)
                    }
                }
            }
            B::Eq | B::Ne => {
                let a = self.check_expr(left, None);
                let b = self.check_expr(right, Some(&a.ty));
                let (a, b) = self.adapt_literals(a, b);
                self.unify(&a.ty, &b.ty, line);
                let t = a.ty.clone();
                let eq = self.dict(Class::Eq, t, vec![a, b], Type::Bool, line);
                if op == B::Ne { self.expr(ExprKind::Not(Box::new(eq)), Type::Bool) } else { eq }
            }
            B::Lt | B::Le | B::Gt | B::Ge => {
                let a = self.check_expr(left, None);
                let b = self.check_expr(right, Some(&a.ty));
                let (a, b) = self.adapt_literals(a, b);
                self.unify(&a.ty, &b.ty, line);
                let t = a.ty.clone();
                match op {
                    B::Lt => self.dict(Class::Ord, t, vec![a, b], Type::Bool, line),
                    B::Gt => self.dict(Class::Ord, t, vec![b, a], Type::Bool, line),
                    B::Le => {
                        let lt = self.dict(Class::Ord, t, vec![b, a], Type::Bool, line);
                        self.expr(ExprKind::Not(Box::new(lt)), Type::Bool)
                    }
                    _ => {
                        let lt = self.dict(Class::Ord, t, vec![a, b], Type::Bool, line);
                        self.expr(ExprKind::Not(Box::new(lt)), Type::Bool)
                    }
                }
            }
            B::Add | B::Sub | B::Mul | B::Div | B::Mod | B::Pow => {
                let a = self.check_expr(left, expected);
                let aop = match op {
                    B::Add => ArithOp::Add,
                    B::Sub => ArithOp::Sub,
                    B::Mul => ArithOp::Mul,
                    B::Div => ArithOp::Div,
                    B::Mod => ArithOp::Mod,
                    _ => ArithOp::Pow,
                };
                // an operator a class defines: a method call, the right operand free
                if let Type::Data(tid, _) = self.shallow(&a.ty)
                    && !matches!(self.types[tid].kind, DataKind::Builtin)
                        && let Some(m) = self.method_through_parents(tid, aop.symbol()) {
                            let _ = m;
                            return self.method_call_on(a, aop.symbol(), std::slice::from_ref(right), &[], expected, line);
                        }
                let b = self.check_expr(right, Some(&a.ty));
                let (a, b) = self.adapt_literals(a, b);
                self.unify(&a.ty, &b.ty, line);
                let t = a.ty.clone();
                self.dict(Class::Arith(aop), t.clone(), vec![a, b], t, line)
            }
            B::TypeOr | B::TypeAnd | B::BitXor | B::Shl | B::Shr | B::UShr => {
                let a = self.check_expr(left, Some(&Type::Int));
                let b = self.check_expr(right, Some(&Type::Int));
                self.unify(&Type::Int, &a.ty, line);
                self.unify(&Type::Int, &b.ty, line);
                let name = match op {
                    B::TypeOr => "int.or",
                    B::TypeAnd => "int.and",
                    B::BitXor => "int.xor",
                    B::Shl => "int.shl",
                    B::Shr => "int.shr",
                    _ => "int.ushr",
                };
                self.expr(ExprKind::Builtin(name.into(), vec![a, b]), Type::Int)
            }
        }
    }

    /// An int literal next to a float adapts to float.
    fn adapt_literals(&mut self, a: Expr, b: Expr) -> (Expr, Expr) {
        let af = matches!(self.shallow(&a.ty), Type::Float);
        let bf = matches!(self.shallow(&b.ty), Type::Float);
        let a = match (&a.kind, bf) {
            (ExprKind::Lit(Lit::Int(i)), true) => {
                let i = *i;
                self.lit(Lit::Float(i as f64))
            }
            _ => a,
        };
        let b = match (&b.kind, af) {
            (ExprKind::Lit(Lit::Int(i)), true) => {
                let i = *i;
                self.lit(Lit::Float(i as f64))
            }
            _ => b,
        };
        (a, b)
    }

    // -- lambdas and blocks ----------------------------------------------------

    /// A lambda: a new def in the current unit, checked in its own frame.
    pub(crate) fn check_lambda(&mut self, params: &[ast::Param], body: &ast::Expression) -> Expr {
        let line = self.line;
        self.lambda_counter += 1;
        let name = format!("fn{}", self.lambda_counter);
        let unit = Some(self.unit());
        let id = self.new_def(&name, DefKind::Lambda, unit, line);
        self.defs[id].unsafe_ = self.frame_ref().unsafe_;
        self.defs[id].state = State::InProgress;
        let ret = self.fresh();
        self.frames.push(Frame {
            def: id,
            kind: FrameKind::Plain,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: ret.clone(),
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: self.defs[id].unsafe_,
        });
        let own = self.check_params(params, line);
        let defaults: Vec<Option<Expr>> = params.iter().zip(own.iter()).map(|(p, cp)| {
            p.default.as_ref().map(|d| {
                let x = self.check_expr(d, Some(&cp.ty));
                self.unify(&cp.ty, &x.ty, line);
                x
            })
        }).collect();
        let mut param_stmts = Vec::new();
        for (p, ast_p) in own.iter().zip(params.iter()) {
            param_stmts.extend(self.destructure_param(p, &ast_p.pattern));
        }
        let param_types: Vec<Type> = own.iter().map(|p| p.ty.clone()).collect();
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(param_types, Box::new(ret.clone()), c);
        let mono = self.defs[id].mono.clone();
        self.unify(&mono, &fty, line);
        self.defs[id].params = own.clone();
        self.defs[id].defaults = defaults;
        // calls hoisted out of the body stay in the body, not in front of
        // the statement that makes the lambda
        let outer = std::mem::take(&mut self.pending);
        let mut body_block = match body {
            ast::Expression::Block(stmts) => {
                self.hoist_defs(stmts);
                self.check_block_stmts(stmts)
            }
            other => {
                let x = self.check_expr(other, Some(&ret));
                let mut stmts = std::mem::take(&mut self.pending);
                stmts.push(Stmt { kind: StmtKind::Expr(x), line });
                Block { stmts }
            }
        };
        self.pending = outer;
        let mut stmts = param_stmts;
        stmts.append(&mut body_block.stmts);
        body_block.stmts = stmts;
        self.finish_body_value(&mut body_block, line);
        let frame = self.frames.pop().unwrap();
        let captures = frame.captures.clone();
        self.solve_pending();
        let ret = self.join_returns_of(&frame, ret);
        let fty = Type::Fn(own.iter().map(|p| p.ty.clone()).collect(), Box::new(ret.clone()), c);
        let d = &mut self.defs[id];
        d.params = own;
        d.ret = ret;
        d.body = body_block;
        d.captures = captures;
        d.scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: fty.clone() });
        d.state = State::Done;
        self.expr(ExprKind::Lambda(id), fty)
    }

    fn join_returns_of(&mut self, _frame: &Frame, ret: Type) -> Type {
        ret
    }

    /// A block used as a value: its last expression statement.
    pub(crate) fn check_block_expr(&mut self, stmts: &[ast::Stmt], expected: Option<&Type>) -> Expr {
        let line = self.line;
        self.push_scope();
        self.hoist_defs(stmts);
        let mut block = self.check_block_stmts(stmts);
        self.pop_scope();
        let _ = expected;
        if contains_return(&block.stmts) {
            self.error(line, "`return` cannot leave an `if`, `match` or block whose value is used: make it a statement that returns on every path");
        }
        let ty = match self.block_value(&mut block) {
            Some(t) => t,
            None => {
                let n = self.lit(Lit::Nothing);
                block.stmts.push(Stmt { kind: StmtKind::Expr(n), line });
                Type::Unit
            }
        };
        self.expr(ExprKind::Block(block), ty)
    }

    // -- calls ------------------------------------------------------------------

    fn check_call(&mut self, function: &ast::Expression, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        match function {
            ast::Expression::Identifier(name) => {
                match self.lookup(name) {
                    Some(Binding::Func(d)) => return self.call_def(d, name, args, named, expected),
                    Some(Binding::Class(tid)) => {
                        let d = match self.types[tid].kind {
                            DataKind::Class { ctor, .. } => ctor,
                            _ => unreachable!(),
                        };
                        return self.call_def(d, name, args, named, expected);
                    }
                    Some(Binding::Ctor(tid, ci)) => return self.call_ctor(tid, ci, name, args, named, expected),
                    Some(Binding::ModuleMember(m, n)) => return self.call_module(&m, &n, args),
                    Some(Binding::Local { ty, .. }) => {
                        // a named lambda: its defaults may be left out
                        if let Some(d) = self.lookup_hoisted(name)
                            && matches!(self.defs[d].kind, DefKind::Lambda) && self.defs[d].state == State::Done {
                                let f = self.var(name, ty);
                                let params = self.defs[d].params.clone();
                                let xs = self.arrange_args(d, name, &params, args, named, 0);
                                return self.apply(f, xs);
                            }
                    }
                    Some(Binding::Member { .. }) => {}
                    None => {
                        if GLOBALS.contains(&name.as_str()) {
                            return self.call_global(name, args, named, expected);
                        }
                        self.error(line, format!("unknown function '{}'", name));
                        let t = self.fresh();
                        return self.var("__bad", t);
                    }
                }
            }
            ast::Expression::MemberAccess { object, member } => {
                if let ast::Expression::Import(m) = &**object {
                    return self.call_module(m, member, args);
                }
                if let ast::Expression::Identifier(n) = &**object
                    && n == "self"
                        && let FrameKind::Ctor(tid) | FrameKind::Method(tid) = self.frame_ref().kind
                            && let Some(m) = self.method_through_parents(tid, member) {
                                let _ = m;
                                return self.call_def_by_name(member, args, named, expected);
                            }
                return self.check_method_call(object, member, args, named, expected);
            }
            _ => {}
        }
        // a function value
        if !named.is_empty() {
            self.error(line, "keyword arguments need a def or lambda called by name");
        }
        let f = self.check_expr(function, None);
        let mut xs = Vec::new();
        let mut ptys = Vec::new();
        for a in args {
            let x = self.check_expr(a, None);
            ptys.push(x.ty.clone());
            xs.push(x);
        }
        let ret = self.fresh();
        let want = self.store.fresh_fn(ptys, ret.clone());
        self.unify(&f.ty, &want, line);
        self.expr(ExprKind::CallClosure(Box::new(f), xs), ret)
    }

    /// A method of the current class called by bare name (or `self.m`).
    fn call_def_by_name(&mut self, name: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        let tid = match self.frame_ref().kind {
            FrameKind::Ctor(t) => {
                self.error(line, format!("the constructor cannot call the method .{}() while the object is being built", name));
                t
            }
            FrameKind::Method(t) => t,
            _ => unreachable!(),
        };
        let selfe = self.expr(ExprKind::SelfValue(tid), self.class_self_type(tid));
        self.method_call_on(selfe, name, args, named, expected, line)
    }

    /// The def's parameters with the types of one instantiation of its
    /// scheme, so that checking the arguments against them never pins the
    /// def's own variables.
    fn instantiated_params(&self, d: DefId, fty: &Type) -> Vec<Param> {
        let params = self.defs[d].params.clone();
        match self.shallow(fty) {
            Type::Fn(ps, _, _) if ps.len() == params.len() => params.iter().zip(ps.iter()).map(|(p, t)| Param { name: p.name.clone(), ty: t.clone() }).collect(),
            _ => params,
        }
    }

    /// Positional and keyword arguments against a def's parameters, filling
    /// defaults. Returns the argument expressions in parameter order.
    fn arrange_args(&mut self, d: DefId, name: &str, params: &[Param], args: &[ast::Expression], named: &[(String, ast::Expression)], skip: usize) -> Vec<Expr> {
        let line = self.line;
        let own: Vec<Param> = params[skip..].to_vec();
        let defaults = self.defs[d].defaults.clone();
        let mut slots: Vec<Option<Expr>> = own.iter().map(|_| None).collect();
        for (i, a) in args.iter().enumerate() {
            if i >= own.len() {
                self.error(line, format!("{} takes {} argument(s), found {}", name, own.len(), args.len()));
                break;
            }
            let x = self.check_expr(a, Some(&own[i].ty));
            slots[i] = Some(x);
        }
        for (n, a) in named {
            match own.iter().position(|p| &p.name == n) {
                Some(i) => {
                    if slots[i].is_some() {
                        self.error(line, format!("argument {} given twice", n));
                    }
                    let x = self.check_expr(a, Some(&own[i].ty));
                    slots[i] = Some(x);
                }
                None => self.error(line, format!("{} has no parameter named {}", name, n)),
            }
        }
        let mut out = Vec::new();
        for (i, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(x) => out.push(x),
                None => match defaults.get(i + skip).cloned().flatten() {
                    Some(dv) => out.push(dv),
                    None => {
                        self.error(line, format!("{} needs an argument for {}", name, own[i].name));
                        let t = own[i].ty.clone();
                        out.push(self.var("__bad", t));
                    }
                },
            }
        }
        out
    }

    fn call_def(&mut self, d: DefId, name: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        self.ensure_def(d, line);
        self.capture_through(d);
        let nested = self.defs[d].unit != d && !matches!(self.defs[d].kind, DefKind::Method { .. });
        if nested && !self.defs[d].captures.is_empty() && self.defs[d].state == State::Done {
            let f = self.def_value(d, name);
            let params = self.instantiated_params(d, &f.ty);
            let xs = self.arrange_args(d, name, &params, args, named, 0);
            let ret = self.fresh();
            let ptys = xs.iter().map(|x| x.ty.clone()).collect();
            let want = self.store.fresh_fn(ptys, ret.clone());
            self.unify(&f.ty, &want, line);
            return self.expr(ExprKind::CallClosure(Box::new(f), xs), ret);
        }
        if let DefKind::Method { .. } = self.defs[d].kind {
            return self.call_def_by_name(name, args, named, expected);
        }
        let (fty, targs, dicts) = self.instantiate_def_type(d, line);
        let params = self.instantiated_params(d, &fty);
        let xs = self.arrange_args(d, name, &params, args, named, 0);
        let ret = self.fresh();
        let ptys: Vec<Type> = xs.iter().map(|x| x.ty.clone()).collect();
        let want = self.store.fresh_fn(ptys, ret.clone());
        self.unify(&fty, &want, line);
        if let Some(e) = expected {
            let _ = self.store.unify(e, &ret);
        }
        self.note_call(d, line);
        self.expr(ExprKind::Call { def: d, targs, dicts, args: xs }, ret)
    }

    fn call_ctor(&mut self, tid: TypeId, ci: usize, name: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        if !named.is_empty() {
            self.error(line, "constructors take positional arguments");
        }
        let (t, _) = self.instantiate_type(tid);
        let targs = match &t {
            Type::Data(_, a) => a.clone(),
            _ => vec![],
        };
        let ftys = self.ctor_field_types(tid, ci, &targs);
        if ftys.len() != args.len() {
            self.error(line, format!("{} takes {} field(s), found {}", name, ftys.len(), args.len()));
        }
        let mut xs = Vec::new();
        for (a, ft) in args.iter().zip(ftys.iter()) {
            let x = self.check_expr(a, Some(ft));
            self.unify(ft, &x.ty, line);
            xs.push(x);
        }
        if let Some(e) = expected {
            let _ = self.store.unify(e, &t);
        }
        self.expr(ExprKind::Con(tid, ci, xs), t)
    }

    /// `obj.m(args)`: a class method (direct call, with the receiver
    /// rebound when the method mutates) or a builtin/unknown method (a
    /// constraint).
    fn check_method_call(&mut self, object: &ast::Expression, member: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        let recv = self.check_expr(object, None);
        self.method_call_on(recv, member, args, named, expected, line)
    }

    pub(crate) fn method_call_on(&mut self, recv: Expr, member: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>, line: usize) -> Expr {
        let mut recv = recv;
        // a method name that exactly one class declares (and no builtin type
        // has) fixes a receiver whose type is not known yet
        if let Type::Var(_) = self.shallow(&recv.ty) {
            let classes: Vec<TypeId> = self.class_method_names.get(member).cloned().unwrap_or_default();
            if classes.len() == 1 && solve::unique_receiver(&mut self.store, member).is_none() && solve::method_sig(&mut self.store, &Type::Str, member, args.len()).is_none() {
                let tid = classes[0];
                if let DataKind::Class { ctor, .. } = self.types[tid].kind {
                    self.ensure_def(ctor, line);
                }
                let (t, _) = self.instantiate_type(tid);
                self.unify(&recv.ty, &t, line);
            }
        }
        // a dictionary element used as the receiver of a mutation is the
        // element itself (a missing key aborts)
        if matches!(member, "push" | "pop" | "sort" | "set" | "remove" | "delete")
            && let (ExprKind::Dict { .. }, Type::Data(MAYBE, _)) = (&recv.kind, self.shallow(&recv.ty)) {
                self.effect(Effect::ABORT);
                let inner = match self.shallow(&recv.ty) {
                    Type::Data(MAYBE, a) => a[0].clone(),
                    _ => unreachable!(),
                };
                recv = self.expr(ExprKind::Builtin("maybe.unwrap".into(), vec![recv]), inner);
            }
        let rt = self.shallow(&recv.ty);
        if let Type::Data(tid, _) = &rt {
            let tid = *tid;
            if !matches!(self.types[tid].kind, DataKind::Builtin) {
                if let Some(m) = self.method_through_parents(tid, member) {
                    return self.call_class_method(recv, tid, m, member, args, named, expected);
                }
                if !matches!(self.types[tid].kind, DataKind::Record { .. }) {
                    self.error(line, format!("{} has no method .{}()", self.types[tid].name, member));
                }
            }
        }
        // a function-valued field
        if let Type::Data(tid, _) = &rt
            && self.types[*tid].field_index(member).is_some() {
                let f = self.check_member_of(recv.clone(), member);
                if let Type::Fn(..) = self.shallow(&f.ty) {
                    let mut xs = Vec::new();
                    let mut ptys = Vec::new();
                    for a in args {
                        let x = self.check_expr(a, None);
                        ptys.push(x.ty.clone());
                        xs.push(x);
                    }
                    let ret = self.fresh();
                    let want = self.store.fresh_fn(ptys, ret.clone());
                    self.unify(&f.ty, &want, line);
                    return self.expr(ExprKind::CallClosure(Box::new(f), xs), ret);
                }
            }
        if !named.is_empty() {
            self.error(line, "builtin methods take positional arguments");
        }
        let mut xs = Vec::new();
        let mut atys = Vec::new();
        for a in args {
            let x = self.check_expr(a, None);
            atys.push(x.ty.clone());
            xs.push(x);
        }
        let ret = self.fresh();
        let recv_copy = recv.clone();
        let mut all = vec![recv];
        all.extend(xs);
        let subject = all[0].ty.clone();
        let e = self.dict(Class::Method(member.to_string(), atys, ret.clone()), subject, all, ret.clone(), line);
        let _ = expected;
        // `pop` answers (container, value): the container is stored back
        if member == "pop" && self.is_path(&recv_copy) {
            let tmp = self.temp("pop");
            self.pending.push(Stmt { kind: StmtKind::Let { name: tmp.clone(), value: e }, line });
            let ct = self.fresh();
            let vt = self.fresh();
            self.unify(&ret, &Type::pair(ct.clone(), vt.clone()), line);
            let t = self.var(&tmp, ret.clone());
            let cont = self.expr(ExprKind::Field(Box::new(t), PAIR, 0), ct);
            let stmts = self.rebind_path(&recv_copy, cont);
            self.pending.extend(stmts);
            let t = self.var(&tmp, ret);
            return self.expr(ExprKind::Field(Box::new(t), PAIR, 1), vt);
        }
        e
    }

    /// A class method call. A mutating method on a variable hoists the
    /// call in front of the statement and rebinds the variable.
    fn call_class_method(&mut self, recv: Expr, tid: TypeId, m: DefId, member: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        self.ensure_def(m, line);
        let (fty, targs, dicts) = self.instantiate_def_type(m, line);
        let params = self.instantiated_params(m, &fty);
        let mut xs = vec![recv];
        // the receiver seen by the method is the object that owns it
        let owner_ty = self.class_self_type_for_method(m);
        let recv_expr = xs.pop().unwrap();
        let recv_expr = self.receiver_for(recv_expr, tid, m);
        let _ = owner_ty;
        xs.push(recv_expr);
        let rest = self.arrange_args(m, member, &params, args, named, 1);
        xs.extend(rest);
        let ret = self.fresh();
        let ptys: Vec<Type> = xs.iter().map(|x| x.ty.clone()).collect();
        let want = self.store.fresh_fn(ptys, ret.clone());
        self.unify(&fty, &want, line);
        self.note_call(m, line);
        let (mutates, returns_value) = match self.defs[m].kind {
            DefKind::Method { mutates, returns_value, .. } => (mutates, returns_value),
            _ => (false, false),
        };
        let call = self.expr(ExprKind::Call { def: m, targs, dicts, args: xs.clone() }, ret.clone());
        if !mutates {
            if let Some(e) = expected {
                let _ = self.store.unify(e, &ret);
            }
            return call;
        }
        // mutating: the receiver path is rebound to the new object
        let recv_expr = xs[0].clone();
        let tmp = self.temp("m");
        self.pending.push(Stmt { kind: StmtKind::Let { name: tmp.clone(), value: call }, line });
        let new_obj = if returns_value {
            let pair_ty = ret.clone();
            let selft = match self.shallow(&pair_ty) {
                Type::Data(PAIR, a) => a[0].clone(),
                _ => self.fresh(),
            };
            let t = self.var(&tmp, pair_ty);
            self.expr(ExprKind::Field(Box::new(t), PAIR, 0), selft)
        } else {
            self.var(&tmp, ret.clone())
        };
        let rebinds = self.rebind_receiver(&recv_expr, new_obj, tid, m);
        self.pending.extend(rebinds);
        if returns_value {
            let vt = match self.shallow(&ret) {
                Type::Data(PAIR, a) => a[1].clone(),
                _ => self.fresh(),
            };
            let t = self.var(&tmp, ret);
            self.expr(ExprKind::Field(Box::new(t), PAIR, 1), vt)
        } else {
            self.lit(Lit::Nothing)
        }
    }

    // -- members and indexing ------------------------------------------------------

    fn check_member(&mut self, object: &ast::Expression, member: &str) -> Expr {
        let line = self.line;
        if let ast::Expression::Import(m) = object {
            return self.module_value(m, member);
        }
        let recv = self.check_expr(object, None);
        let _ = line;
        self.check_member_of(recv, member)
    }

    pub(crate) fn check_member_of(&mut self, recv: Expr, member: &str) -> Expr {
        let line = self.line;
        let rt = self.shallow(&recv.ty);
        if let Type::Data(tid, _) = &rt {
            let tid = *tid;
            if self.types[tid].field_index(member).is_none()
                && let Some(m) = self.method_through_parents(tid, member) {
                    self.error(line, format!("{}.{} is a method: call it, or wrap it in a lambda", self.types[tid].name, member));
                    let _ = m;
                }
        }
        let ty = self.fresh();
        let subject = recv.ty.clone();
        self.dict(Class::Field(member.to_string(), ty.clone()), subject, vec![recv], ty, line)
    }

    fn check_index(&mut self, object: &ast::Expression, index: &ast::Expression) -> Expr {
        let line = self.line;
        let recv = self.check_expr(object, None);
        if let ast::Expression::Range { start, end } = index {
            // a slice: xs[a..b], xs[..b], xs[a..]
            let s = match start {
                Some(s) => self.check_expr(s, Some(&Type::Int)),
                None => self.lit(Lit::Int(0)),
            };
            let en = match end {
                Some(e) => self.check_expr(e, Some(&Type::Int)),
                None => self.lit(Lit::Int(i32::MAX as i64)),
            };
            let r = self.expr(ExprKind::Con(RANGE, 0, vec![s, en]), Type::range());
            let ret = self.fresh();
            let subject = recv.ty.clone();
            return self.dict(Class::Method("slice".into(), vec![Type::range()], ret.clone()), subject, vec![recv, r], ret, line);
        }
        let idx = self.check_expr(index, None);
        let lit = match &idx.kind {
            ExprKind::Lit(Lit::Int(i)) => Some(*i),
            _ => None,
        };
        let elem = self.fresh();
        let subject = recv.ty.clone();
        // a dictionary element read for a mutation is unwrapped by the caller
        self.dict(Class::Index(idx.ty.clone(), elem.clone(), lit), subject, vec![recv, idx], elem, line)
    }

    // -- control ------------------------------------------------------------------

    fn check_if_expr(&mut self, cond: &ast::Expression, then: &ast::Expression, elifs: &[(ast::Expression, ast::Expression)], else_: Option<&ast::Expression>, expected: Option<&Type>) -> Expr {
        let line = self.line;
        let c = self.check_expr(cond, Some(&Type::Bool));
        self.unify(&Type::Bool, &c.ty, line);
        let t = self.check_expr(then, expected);
        let rest: Expr = if let Some((ec, eb)) = elifs.first() {
            self.check_if_expr(ec, eb, &elifs[1..], else_, expected.or(Some(&t.ty)))
        } else {
            match else_ {
                Some(e) => self.check_expr(e, expected.or(Some(&t.ty))),
                None => {
                    self.error(line, "an `if` used as a value needs an `else`");
                    self.lit(Lit::Nothing)
                }
            }
        };
        let (t, rest, ty) = self.join_branches(t, rest);
        self.expr(ExprKind::If(Box::new(c), Box::new(t), Box::new(rest)), ty)
    }

    /// Two branch values of one expression: they must agree, except that
    /// `nothing` against a value makes a `T | nothing`.
    pub(crate) fn join_branches(&mut self, a: Expr, b: Expr) -> (Expr, Expr, Type) {
        let line = self.line;
        let an = matches!(a.kind, ExprKind::Lit(Lit::Nothing));
        let bn = matches!(b.kind, ExprKind::Lit(Lit::Nothing));
        let at = self.shallow(&a.ty);
        let bt = self.shallow(&b.ty);
        if an && !matches!(bt, Type::Unit) {
            let inner = b.ty.clone();
            let b = self.some(b);
            let none = self.expr(ExprKind::Con(MAYBE, 0, vec![]), Type::maybe(inner.clone()));
            return (none, b, Type::maybe(inner));
        }
        if bn && !matches!(at, Type::Unit) {
            let inner = a.ty.clone();
            let a = self.some(a);
            let none = self.expr(ExprKind::Con(MAYBE, 0, vec![]), Type::maybe(inner.clone()));
            return (a, none, Type::maybe(inner));
        }
        self.unify(&a.ty, &b.ty, line);
        let ty = a.ty.clone();
        (a, b, ty)
    }

    /// Lift a value into `T | nothing`, unless it already is one.
    pub(crate) fn some(&mut self, x: Expr) -> Expr {
        if let Type::Data(MAYBE, _) = self.shallow(&x.ty) {
            return x;
        }
        let t = Type::maybe(x.ty.clone());
        self.expr(ExprKind::Con(MAYBE, 1, vec![x]), t)
    }

    /// `for x in xs [if cond] do body` as a value: a block that pushes onto
    /// an accumulator.
    fn check_comprehension(&mut self, clauses: &[ast::CompClause], body: &ast::Expression) -> Expr {
        let line = self.line;
        let acc = self.temp("acc");
        let elem = self.fresh();
        let empty = self.expr(ExprKind::List(vec![]), Type::list(elem.clone()));
        let mut stmts = vec![Stmt { kind: StmtKind::Let { name: acc.clone(), value: empty }, line }];
        // the innermost loop pushes; an if without else filters
        let (filter, value): (Option<&ast::Expression>, &ast::Expression) = match body {
            ast::Expression::IfExpr { condition, then_branch, elif_branches, else_branch: None } if elif_branches.is_empty() => (Some(condition), then_branch),
            other => (None, other),
        };
        let mut loops: Vec<(Vec<Pat>, Vec<Iter>)> = Vec::new();
        self.push_scope();
        for c in clauses {
            match c {
                ast::CompClause::For { pattern, iterables } => {
                    let (pats, iters) = self.check_for_header(pattern, iterables);
                    loops.push((pats, iters));
                }
            }
        }
        let mut inner = Vec::new();
        let v = self.check_expr(value, Some(&elem));
        self.unify(&elem, &v.ty, line);
        let acc_var = self.var(&acc, Type::list(elem.clone()));
        let pushed = self.dict(Class::Method("push".into(), vec![elem.clone()], Type::list(elem.clone())), Type::list(elem.clone()), vec![acc_var, v], Type::list(elem.clone()), line);
        let push_stmt = Stmt { kind: StmtKind::Assign { name: acc.clone(), value: pushed }, line };
        match filter {
            Some(f) => {
                let c = self.check_expr(f, Some(&Type::Bool));
                self.unify(&Type::Bool, &c.ty, line);
                inner.push(Stmt { kind: StmtKind::If { cond: c, then: Block { stmts: vec![push_stmt] }, else_: Block::default() }, line });
            }
            None => inner.push(push_stmt),
        }
        self.pop_scope();
        let mut body_block = Block { stmts: inner };
        for (pats, iters) in loops.into_iter().rev() {
            body_block = Block { stmts: vec![Stmt { kind: StmtKind::For { patterns: pats, iters, body: body_block }, line }] };
        }
        stmts.extend(body_block.stmts);
        let result = self.var(&acc, Type::list(elem.clone()));
        stmts.push(Stmt { kind: StmtKind::Expr(result), line });
        self.expr(ExprKind::Block(Block { stmts }), Type::list(elem))
    }

    // -- pipelines -----------------------------------------------------------------

    /// The right side of a pipeline operator as a function of the piped
    /// value: a function value, or an expression over `$` wrapped in a
    /// lambda.
    fn stage_function(&mut self, right: &ast::Expression, input: &Type) -> Expr {
        let line = self.line;
        if mentions_dollar(right) {
            // a synthetic lambda `$ => right`
            self.lambda_counter += 1;
            let id = self.new_def(&format!("stage{}", self.lambda_counter), DefKind::Lambda, Some(self.unit()), line);
            self.defs[id].unsafe_ = self.frame_ref().unsafe_;
            self.defs[id].state = State::InProgress;
            let ret = self.fresh();
            self.frames.push(Frame {
                def: id,
                kind: FrameKind::Plain,
                scopes: vec![Scope::default()],
                captures: Vec::new(),
                loop_depth: 0,
                returns: Vec::new(),
                ret: ret.clone(),
                mutates_member: false,
                piped: vec![input.clone()],
                unsafe_: self.defs[id].unsafe_,
            });
            let pname = "__pipe1".to_string();
            self.declare(&pname, Binding::Local { ty: input.clone(), mutable: false });
            let outer = std::mem::take(&mut self.pending);
            let x = self.check_expr(right, None);
            let mut stmts = std::mem::replace(&mut self.pending, outer);
            stmts.push(Stmt { kind: StmtKind::Expr(x), line });
            let mut body = Block { stmts };
            self.finish_body_value(&mut body, line);
            let frame = self.frames.pop().unwrap();
            let captures = frame.captures.clone();
            let c = self.store.clos_singleton(self.defs[id].closure_id);
            let fty = Type::Fn(vec![input.clone()], Box::new(ret.clone()), c);
            let d = &mut self.defs[id];
            d.params = vec![Param { name: pname, ty: input.clone() }];
            d.ret = ret;
            d.body = body;
            d.captures = captures;
            d.scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: fty.clone() });
            d.state = State::Done;
            return self.expr(ExprKind::Lambda(id), fty);
        }
        self.check_expr(right, None)
    }

    fn check_pipeline(&mut self, left: &ast::Expression, op: ast::PipelineOperator, right: &ast::Expression) -> Expr {
        use ast::PipelineOperator as P;
        let line = self.line;
        let l = self.check_expr(left, None);
        if matches!(op, P::Pipe | P::Handle) {
            self.recursive_result(left, &l);
        }
        let lt = self.shallow(&l.ty);
        match op {
            P::Pipe => {
                // a result unwraps into the stage and errs pass along
                if let Type::Data(RESULT, args) = &lt {
                    let (e, a) = (args[0].clone(), args[1].clone());
                    let f = self.stage_function(right, &a);
                    return self.railway(l, f, e, a);
                }
                let f = self.stage_function(right, &l.ty);
                self.apply(f, vec![l])
            }
            P::Map | P::Filter => {
                let (list_ty, wrapped_err) = match &lt {
                    Type::Data(RESULT, args) => (self.shallow(&args[1]), Some(args[0].clone())),
                    other => (other.clone(), None),
                };
                let elem = match &list_ty {
                    Type::List(e) => (**e).clone(),
                    Type::Data(RANGE, _) => Type::Int,
                    Type::Var(_) => {
                        let e = self.fresh();
                        self.unify(&list_ty, &Type::list(e.clone()), line);
                        e
                    }
                    _ => {
                        let s = self.show_type(&l.ty);
                        self.error(line, format!("`{}` needs a list on the left, found {}", if op == P::Map { "*>" } else { "?>" }, s));
                        self.fresh()
                    }
                };
                // per-element railway: a list of results applies the stage to the ok values
                let (inner, elem_err) = match self.shallow(&elem) {
                    Type::Data(RESULT, args) => (args[1].clone(), Some(args[0].clone())),
                    _ => (elem.clone(), None),
                };
                let f = self.stage_function(right, &inner);
                let stage = if op == P::Map { "map" } else { "filter" };
                let f = match &elem_err {
                    Some(e) => self.lift_stage(f, e.clone(), inner.clone(), op == P::Filter),
                    None => f,
                };
                let ft = self.shallow(&f.ty);
                let out_elem = match (&ft, op) {
                    (Type::Fn(_, r, _), P::Map) => match elem_err {
                        Some(e) => {
                            // map over ok values: a stage answering a result binds
                            match self.shallow(r) {
                                Type::Data(RESULT, a) => Type::result(e, a[1].clone()),
                                other => Type::result(e, other),
                            }
                        }
                        None => (**r).clone(),
                    },
                    _ => elem.clone(),
                };
                let base = match wrapped_err {
                    Some(_) => {
                        let inner_list = self.var("__railway", list_ty.clone());
                        let _ = inner_list;
                        l
                    }
                    None => l,
                };
                let recv_ty = if let Type::Data(RANGE, _) = list_ty { Type::range() } else { Type::list(elem.clone()) };
                let recv = if let Type::Data(RESULT, _) = &lt { base } else { base };
                let result_ty = Type::list(out_elem.clone());
                if let Type::Data(RESULT, args) = &lt {
                    let (e, _) = (args[0].clone(), args[1].clone());
                    let stage_call = |ck: &mut Checker, v: Expr| -> Expr {
                        ck.dict(Class::Method(stage.into(), vec![f.ty.clone()], result_ty.clone()), recv_ty.clone(), vec![v, f.clone()], result_ty.clone(), line)
                    };
                    let tmp = self.temp("rw");
                    let v = self.var(&tmp, list_ty.clone());
                    let applied = stage_call(self, v);
                    let done = self.expr(ExprKind::Con(RESULT, 1, vec![applied]), Type::result(e.clone(), result_ty.clone()));
                    let et = self.temp("err");
                    let ev = self.var(&et, e.clone());
                    let fail = self.expr(ExprKind::Con(RESULT, 0, vec![ev]), Type::result(e.clone(), result_ty.clone()));
                    let arms = vec![
                        Arm { pat: Pat::Con(RESULT, 1, vec![Pat::Bind(tmp)]), guard: None, body: done, line },
                        Arm { pat: Pat::Con(RESULT, 0, vec![Pat::Bind(et)]), guard: None, body: fail, line },
                    ];
                    return self.expr(ExprKind::Match(Box::new(recv), arms), Type::result(e, result_ty));
                }
                self.dict(Class::Method(stage.into(), vec![f.ty.clone()], result_ty.clone()), recv_ty, vec![recv, f], result_ty, line)
            }
            P::Handle => {
                match &lt {
                    Type::Data(RESULT, args) => {
                        let (e, a) = (args[0].clone(), args[1].clone());
                        let h = self.handler(right, &e, &a);
                        self.handle_one(l, h, e, a)
                    }
                    Type::List(elem) => match self.shallow(elem) {
                        Type::Data(RESULT, args) => {
                            let (e, a) = (args[0].clone(), args[1].clone());
                            let h = self.handler(right, &e, &a);
                            // per element
                            self.lambda_counter += 1;
                            let hv = self.temp("h");
                            let hl = self.var(&hv, h.ty.clone());
                            let f = self.handle_lambda(hl, e.clone(), a.clone());
                            let out = Type::list(a.clone());
                            let call = self.dict(Class::Method("map".into(), vec![f.ty.clone()], out.clone()), Type::list(elem.as_ref().clone()), vec![l, f], out.clone(), line);
                            let block = Block { stmts: vec![
                                Stmt { kind: StmtKind::Let { name: hv, value: h }, line },
                                Stmt { kind: StmtKind::Expr(call), line },
                            ] };
                            self.expr(ExprKind::Block(block), out)
                        }
                        _ => {
                            self.error(line, "`!>` needs a result (or a list of results) on the left");
                            l
                        }
                    },
                    _ => {
                        self.error(line, "`!>` needs a result (or a list of results) on the left");
                        l
                    }
                }
            }
        }
    }

    /// A recursive call's type is not known while its def is checked. When
    /// the def answers `{ok: ..}` or `{err: ..}` on some path, the call is a
    /// result, so a pipeline over it takes the railway.
    fn recursive_result(&mut self, left: &ast::Expression, l: &Expr) {
        let ast::Expression::Call { function, .. } = left else { return };
        let ast::Expression::Identifier(name) = &**function else { return };
        if !matches!(self.shallow(&l.ty), Type::Var(_)) {
            return;
        }
        let Some(Binding::Func(d)) = self.lookup(name) else { return };
        if !matches!(self.defs[d].state, State::InProgress) {
            return;
        }
        let answers_result = self.defs[d].source.as_ref().is_some_and(|s| stmts_answer_result(&s.body));
        if answers_result {
            let (e, a) = (self.fresh(), self.fresh());
            self.unify(&Type::result(e, a), &l.ty, self.line);
        }
    }

    /// Call a function value with arguments.
    pub(crate) fn apply(&mut self, f: Expr, args: Vec<Expr>) -> Expr {
        let line = self.line;
        let ret = self.fresh();
        let ptys: Vec<Type> = args.iter().map(|a| a.ty.clone()).collect();
        let want = self.store.fresh_fn(ptys, ret.clone());
        self.unify(&f.ty, &want, line);
        self.expr(ExprKind::CallClosure(Box::new(f), args), ret)
    }

    /// `result |> f`: apply f to the ok value; a stage answering a result
    /// binds, one answering a value maps.
    fn railway(&mut self, l: Expr, f: Expr, e: Type, a: Type) -> Expr {
        let line = self.line;
        let tmp = self.temp("ok");
        let v = self.var(&tmp, a.clone());
        let applied = self.apply(f, vec![v]);
        let out_a = match self.shallow(&applied.ty) {
            Type::Data(RESULT, args) => {
                self.unify(&e, &args[0], line);
                args[1].clone()
            }
            other => other,
        };
        let rt = Type::result(e.clone(), out_a.clone());
        let done = match self.shallow(&applied.ty) {
            Type::Data(RESULT, _) => applied,
            _ => self.expr(ExprKind::Con(RESULT, 1, vec![applied]), rt.clone()),
        };
        let et = self.temp("err");
        let ev = self.var(&et, e.clone());
        let fail = self.expr(ExprKind::Con(RESULT, 0, vec![ev]), rt.clone());
        let arms = vec![
            Arm { pat: Pat::Con(RESULT, 1, vec![Pat::Bind(tmp)]), guard: None, body: done, line },
            Arm { pat: Pat::Con(RESULT, 0, vec![Pat::Bind(et)]), guard: None, body: fail, line },
        ];
        self.expr(ExprKind::Match(Box::new(l), arms), rt)
    }

    /// A stage over elements that are results: apply to ok values, pass
    /// errs along (a filter keeps them).
    fn lift_stage(&mut self, f: Expr, e: Type, a: Type, is_filter: bool) -> Expr {
        let line = self.line;
        self.lambda_counter += 1;
        let id = self.new_def(&format!("rail{}", self.lambda_counter), DefKind::Lambda, Some(self.unit()), line);
        self.defs[id].state = State::InProgress;
        let fv = self.temp("f");
        let elem_ty = Type::result(e.clone(), a.clone());
        let p = "__elem".to_string();
        let ret = self.fresh();
        self.frames.push(Frame {
            def: id,
            kind: FrameKind::Plain,
            scopes: vec![Scope::default()],
            captures: vec![(fv.clone(), f.ty.clone())],
            loop_depth: 0,
            returns: Vec::new(),
            ret: ret.clone(),
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: self.frame_ref().unsafe_,
        });
        self.declare(&p, Binding::Local { ty: elem_ty.clone(), mutable: false });
        self.declare(&fv, Binding::Local { ty: f.ty.clone(), mutable: false });
        let subject = self.var(&p, elem_ty.clone());
        let fvar = self.var(&fv, f.ty.clone());
        let ok = self.temp("ok");
        let okv = self.var(&ok, a.clone());
        let applied = self.apply(fvar, vec![okv]);
        let body = if is_filter {
            self.unify(&Type::Bool, &applied.ty, line);
            let et = self.temp("err");
            let keep = self.lit(Lit::Bool(true));
            let arms = vec![
                Arm { pat: Pat::Con(RESULT, 1, vec![Pat::Bind(ok)]), guard: None, body: applied, line },
                Arm { pat: Pat::Con(RESULT, 0, vec![Pat::Bind(et)]), guard: None, body: keep, line },
            ];
            self.unify(&ret, &Type::Bool, line);
            self.expr(ExprKind::Match(Box::new(subject), arms), Type::Bool)
        } else {
            let out_a = match self.shallow(&applied.ty) {
                Type::Data(RESULT, args) => {
                    self.unify(&e, &args[0], line);
                    args[1].clone()
                }
                other => other,
            };
            let rt = Type::result(e.clone(), out_a);
            let done = match self.shallow(&applied.ty) {
                Type::Data(RESULT, _) => applied,
                _ => self.expr(ExprKind::Con(RESULT, 1, vec![applied]), rt.clone()),
            };
            let et = self.temp("err");
            let ev = self.var(&et, e.clone());
            let fail = self.expr(ExprKind::Con(RESULT, 0, vec![ev]), rt.clone());
            let arms = vec![
                Arm { pat: Pat::Con(RESULT, 1, vec![Pat::Bind(ok)]), guard: None, body: done, line },
                Arm { pat: Pat::Con(RESULT, 0, vec![Pat::Bind(et)]), guard: None, body: fail, line },
            ];
            self.unify(&ret, &rt, line);
            self.expr(ExprKind::Match(Box::new(subject), arms), rt)
        };
        let mut block = Block { stmts: vec![Stmt { kind: StmtKind::Expr(body), line }] };
        self.finish_body_value(&mut block, line);
        let frame = self.frames.pop().unwrap();
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(vec![elem_ty.clone()], Box::new(ret.clone()), c);
        let d = &mut self.defs[id];
        d.params = vec![Param { name: p, ty: elem_ty }];
        d.ret = ret;
        d.body = block;
        d.captures = frame.captures;
        d.scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: fty.clone() });
        d.state = State::Done;
        // bind the stage function under the captured name before use
        let lam = self.expr(ExprKind::Lambda(id), fty.clone());
        let block = Block { stmts: vec![
            Stmt { kind: StmtKind::Let { name: fv, value: f }, line },
            Stmt { kind: StmtKind::Expr(lam), line },
        ] };
        self.expr(ExprKind::Block(block), fty)
    }

    /// The handler of `!>`: a function of the error, a stage over `$`, or a
    /// plain value of the ok type.
    fn handler(&mut self, right: &ast::Expression, e: &Type, a: &Type) -> Expr {
        let line = self.line;
        if mentions_dollar(right) {
            return self.stage_function(right, e);
        }
        let x = self.check_expr(right, None);
        match self.shallow(&x.ty) {
            Type::Fn(ps, _, _) if ps.len() == 1 => x,
            _ => {
                // a plain recovery value: wrap in a constant lambda
                self.unify(a, &x.ty, line);
                self.const_lambda(x, e.clone())
            }
        }
    }

    /// `_ => value` as a lambda over the error type.
    fn const_lambda(&mut self, value: Expr, param_ty: Type) -> Expr {
        let line = self.line;
        self.lambda_counter += 1;
        let id = self.new_def(&format!("const{}", self.lambda_counter), DefKind::Lambda, Some(self.unit()), line);
        self.defs[id].state = State::InProgress;
        let vname = self.temp("v");
        let vt = value.ty.clone();
        let p = "__ignored".to_string();
        let body = Block { stmts: vec![Stmt { kind: StmtKind::Return(Expr { kind: ExprKind::Var(vname.clone()), ty: vt.clone(), line }), line }] };
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(vec![param_ty.clone()], Box::new(vt.clone()), c);
        let d = &mut self.defs[id];
        d.params = vec![Param { name: p, ty: param_ty }];
        d.ret = vt.clone();
        d.body = body;
        d.captures = vec![(vname.clone(), vt.clone())];
        d.scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: fty.clone() });
        d.state = State::Done;
        let lam = self.expr(ExprKind::Lambda(id), fty.clone());
        let block = Block { stmts: vec![
            Stmt { kind: StmtKind::Let { name: vname, value }, line },
            Stmt { kind: StmtKind::Expr(lam), line },
        ] };
        self.expr(ExprKind::Block(block), fty)
    }

    /// `match r: Done(v) => v; Fail(e) => h(e)`
    fn handle_one(&mut self, l: Expr, h: Expr, e: Type, a: Type) -> Expr {
        let line = self.line;
        let ok = self.temp("ok");
        let okv = self.var(&ok, a.clone());
        let et = self.temp("err");
        let ev = self.var(&et, e.clone());
        let recovered = self.apply(h, vec![ev]);
        self.unify(&a, &recovered.ty, line);
        let arms = vec![
            Arm { pat: Pat::Con(RESULT, 1, vec![Pat::Bind(ok)]), guard: None, body: okv, line },
            Arm { pat: Pat::Con(RESULT, 0, vec![Pat::Bind(et)]), guard: None, body: recovered, line },
        ];
        self.expr(ExprKind::Match(Box::new(l), arms), a)
    }

    /// A lambda `r => match r ...` handling one result with `h` (a local).
    fn handle_lambda(&mut self, h: Expr, e: Type, a: Type) -> Expr {
        let line = self.line;
        self.lambda_counter += 1;
        let id = self.new_def(&format!("handle{}", self.lambda_counter), DefKind::Lambda, Some(self.unit()), line);
        self.defs[id].state = State::InProgress;
        let hname = match &h.kind {
            ExprKind::Var(n) => n.clone(),
            _ => unreachable!(),
        };
        let elem_ty = Type::result(e.clone(), a.clone());
        let p = "__elem".to_string();
        self.frames.push(Frame {
            def: id,
            kind: FrameKind::Plain,
            scopes: vec![Scope::default()],
            captures: vec![(hname.clone(), h.ty.clone())],
            loop_depth: 0,
            returns: Vec::new(),
            ret: a.clone(),
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: self.frame_ref().unsafe_,
        });
        self.declare(&p, Binding::Local { ty: elem_ty.clone(), mutable: false });
        self.declare(&hname, Binding::Local { ty: h.ty.clone(), mutable: false });
        let subject = self.var(&p, elem_ty.clone());
        let body = self.handle_one(subject, h, e, a.clone());
        let mut block = Block { stmts: vec![Stmt { kind: StmtKind::Expr(body), line }] };
        self.finish_body_value(&mut block, line);
        let frame = self.frames.pop().unwrap();
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(vec![elem_ty.clone()], Box::new(a.clone()), c);
        let d = &mut self.defs[id];
        d.params = vec![Param { name: p, ty: elem_ty }];
        d.ret = a;
        d.body = block;
        d.captures = frame.captures;
        d.scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: fty.clone() });
        d.state = State::Done;
        self.expr(ExprKind::Lambda(id), fty)
    }

    // -- globals and modules ------------------------------------------------------

    fn call_global(&mut self, name: &str, args: &[ast::Expression], named: &[(String, ast::Expression)], expected: Option<&Type>) -> Expr {
        let line = self.line;
        if !named.is_empty() {
            self.error(line, "builtins take positional arguments");
        }
        let n = args.len();
        match name {
            "print" => {
                self.effect(Effect::IO);
                if n == 0 {
                    let e = self.lit(Lit::Str(String::new()));
                    let p = self.expr(ExprKind::Builtin("print".into(), vec![e]), Type::Unit);
                    return p;
                }
                // print answers its first argument
                let first = self.check_expr(&args[0], None);
                let tmp = self.temp("p");
                let ft = first.ty.clone();
                let mut stmts = vec![Stmt { kind: StmtKind::Let { name: tmp.clone(), value: first }, line }];
                let fv = self.var(&tmp, ft.clone());
                let mut shown = vec![self.show(fv)];
                for a in &args[1..] {
                    let x = self.check_expr(a, None);
                    shown.push(self.show(x));
                }
                let p = self.expr(ExprKind::Builtin("print".into(), shown), Type::Unit);
                stmts.push(Stmt { kind: StmtKind::Expr(p), line });
                let result = self.var(&tmp, ft.clone());
                stmts.push(Stmt { kind: StmtKind::Expr(result), line });
                self.expr(ExprKind::Block(Block { stmts }), ft)
            }
            "len" => {
                if n != 1 {
                    self.error(line, "len takes one argument");
                }
                let x = self.check_expr(&args[0], None);
                let t = x.ty.clone();
                self.dict(Class::Len, t, vec![x], Type::Int, line)
            }
            "min" | "max" if n == 2 => {
                let a = self.check_expr(&args[0], None);
                let b = self.check_expr(&args[1], Some(&a.ty));
                let (a, b) = self.adapt_literals(a, b);
                self.unify(&a.ty, &b.ty, line);
                let t = a.ty.clone();
                let ta = self.temp("a");
                let tb = self.temp("b");
                let av = self.var(&ta, t.clone());
                let bv = self.var(&tb, t.clone());
                let (l, r) = if name == "min" { (av.clone(), bv.clone()) } else { (bv.clone(), av.clone()) };
                let lt = self.dict(Class::Ord, t.clone(), vec![l, r], Type::Bool, line);
                let pick = self.expr(ExprKind::If(Box::new(lt), Box::new(av), Box::new(bv)), t.clone());
                let block = Block { stmts: vec![
                    Stmt { kind: StmtKind::Let { name: ta, value: a }, line },
                    Stmt { kind: StmtKind::Let { name: tb, value: b }, line },
                    Stmt { kind: StmtKind::Expr(pick), line },
                ] };
                self.expr(ExprKind::Block(block), t)
            }
            "sum" | "min" | "max" | "abs" | "round" | "sorted" | "reversed" => {
                if n == 0 {
                    self.error(line, format!("{} takes an argument", name));
                    return self.lit(Lit::Nothing);
                }
                let recv = self.check_expr(&args[0], None);
                let rest: Vec<ast::Expression> = args[1..].to_vec();
                self.method_call_on(recv, name, &rest, &[], expected, line)
            }
            "range" => {
                let (s, e) = if n == 1 {
                    let e = self.check_expr(&args[0], Some(&Type::Int));
                    (self.lit(Lit::Int(0)), e)
                } else if n == 2 {
                    let s = self.check_expr(&args[0], Some(&Type::Int));
                    let e = self.check_expr(&args[1], Some(&Type::Int));
                    (s, e)
                } else {
                    self.error(line, "range takes one or two arguments");
                    (self.lit(Lit::Int(0)), self.lit(Lit::Int(0)))
                };
                self.unify(&Type::Int, &s.ty, line);
                self.unify(&Type::Int, &e.ty, line);
                self.expr(ExprKind::Con(RANGE, 0, vec![s, e]), Type::range())
            }
            "error" => {
                self.effect(Effect::ABORT);
                let msg = if n >= 1 {
                    let m = self.check_expr(&args[0], Some(&Type::Str));
                    self.show(m)
                } else {
                    self.lit(Lit::Str("error".into()))
                };
                let t = match expected {
                    Some(t) => t.clone(),
                    None => self.fresh(),
                };
                self.expr(ExprKind::Abort(Box::new(msg)), t)
            }
            "assert" => {
                self.effect(Effect::ABORT);
                let c = if n >= 1 { self.check_expr(&args[0], Some(&Type::Bool)) } else { self.lit(Lit::Bool(true)) };
                self.unify(&Type::Bool, &c.ty, line);
                let msg = if n >= 2 {
                    let m = self.check_expr(&args[1], Some(&Type::Str));
                    self.show(m)
                } else {
                    self.lit(Lit::Str("assertion failed".into()))
                };
                self.expr(ExprKind::Builtin("assert".into(), vec![c, msg]), Type::Unit)
            }
            "str" | "int" | "float" => {
                if n != 1 {
                    self.error(line, format!("{} takes one argument", name));
                    return self.lit(Lit::Nothing);
                }
                let x = self.check_expr(&args[0], None);
                let to: &'static str = match name {
                    "str" => "str",
                    "int" => "int",
                    _ => "float",
                };
                self.convert(to, x)
            }
            _ => unreachable!(),
        }
    }

    /// A global builtin used as a value (`*> len`): a lambda around it.
    fn global_value(&mut self, name: &str) -> Expr {
        let line = self.line;
        let arity = match name {
            "print" | "len" | "sum" | "abs" | "sorted" | "reversed" | "str" | "int" | "float" | "error" | "range" => 1,
            _ => {
                self.error(line, format!("{} cannot be used as a value here; wrap it in a lambda", name));
                return self.lit(Lit::Nothing);
            }
        };
        let params: Vec<ast::Param> = (0..arity).map(|i| ast::Param { is_public: false, is_var: false, pattern: ast::Pattern::Identifier(format!("__g{}", i)), default: None }).collect();
        let args: Vec<ast::Expression> = (0..arity).map(|i| ast::Expression::Identifier(format!("__g{}", i))).collect();
        let body = ast::Expression::Call { function: Box::new(ast::Expression::Identifier(name.to_string())), args, named_args: vec![] };
        self.check_lambda(&params, &body)
    }

    /// The module member table: `$math.sqrt` and friends.
    fn module_sig(&mut self, module: &str, name: &str, nargs: usize) -> Option<(Vec<Type>, Type, Effect)> {
        let pure = Effect::PURE;
        Some(match (module, name) {
            ("math", "pi") | ("math", "e") | ("math", "tau") | ("math", "inf") => (vec![], Type::Float, pure),
            ("math", "sqrt") | ("math", "sin") | ("math", "cos") | ("math", "tan") | ("math", "exp") | ("math", "floor") | ("math", "ceil")
            | ("math", "abs") | ("math", "log2") | ("math", "log10") | ("math", "asin") | ("math", "acos") | ("math", "atan") => (vec![Type::Float], Type::Float, pure),
            ("math", "log") => (if nargs == 1 { vec![Type::Float] } else { vec![Type::Float, Type::Float] }, Type::Float, pure),
            ("math", "pow") | ("math", "atan2") | ("math", "min") | ("math", "max") => (vec![Type::Float, Type::Float], Type::Float, pure),
            ("strings", "join") => (if nargs == 1 { vec![Type::list(Type::Str)] } else { vec![Type::list(Type::Str), Type::Str] }, Type::Str, pure),
            ("strings", "char_code") => (vec![Type::Str], Type::Int, pure),
            ("strings", "from_char_code") => (vec![Type::Int], Type::Str, pure),
            ("lists", "flatten") => {
                let a = self.fresh();
                (vec![Type::list(Type::list(a.clone()))], Type::list(a), pure)
            }
            ("lists", "repeat") => {
                let a = self.fresh();
                (vec![a.clone(), Type::Int], Type::list(a), pure)
            }
            ("lists", "enumerate") => {
                let a = self.fresh();
                (vec![Type::list(a.clone())], Type::list(Type::pair(Type::Int, a)), pure)
            }
            ("lists", "zip") => {
                let a = self.fresh();
                let b = self.fresh();
                (vec![Type::list(a.clone()), Type::list(b.clone())], Type::list(Type::pair(a, b)), pure)
            }
            ("io", "read_file") => (vec![Type::Str], Type::result(Type::Str, Type::Str), Effect::IO),
            ("io", "write_file") => (vec![Type::Str, Type::Str], Type::result(Type::Str, Type::Unit), Effect::IO),
            ("time", "now") => (vec![], Type::Int, Effect::IO),
            _ => return None,
        })
    }

    fn call_module(&mut self, module: &str, name: &str, args: &[ast::Expression]) -> Expr {
        let line = self.line;
        match self.module_sig(module, name, args.len()) {
            Some((ps, ret, eff)) => {
                self.effect(eff);
                if ps.len() != args.len() {
                    self.error(line, format!("${}.{} takes {} argument(s), found {}", module, name, ps.len(), args.len()));
                }
                let mut xs = Vec::new();
                for (a, p) in args.iter().zip(ps.iter()) {
                    let x = self.check_expr(a, Some(p));
                    self.unify(p, &x.ty, line);
                    xs.push(x);
                }
                self.expr(ExprKind::Builtin(format!("{}.{}", module, name), xs), ret)
            }
            None => {
                self.error(line, format!("unknown module member ${}.{}", module, name));
                let t = self.fresh();
                self.var("__bad", t)
            }
        }
    }

    /// A module member as a value: a constant, or a lambda around a function.
    fn module_value(&mut self, module: &str, name: &str) -> Expr {
        let line = self.line;
        match self.module_sig(module, name, 1) {
            Some((ps, ret, _)) if ps.is_empty() => self.expr(ExprKind::Builtin(format!("{}.{}", module, name), vec![]), ret),
            Some((ps, _, _)) => {
                let params: Vec<ast::Param> = (0..ps.len()).map(|i| ast::Param { is_public: false, is_var: false, pattern: ast::Pattern::Identifier(format!("__g{}", i)), default: None }).collect();
                let args: Vec<ast::Expression> = (0..ps.len()).map(|i| ast::Expression::Identifier(format!("__g{}", i))).collect();
                let body = ast::Expression::Call {
                    function: Box::new(ast::Expression::MemberAccess { object: Box::new(ast::Expression::Import(module.to_string())), member: name.to_string() }),
                    args,
                    named_args: vec![],
                };
                self.check_lambda(&params, &body)
            }
            None => {
                self.error(line, format!("unknown module member ${}.{}", module, name));
                let t = self.fresh();
                self.var("__bad", t)
            }
        }
    }
}

/// Whether an expression mentions `$` outside a nested lambda.
pub(crate) fn mentions_dollar(e: &ast::Expression) -> bool {
    use ast::Expression as E;
    match e {
        E::PreviousResult => true,
        E::Identifier(_) | E::Import(_) | E::Number(_) | E::Str(_) | E::TString(_) | E::Boolean(_) | E::Nothing | E::Ellipsis => false,
        E::FString(parts) => parts.iter().any(|p| matches!(p, ast::FStringPart::Expression(x, _) if mentions_dollar(x))),
        E::List(items) => items.iter().any(mentions_dollar),
        E::Object(entries) => entries.iter().any(|en| matches!(en, ast::ObjectEntry::KeyValue { value, .. } if mentions_dollar(value))),
        E::BinaryOp { left, right, .. } => mentions_dollar(left) || mentions_dollar(right),
        E::UnaryOp { operand, .. } => mentions_dollar(operand),
        E::Lambda { .. } => false,
        E::Block(stmts) => stmts.iter().any(stmt_mentions_dollar),
        E::Call { function, args, named_args } => mentions_dollar(function) || args.iter().any(mentions_dollar) || named_args.iter().any(|(_, a)| mentions_dollar(a)),
        E::MemberAccess { object, .. } | E::SpreadMember { object } => mentions_dollar(object),
        E::Index { object, index } => mentions_dollar(object) || mentions_dollar(index),
        E::IfExpr { condition, then_branch, elif_branches, else_branch } => {
            mentions_dollar(condition) || mentions_dollar(then_branch) || elif_branches.iter().any(|(c, b)| mentions_dollar(c) || mentions_dollar(b)) || else_branch.as_ref().is_some_and(|b| mentions_dollar(b))
        }
        E::Comprehension { clauses, body } => {
            clauses.iter().any(|c| match c {
                ast::CompClause::For { iterables, .. } => iterables.iter().any(mentions_dollar),
            }) || mentions_dollar(body)
        }
        E::TypeCheck { expression, .. } => mentions_dollar(expression),
        E::Range { start, end } => start.as_ref().is_some_and(|s| mentions_dollar(s)) || end.as_ref().is_some_and(|e| mentions_dollar(e)),
        E::Pipeline { left, .. } => mentions_dollar(left),
    }
}

fn stmt_mentions_dollar(s: &ast::Stmt) -> bool {
    use ast::Statement as S;
    match &s.node {
        S::Declaration { value, .. } => mentions_dollar(value),
        S::Assignment { value, .. } => mentions_dollar(value),
        S::Return(Some(e)) => mentions_dollar(e),
        S::Expression(e) => mentions_dollar(e),
        S::If { condition, body, elif_branches, else_body } => {
            mentions_dollar(condition) || body.iter().any(stmt_mentions_dollar) || elif_branches.iter().any(|(c, b)| mentions_dollar(c) || b.iter().any(stmt_mentions_dollar)) || else_body.as_ref().is_some_and(|b| b.iter().any(stmt_mentions_dollar))
        }
        S::Match { subject, arms } => mentions_dollar(subject) || arms.iter().any(|a| mentions_dollar(&a.body)),
        S::For { iterables, body, .. } => iterables.iter().any(mentions_dollar) || body.iter().any(stmt_mentions_dollar),
        S::While { condition, body } => mentions_dollar(condition) || body.iter().any(stmt_mentions_dollar),
        _ => false,
    }
}

/// Whether a body answers an `{ok: ..}` / `{err: ..}` literal on some path:
/// its last statement's value, or a `return`.
fn stmts_answer_result(stmts: &[ast::Stmt]) -> bool {
    use ast::Statement as S;
    let returns = |ss: &[ast::Stmt]| stmts_return_result(ss);
    if returns(stmts) {
        return true;
    }
    match stmts.last().map(|s| &s.node) {
        Some(S::Expression(e)) => expr_answers_result(e),
        Some(S::If { body, elif_branches, else_body, .. }) => {
            stmts_answer_result(body) || elif_branches.iter().any(|(_, b)| stmts_answer_result(b)) || else_body.as_ref().is_some_and(|b| stmts_answer_result(b))
        }
        Some(S::Match { arms, .. }) => arms.iter().any(|a| expr_answers_result(&a.body)),
        _ => false,
    }
}

/// A `return {ok: ..}` / `return {err: ..}` anywhere in the statements.
fn stmts_return_result(stmts: &[ast::Stmt]) -> bool {
    use ast::Statement as S;
    stmts.iter().any(|s| match &s.node {
        S::Return(Some(e)) => expr_answers_result(e),
        S::If { body, elif_branches, else_body, .. } => {
            stmts_return_result(body) || elif_branches.iter().any(|(_, b)| stmts_return_result(b)) || else_body.as_ref().is_some_and(|b| stmts_return_result(b))
        }
        S::Match { arms, .. } => arms.iter().any(|a| matches!(&a.body, ast::Expression::Block(b) if stmts_return_result(b))),
        S::For { body, .. } | S::While { body, .. } => stmts_return_result(body),
        _ => false,
    })
}

fn expr_answers_result(e: &ast::Expression) -> bool {
    match e {
        ast::Expression::Object(entries) if entries.len() == 1 => match &entries[0] {
            ast::ObjectEntry::KeyValue { key, .. } | ast::ObjectEntry::Shorthand(key) => key == "ok" || key == "err",
            ast::ObjectEntry::Spread => false,
        },
        ast::Expression::Block(stmts) => stmts_answer_result(stmts),
        ast::Expression::IfExpr { then_branch, elif_branches, else_branch, .. } => {
            expr_answers_result(then_branch) || elif_branches.iter().any(|(_, b)| expr_answers_result(b)) || else_branch.as_ref().is_some_and(|b| expr_answers_result(b))
        }
        _ => false,
    }
}
