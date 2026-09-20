// src/bend/infer/exprs.rs
// Expressions, lambdas, calls, patterns, and type expressions.

use super::stmts::{int_lit, is_constructor, param_name};
use super::*;

impl Infer {
    pub(super) fn infer_expr(&mut self, e: &ast::Expression, line: usize) -> TExpr {
        use ast::Expression as E;
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        match e {
            E::Identifier(name) => self.infer_identifier(name, line),
            E::PreviousResult => self.infer_identifier("$", line),
            E::Import(name) => {
                self.error(line, format!("a module (${}) can only be used with .member access or destructuring", name));
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            E::ImportFile(_) => {
                self.error(line, "user-file imports are not supported");
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            E::Number(n) => self.infer_number(n, line),
            E::Str(s) | E::TString(s) => mk(TExprKind::Lit(Lit::Str(s.clone())), Type::Str),
            E::FString(parts) => {
                let mut out = Vec::new();
                for p in parts {
                    match p {
                        ast::FStringPart::Text(t) => out.push(FPart::Text(t.clone())),
                        ast::FStringPart::Expression(x, spec) => {
                            let v = self.infer_expr(x, line);
                            out.push(FPart::Expr(v, spec.clone()));
                        }
                    }
                }
                mk(TExprKind::FString(out), Type::Str)
            }
            E::Boolean(b) => mk(TExprKind::Lit(Lit::Bool(*b)), Type::Bool),
            E::Nothing => mk(TExprKind::Lit(Lit::Nothing), Type::Unit),
            E::Ellipsis => {
                self.error(line, "unexpected '...'");
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            E::List(items) if items.iter().any(|i| matches!(i, E::UnaryOp { op: ast::UnaryOperator::Spread, .. })) => {
                // [...xs, y, ...zs] is a concatenation
                let elem = self.store.fresh();
                let mut parts: Vec<TExpr> = Vec::new();
                let mut run: Vec<TExpr> = Vec::new();
                let list_ty = Type::list(elem.clone());
                for it in items {
                    if let E::UnaryOp { op: ast::UnaryOperator::Spread, operand } = it {
                        if !run.is_empty() {
                            parts.push(mk(TExprKind::List(std::mem::take(&mut run)), list_ty.clone()));
                        }
                        let v = self.infer_expr(operand, line);
                        self.unify(&v.ty, &list_ty, line, "spread");
                        parts.push(v);
                    } else {
                        let v = self.infer_expr(it, line);
                        let v = self.coerce_join(v, &elem, line);
                        self.unify(&elem, &v.ty, line, "list element");
                        run.push(v);
                    }
                }
                if !run.is_empty() {
                    parts.push(mk(TExprKind::List(run), list_ty.clone()));
                }
                mk(TExprKind::Builtin("list_concat".into(), parts), list_ty)
            }
            E::List(items) => {
                let elem = self.store.fresh();
                let mut out = Vec::new();
                for it in items {
                    let v = self.infer_expr(it, line);
                    let v = self.coerce_join(v, &elem, line);
                    self.join_into(&elem, &v.ty, line);
                    out.push(v);
                }
                // re-lift earlier plain elements if a later one made it maybe
                let elem_r = self.store.shallow(&elem);
                let out: Vec<TExpr> = out.into_iter().map(|v| self.coerce_join(v, &elem_r, line)).collect();
                mk(TExprKind::List(out), Type::list(elem))
            }
            E::Object(entries) => self.infer_object(entries, line),
            E::BinaryOp { left, op, right } => self.infer_binary(*op, left, right, line),
            E::UnaryOp { op, operand } => {
                let v = self.infer_expr(operand, line);
                match op {
                    ast::UnaryOperator::Not => mk(TExprKind::Not(Box::new(v)), Type::Bool),
                    ast::UnaryOperator::Minus => {
                        self.defer(Pending::Numeric { ty: v.ty.clone(), line });
                        let ty = v.ty.clone();
                        mk(TExprKind::Neg(Box::new(v)), ty)
                    }
                    ast::UnaryOperator::Plus => v,
                    ast::UnaryOperator::Spread => {
                        self.error(line, "spread is only valid in list patterns");
                        v
                    }
                }
            }
            E::Lambda { params, body } => self.infer_lambda(params, body, None, line),
            E::Block(stmts) => self.infer_block_expr(stmts, line),
            E::Call { function, args, named_args } => self.infer_call(function, args, named_args, line),
            E::MemberAccess { object, member, safe } => {
                if *safe {
                    self.error(line, "?. is not supported; match on `T | nothing` instead");
                }
                self.infer_member_access(object, member, line)
            }
            E::SpreadMember { .. } => {
                self.error(line, "`.{...}` is only valid as `self.{...} = parent`");
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            E::Index { object, index } => {
                let obj = self.infer_expr(object, line);
                let idx = self.infer_expr(index, line);
                let lit = match &idx.kind {
                    TExprKind::Lit(Lit::Int(n)) => Some(*n),
                    _ => None,
                };
                // pair[0] / pair[1]: the key / value of a dictionary entry
                if let (Type::Record(PAIR_REC, args), Some(i @ (0 | 1))) = (self.store.shallow(&obj.ty), lit) {
                    let ty = args[i as usize].clone();
                    return mk(TExprKind::Field(Box::new(obj), PAIR_REC, i as usize), ty);
                }
                let ret = self.store.fresh();
                self.defer(Pending::Index { recv: obj.ty.clone(), idx: idx.ty.clone(), ret: ret.clone(), lit, line });
                self.resolve_pending(false);
                let is_slice = matches!(self.store.shallow(&idx.ty), Type::Range | Type::Stream(_));
                let name = if is_slice { "slice" } else { "index" };
                mk(TExprKind::Builtin(name.into(), vec![obj, idx]), ret)
            }
            E::IfExpr { condition, then_branch, elif_branches, else_branch } => {
                let cond = self.infer_expr(condition, line);
                let result = self.store.fresh();
                let then = self.infer_expr(then_branch, line);
                let then = self.coerce_join(then, &result, line);
                self.join_into(&result, &then.ty, line);
                let mut else_expr: Option<TExpr> = else_branch.as_ref().map(|b| self.infer_expr(b, line));
                // elifs nest into the else
                for (c, b) in elif_branches.iter().rev() {
                    let c = self.infer_expr(c, line);
                    let b = self.infer_expr(b, line);
                    let b = self.coerce_join(b, &result, line);
                    self.join_into(&result, &b.ty, line);
                    let e = match else_expr.take() {
                        Some(e) => e,
                        None => mk(TExprKind::Lit(Lit::Nothing), Type::Unit),
                    };
                    let e = self.coerce_join(e, &result, line);
                    self.join_into(&result, &e.ty, line);
                    let rt = self.store.resolve(&result);
                    else_expr = Some(mk(TExprKind::If { cond: Box::new(c), then: Box::new(b), else_: Box::new(e) }, rt));
                }
                let else_ = match else_expr {
                    Some(e) => e,
                    None => mk(TExprKind::Lit(Lit::Nothing), Type::Unit),
                };
                let else_ = self.coerce_join(else_, &result, line);
                self.join_into(&result, &else_.ty, line);
                let rt = self.store.shallow(&result);
                let then = self.coerce_join(then, &rt, line);
                let else_ = self.coerce_join(else_, &rt, line);
                mk(TExprKind::If { cond: Box::new(cond), then: Box::new(then), else_: Box::new(else_) }, result)
            }
            E::Comprehension { clauses, body } => self.infer_comprehension(clauses, body, line),
            E::TypeCheck { expression, type_expr } => {
                let v = self.infer_expr(expression, line);
                let t = self.type_from_expr(type_expr, line);
                let v = self.coerce_join(v, &t, line);
                self.unify(&t, &v.ty, line, "type assertion");
                v
            }
            E::Range { start, end } => {
                let s = match start {
                    Some(s) => self.infer_expr(s, line),
                    None => int_lit(0, line),
                };
                self.unify(&s.ty, &Type::Int, line, "range start");
                match end {
                    Some(e) => {
                        let e = self.infer_expr(e, line);
                        self.unify(&e.ty, &Type::Int, line, "range end");
                        mk(TExprKind::Range { start: Box::new(s), end: Some(Box::new(e)) }, Type::Range)
                    }
                    None => mk(TExprKind::Range { start: Box::new(s), end: None }, Type::stream(Type::Int)),
                }
            }
            E::Await(_) | E::Async(_) => {
                self.error(line, "async/await are not supported");
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            E::Pipeline { left, op, right } => self.infer_pipeline(left, *op, right, line),
        }
    }

    fn infer_number(&mut self, n: &ast::NumberLiteral, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        match n {
            ast::NumberLiteral::Decimal(s) => {
                let clean: String = s.chars().filter(|c| *c != '_').collect();
                if clean.contains('.') {
                    mk(TExprKind::Lit(Lit::Float(clean.parse().unwrap_or(0.0))), Type::Float)
                } else {
                    match clean.parse::<i64>() {
                        Ok(v) => mk(TExprKind::Lit(Lit::Int(v)), Type::Int),
                        Err(_) => mk(TExprKind::Lit(Lit::Float(clean.parse().unwrap_or(0.0))), Type::Float),
                    }
                }
            }
            ast::NumberLiteral::Hex(s) => {
                let v = i64::from_str_radix(s.trim_start_matches("0x").trim_start_matches("0X"), 16).unwrap_or(0);
                mk(TExprKind::Lit(Lit::Int(v)), Type::Int)
            }
            ast::NumberLiteral::Binary(s) => {
                let v = i64::from_str_radix(s.trim_start_matches("0b").trim_start_matches("0B"), 2).unwrap_or(0);
                mk(TExprKind::Lit(Lit::Int(v)), Type::Int)
            }
            ast::NumberLiteral::Scientific(s) => mk(TExprKind::Lit(Lit::Float(s.parse().unwrap_or(0.0))), Type::Float),
            ast::NumberLiteral::Imaginary(_) => {
                self.error(line, "imaginary numbers are not supported");
                mk(TExprKind::Lit(Lit::Int(0)), Type::Int)
            }
        }
    }

    fn infer_identifier(&mut self, name: &str, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        if name == "self" {
            match self.frames.last().unwrap().kind {
                FrameKind::Ctor(rec) | FrameKind::Method(rec) => {
                    let ty = Type::Record(rec, self.records[rec].field_vars.clone());
                    return mk(TExprKind::SelfValue(rec), ty);
                }
                _ => {
                    self.error(line, "`self` outside a constructor or method");
                    return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
                }
            }
        }
        match self.lookup(name, line) {
            Some(Binding::Local { ty, .. }) => mk(TExprKind::Local(name.to_string()), ty),
            Some(Binding::Member { path, ty, .. }) => {
                let e = self.member_path_read(&path, line);
                let _ = ty;
                e
            }
            Some(Binding::Func { def }) => {
                let ty = self.def_value_type(def, line);
                // a method referenced by bare name inside its class: bind self
                if let Some(Some(TDef { kind: DefKind::Method { .. }, .. })) = self.defs.get(def) {
                    if let Type::Fn(params, r, _) = self.store.shallow(&ty) {
                        let f = self.store.fresh_fn(params[1..].to_vec(), (*r).clone());
                        let recv = self.self_expr(line);
                        return mk(TExprKind::Member(Box::new(recv), name.to_string()), f);
                    }
                }
                mk(TExprKind::DefRef(def), ty)
            }
            Some(Binding::Class(rec)) => {
                let ctor = match &self.records[rec].kind {
                    RecordKind::Class { ctor, .. } => *ctor,
                    _ => unreachable!(),
                };
                let ty = self.def_value_type(ctor, line);
                mk(TExprKind::DefRef(ctor), ty)
            }
            Some(Binding::ModuleMember(module, member)) => match sigs::module_member(&mut self.store, &module, &member, 1) {
                Some(t @ Type::Fn(..)) => {
                    // a module function as a value: a lambda calling it
                    let n = match &t {
                        Type::Fn(ps, _, _) => ps.len(),
                        _ => 1,
                    };
                    self.module_fn_as_value(&module, &member, n, line)
                }
                Some(t) => mk(TExprKind::Builtin(format!("{}.{}", module, member), vec![]), t),
                None => mk(TExprKind::Lit(Lit::Nothing), Type::Unit),
            },
            Some(Binding::TypeAlias(_)) => {
                self.error(line, format!("'{}' is a type, not a value", name));
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            None => {
                if BUILTIN_GLOBALS.contains(&name) {
                    // a builtin used as a value: wrap as a lambda-like value
                    return self.builtin_as_value(name, line);
                }
                self.error(line, format!("undefined name '{}'", name));
                mk(TExprKind::Lit(Lit::Nothing), self.store.fresh())
            }
        }
    }

    /// The receiver value inside a method (rebuilt from member locals) or
    /// the object under construction.
    pub(super) fn self_expr(&mut self, line: usize) -> TExpr {
        match self.frames.last().unwrap().kind {
            FrameKind::Ctor(rec) | FrameKind::Method(rec) => {
                let ty = Type::Record(rec, self.records[rec].field_vars.clone());
                TExpr { kind: TExprKind::SelfValue(rec), ty, line }
            }
            _ => {
                // a lambda inside a method: `self` is captured
                match self.lookup("self", line) {
                    Some(Binding::Local { ty, .. }) => TExpr { kind: TExprKind::Local("self".into()), ty, line },
                    _ => {
                        self.error(line, "method reference outside its class");
                        TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line }
                    }
                }
            }
        }
    }

    /// `$math.sqrt` used as a value: a synthetic lambda calling it.
    fn module_fn_as_value(&mut self, module: &str, member: &str, nargs: usize, line: usize) -> TExpr {
        let names: Vec<String> = (0..nargs).map(|i| format!("__x{}", i)).collect();
        let body = ast::Expression::Call {
            function: Box::new(ast::Expression::MemberAccess { object: Box::new(ast::Expression::Import(module.to_string())), member: member.to_string(), safe: false }),
            args: names.iter().map(|n| ast::Expression::Identifier(n.clone())).collect(),
            named_args: vec![],
        };
        let params = names.into_iter().map(|n| ast::Param { is_public: false, is_var: false, pattern: ast::Pattern::Identifier(n), default: None }).collect::<Vec<_>>();
        self.infer_lambda(&params, &body, None, line)
    }

    /// `print`, `len`, ... used as a value (e.g. `|> print`, `*> str`):
    /// a synthetic one-argument lambda.
    fn builtin_as_value(&mut self, name: &str, line: usize) -> TExpr {
        let param = "__x".to_string();
        let body = ast::Expression::Call {
            function: Box::new(ast::Expression::Identifier(name.to_string())),
            args: vec![ast::Expression::Identifier(param.clone())],
            named_args: vec![],
        };
        let params = vec![ast::Param { is_public: false, is_var: false, pattern: ast::Pattern::Identifier(param), default: None }];
        self.infer_lambda(&params, &body, None, line)
    }

    fn infer_object(&mut self, entries: &[ast::ObjectEntry], line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        if entries.is_empty() {
            let v = self.store.fresh();
            return mk(TExprKind::EmptyMap, Type::map(v));
        }
        let mut names = Vec::new();
        let mut values = Vec::new();
        for en in entries {
            match en {
                ast::ObjectEntry::KeyValue { key, value } => {
                    names.push(key.clone());
                    values.push(self.infer_expr(value, line));
                }
                ast::ObjectEntry::Shorthand(n) => {
                    names.push(n.clone());
                    values.push(self.infer_identifier(n, line));
                }
                ast::ObjectEntry::Spread => {
                    self.error(line, "object spread is not supported");
                }
            }
        }
        // results
        if names.len() == 1 && names[0] == "ok" {
            let v = values.pop().unwrap();
            let e = self.store.fresh();
            let ty = Type::result(e, v.ty.clone());
            return mk(TExprKind::MakeOk(Box::new(v)), ty);
        }
        if names.len() == 1 && names[0] == "err" {
            let v = values.pop().unwrap();
            let a = self.store.fresh();
            let ty = Type::result(v.ty.clone(), a);
            return mk(TExprKind::MakeErr(Box::new(v)), ty);
        }
        let (rec, args) = self.literal_shape(&names);
        for (v, a) in values.iter().zip(args.iter()) {
            self.unify(a, &v.ty, line, "field");
        }
        mk(TExprKind::MakeRecord(rec, values), Type::Record(rec, args))
    }

    fn infer_binary(&mut self, op: ast::BinaryOperator, left: &ast::Expression, right: &ast::Expression, line: usize) -> TExpr {
        use ast::BinaryOperator as B;
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        match op {
            B::And | B::Or => {
                let a = self.infer_expr(left, line);
                let b = self.infer_expr(right, line);
                // `x or default` on a maybe: unwrap
                let at = self.store.shallow(&a.ty);
                let bt = self.store.shallow(&b.ty);
                if op == B::Or {
                    if let Type::Maybe(inner) = &at {
                        if !matches!(bt, Type::Maybe(_) | Type::Var(_) | Type::Unit) {
                            self.unify(inner, &b.ty, line, "or");
                            let ty = (**inner).clone();
                            return mk(TExprKind::Builtin("maybe_or".into(), vec![a, b]), ty);
                        }
                    }
                    // the left side is not known yet (a parameter): decide later
                    if let Type::Var(_) = &at {
                        let ret = self.store.fresh();
                        self.defer(Pending::Or { lhs: a.ty.clone(), rhs: b.ty.clone(), ret: ret.clone(), line });
                        self.resolve_pending(false);
                        return mk(TExprKind::Builtin("or_dyn".into(), vec![a, b]), ret);
                    }
                }
                let b = self.coerce_join(b, &a.ty, line);
                let a = self.coerce_join(a, &b.ty, line);
                self.join_into(&a.ty, &b.ty, line);
                let ty = a.ty.clone();
                if op == B::And {
                    mk(TExprKind::And(Box::new(a), Box::new(b)), ty)
                } else {
                    mk(TExprKind::Or(Box::new(a), Box::new(b)), ty)
                }
            }
            B::TypeOr | B::TypeAnd => {
                self.error(line, "type expressions are only valid in annotations");
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            _ => {
                let a = self.infer_expr(left, line);
                let b = self.infer_expr(right, line);
                let bop = match op {
                    B::Add => BinOp::Add,
                    B::Sub => BinOp::Sub,
                    B::Mul => BinOp::Mul,
                    B::Div => BinOp::Div,
                    B::Mod => BinOp::Mod,
                    B::Pow => BinOp::Pow,
                    B::Eq => BinOp::Eq,
                    B::Ne => BinOp::Ne,
                    B::Lt => BinOp::Lt,
                    B::Le => BinOp::Le,
                    B::Gt => BinOp::Gt,
                    B::Ge => BinOp::Ge,
                    _ => unreachable!(),
                };
                self.binop(bop, a, b, line)
            }
        }
    }

    pub(super) fn binop(&mut self, op: BinOp, a: TExpr, b: TExpr, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        // int literals next to floats become float literals
        let (a, b) = if matches!(self.store.shallow(&a.ty), Type::Float) {
            let b = self.coerce_join(b, &Type::Float, line);
            (a, b)
        } else if matches!(self.store.shallow(&b.ty), Type::Float) {
            let a = self.coerce_join(a, &Type::Float, line);
            (a, b)
        } else {
            (a, b)
        };
        if op.is_comparison() {
            // comparing with nothing: is_none / is_some
            let at = self.store.shallow(&a.ty);
            let bt = self.store.shallow(&b.ty);
            if matches!(op, BinOp::Eq | BinOp::Ne) {
                let a_nothing = matches!(at, Type::Unit) && matches!(a.kind, TExprKind::Lit(Lit::Nothing));
                let b_nothing = matches!(bt, Type::Unit) && matches!(b.kind, TExprKind::Lit(Lit::Nothing));
                if b_nothing && !a_nothing {
                    let m = Type::maybe(self.store.fresh());
                    let a = self.coerce_join(a, &m, line);
                    let name = if op == BinOp::Eq { "is_nothing" } else { "is_something" };
                    return mk(TExprKind::Builtin(name.into(), vec![a]), Type::Bool);
                }
                if a_nothing && !b_nothing {
                    let m = Type::maybe(self.store.fresh());
                    let b = self.coerce_join(b, &m, line);
                    let name = if op == BinOp::Eq { "is_nothing" } else { "is_something" };
                    return mk(TExprKind::Builtin(name.into(), vec![b]), Type::Bool);
                }
            }
            let b = self.coerce_join(b, &a.ty, line);
            let a = self.coerce_join(a, &b.ty, line);
            self.unify(&a.ty, &b.ty, line, "comparison operands");
            if !matches!(op, BinOp::Eq | BinOp::Ne) {
                self.defer(Pending::Numeric { ty: a.ty.clone(), line });
                // strings compare too: drop the numeric constraint for str
                if let Type::Str = self.store.shallow(&a.ty) {
                    self.pending.pop();
                }
            }
            return mk(TExprKind::BinOp(op, Box::new(a), Box::new(b)), Type::Bool);
        }
        // custom operators: the left operand's class decides
        if let Type::Record(rec, _) = self.store.shallow(&a.ty) {
            let sym = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                BinOp::Pow => "**",
                _ => unreachable!(),
            };
            if self.find_method(rec, sym).is_none() {
                self.error(line, format!("{} has no operator {}", self.records[rec].name, sym));
            }
            return self.method_call(a, sym, vec![b], line);
        }
        self.unify(&a.ty, &b.ty, line, "arithmetic operands");
        self.defer(Pending::Arith { ty: a.ty.clone(), op, line });
        let ty = a.ty.clone();
        mk(TExprKind::BinOp(op, Box::new(a), Box::new(b)), ty)
    }

    // -- lambdas and calls ---------------------------------------------------

    /// A lambda expression. `bound_name` is set when the lambda is the
    /// direct value of a named binding (so it can recurse by that name and
    /// becomes a method inside a constructor).
    pub(super) fn infer_lambda(&mut self, params: &[ast::Param], body: &ast::Expression, bound_name: Option<(&str, bool)>, line: usize) -> TExpr {
        let (name, is_public) = match bound_name {
            Some((n, p)) => (n.to_string(), p),
            None => (self.fresh_name("lam"), false),
        };
        let kind = match self.frames.last().unwrap().kind {
            FrameKind::Ctor(rec) if bound_name.is_some() => {
                if is_public || self.references_members_expr(rec, params, body) {
                    DefKind::Method { rec, mutates: false }
                } else {
                    DefKind::Lambda
                }
            }
            _ => DefKind::Lambda,
        };
        let id = self.new_def(&name, kind.clone(), line);
        if let DefKind::Method { rec, .. } = kind {
            if let RecordKind::Class { methods, .. } = &mut self.records[rec].kind {
                methods.push((name.clone(), id));
            }
        }
        if bound_name.is_some() {
            self.declare(&name, Binding::Func { def: id });
        }
        // a block body is a statement list; anything else is an expression
        match body {
            ast::Expression::Block(stmts) => self.infer_function(id, &name, kind.clone(), params, None, Some(stmts), None, line),
            other => self.infer_function(id, &name, kind.clone(), params, None, None, Some(other), line),
        }
        let ty = self.def_value_type(id, line);
        if let DefKind::Method { .. } = kind {
            // as a value: bound to self
            if let Type::Fn(ps, r, _) = self.store.shallow(&ty) {
                let f = self.store.fresh_fn(ps[1..].to_vec(), (*r).clone());
                let recv = self.self_expr(line);
                return TExpr { kind: TExprKind::Member(Box::new(recv), name), ty: f, line };
            }
        }
        TExpr { kind: TExprKind::Lambda(id), ty, line }
    }

    fn infer_block_expr(&mut self, stmts: &[ast::Stmt], line: usize) -> TExpr {
        let mut b = self.infer_block(stmts);
        self.tail_to_expr(&mut b);
        let ty = match b.stmts.last() {
            Some(TStmt { kind: TStmtKind::Expr(v), .. }) => v.ty.clone(),
            _ => Type::Unit,
        };
        if b.stmts.is_empty() {
            b.stmts.push(TStmt { kind: TStmtKind::Expr(TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line }), line });
        }
        TExpr { kind: TExprKind::Block(b), ty, line }
    }

    fn infer_call(&mut self, function: &ast::Expression, args: &[ast::Expression], named: &[(String, ast::Expression)], line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        // module members: $math.sqrt(x)
        if let ast::Expression::MemberAccess { object, member, .. } = function {
            if let ast::Expression::Import(module) = &**object {
                let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                return self.module_call(module, member, targs, line);
            }
            // method call; a class name as receiver is a namespace
            let recv = match &**object {
                ast::Expression::Identifier(n) if matches!(self.lookup(n, line), Some(Binding::Class(_))) => {
                    let rec = match self.lookup(n, line) {
                        Some(Binding::Class(r)) => r,
                        _ => unreachable!(),
                    };
                    let ctor = match &self.records[rec].kind {
                        RecordKind::Class { ctor, .. } => *ctor,
                        _ => unreachable!(),
                    };
                    self.direct_call(ctor, vec![], line)
                }
                other => self.infer_expr(other, line),
            };
            let mut targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
            if !named.is_empty() {
                // keyword args on a known class method
                let rt = self.store.shallow(&recv.ty);
                if let Type::Record(rec, _) = rt {
                    if let Some(def) = self.find_method(rec, member) {
                        targs = self.fill_named_args(def, targs, named, true, line);
                    } else {
                        self.error(line, "keyword arguments need a user-defined method");
                    }
                } else {
                    self.error(line, "keyword arguments need a user-defined function");
                }
            }
            return self.method_call(recv, member, targs, line);
        }
        // builtins and globals
        if let ast::Expression::Identifier(name) = function {
            let binding = self.lookup(name, line);
            match binding {
                None if BUILTIN_GLOBALS.contains(&name.as_str()) => {
                    let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                    return self.global_call(name, targs, line);
                }
                Some(Binding::Func { def }) => {
                    let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                    let is_method = matches!(self.defs.get(def), Some(Some(TDef { kind: DefKind::Method { .. }, .. })))
                        || self.frames.iter().any(|f| f.def == def && matches!(f.kind, FrameKind::Method(_)));
                    let targs = self.fill_named_args(def, targs, named, is_method, line);
                    if is_method {
                        let recv = self.self_expr(line);
                        return self.method_call(recv, name, targs, line);
                    }
                    let def = self.template_instance(def, &targs, line);
                    return self.direct_call(def, targs, line);
                }
                Some(Binding::Class(rec)) => {
                    let ctor = match &self.records[rec].kind {
                        RecordKind::Class { ctor, .. } => *ctor,
                        _ => unreachable!(),
                    };
                    let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                    let targs = self.fill_named_args(ctor, targs, named, false, line);
                    return self.direct_call(ctor, targs, line);
                }
                Some(Binding::ModuleMember(module, member)) => {
                    let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                    return self.module_call(&module, &member, targs, line);
                }
                Some(Binding::TypeAlias(t)) => {
                    // a type used as a conversion/assertion: `LogLevel(x)`
                    let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                    if let Some(v) = targs.into_iter().next() {
                        let v = self.coerce_join(v, &t, line);
                        self.unify(&t, &v.ty, line, "type assertion");
                        return v;
                    }
                    self.error(line, "a type assertion needs one argument");
                    return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
                }
                _ => {}
            }
        }
        // a function value
        let f = self.infer_expr(function, line);
        if !named.is_empty() {
            self.error(line, "keyword arguments need a known function");
        }
        let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
        let ret = self.store.fresh();
        let expected = self.store.fresh_fn(targs.iter().map(|a| a.ty.clone()).collect(), ret.clone());
        self.unify(&f.ty, &expected, line, "call");
        mk(TExprKind::CallValue(Box::new(f), targs), ret)
    }

    /// Reorder keyword arguments and fill defaults for a call of a known def.
    fn fill_named_args(&mut self, def: DefId, mut args: Vec<TExpr>, named: &[(String, ast::Expression)], _is_method: bool, line: usize) -> Vec<TExpr> {
        let params: Vec<TParam> = match &self.defs[def] {
            Some(d) => d.params.clone(),
            None => {
                if !named.is_empty() {
                    self.error(line, "keyword arguments cannot be used in a recursive call");
                }
                return args;
            }
        };
        if args.len() > params.len() {
            self.error(line, format!("too many arguments: {} given, {} expected", args.len(), params.len()));
            return args;
        }
        let mut slots: Vec<Option<TExpr>> = params.iter().map(|_| None).collect();
        for (i, a) in args.drain(..).enumerate() {
            slots[i] = Some(a);
        }
        for (n, e) in named {
            match params.iter().position(|p| &p.name == n) {
                Some(i) => {
                    if slots[i].is_some() {
                        self.error(line, format!("argument {} given twice", n));
                    }
                    let v = self.infer_expr(e, line);
                    slots[i] = Some(v);
                }
                None => self.error(line, format!("no parameter named {}", n)),
            }
        }
        let mut out = Vec::new();
        for (i, s) in slots.into_iter().enumerate() {
            match s {
                Some(v) => out.push(v),
                None => match &params[i].default {
                    Some(d) => out.push(d.clone()),
                    None => {
                        self.error(line, format!("missing argument {}", params[i].name));
                    }
                },
            }
        }
        out
    }

    pub(super) fn direct_call(&mut self, def: DefId, args: Vec<TExpr>, line: usize) -> TExpr {
        let fty = self.def_value_type(def, line);
        let (params, ret) = match self.store.shallow(&fty) {
            Type::Fn(p, r, _) => (p, *r),
            _ => {
                self.error(line, "internal: def without a function type");
                return TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
            }
        };
        let mut args = args;
        if args.len() < params.len() {
            // fill defaults
            if let Some(Some(d)) = self.defs.get(def) {
                let d = d.clone();
                for i in args.len()..params.len() {
                    match &d.params.get(i).and_then(|p| p.default.clone()) {
                        Some(v) => args.push(v.clone()),
                        None => {
                            self.error(line, format!("{}() takes {} argument(s), {} given", d.name, params.len(), args.len()));
                            break;
                        }
                    }
                }
            } else {
                self.error(line, format!("call takes {} argument(s), {} given", params.len(), args.len()));
            }
        }
        if args.len() > params.len() {
            self.error(line, format!("call takes {} argument(s), {} given", params.len(), args.len()));
        }
        let mut coerced = Vec::new();
        for (p, a) in params.iter().zip(args.into_iter()) {
            let a = self.coerce_join(a, p, line);
            self.unify(p, &a.ty, line, "argument");
            coerced.push(a);
        }
        TExpr { kind: TExprKind::Call(def, coerced), ty: ret, line }
    }

    pub(super) fn method_call_pub(&mut self, recv: TExpr, name: &str, args: Vec<TExpr>, line: usize) -> TExpr {
        self.method_call(recv, name, args, line)
    }

    fn method_call(&mut self, recv: TExpr, name: &str, args: Vec<TExpr>, line: usize) -> TExpr {
        let ret = self.store.fresh();
        self.defer(Pending::Method { recv: recv.ty.clone(), name: name.to_string(), args: args.iter().map(|a| a.ty.clone()).collect(), ret: ret.clone(), line });
        self.resolve_pending(false);
        TExpr { kind: TExprKind::MethodCall { recv: Box::new(recv), name: name.to_string(), args }, ty: ret, line }
    }

    fn global_call(&mut self, name: &str, args: Vec<TExpr>, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        match name {
            "type" | "any" | "object" | "fn" | "list" | "number" | "nothing" => {
                self.error(line, format!("{}() is not supported", name));
                return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
            }
            "int" | "float" | "str" | "bool" | "print" | "debug" | "len" | "sum" | "min" | "max" | "abs" | "round" | "sorted" | "reversed" => {
                if args.is_empty() {
                    if name == "print" {
                        return mk(TExprKind::Builtin("print".into(), vec![]), Type::Unit);
                    }
                    self.error(line, format!("{}() needs an argument", name));
                    return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
                }
                let ret = self.store.fresh();
                self.defer(Pending::Global { name: name.to_string(), args: args.iter().map(|a| a.ty.clone()).collect(), ret: ret.clone(), line });
                self.resolve_pending(false);
                return mk(TExprKind::Builtin(name.into(), args), ret);
            }
            _ => {}
        }
        match sigs::global_sig(&mut self.store, name, args.len()) {
            Some((params, ret)) => {
                if params.len() != args.len() {
                    self.error(line, format!("{}() takes {} argument(s), {} given", name, params.len(), args.len()));
                }
                let mut out = Vec::new();
                for (p, a) in params.iter().zip(args.into_iter()) {
                    let a = self.coerce_join(a, p, line);
                    self.unify(p, &a.ty, line, &format!("argument of {}()", name));
                    out.push(a);
                }
                mk(TExprKind::Builtin(name.into(), out), ret)
            }
            None => {
                self.error(line, format!("unknown builtin {}", name));
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
        }
    }

    fn module_call(&mut self, module: &str, member: &str, args: Vec<TExpr>, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        match sigs::module_member(&mut self.store, module, member, args.len()) {
            Some(Type::Fn(params, ret, _)) => {
                if params.len() != args.len() {
                    self.error(line, format!("${}.{} takes {} argument(s), {} given", module, member, params.len(), args.len()));
                }
                let mut out = Vec::new();
                for (p, a) in params.iter().zip(args.into_iter()) {
                    let a = self.coerce_join(a, p, line);
                    self.unify(p, &a.ty, line, &format!("argument of ${}.{}", module, member));
                    out.push(a);
                }
                mk(TExprKind::Builtin(format!("{}.{}", module, member), out), *ret)
            }
            Some(_) => {
                self.error(line, format!("${}.{} is not a function", module, member));
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
            None => {
                self.error(line, format!("unknown module member ${}.{}", module, member));
                mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
            }
        }
    }

    fn infer_member_access(&mut self, object: &ast::Expression, member: &str, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        if let ast::Expression::Import(module) = object {
            return match sigs::module_member(&mut self.store, module, member, 1) {
                Some(t @ Type::Fn(..)) => mk(TExprKind::Builtin(format!("{}.{}", module, member), vec![]), t),
                Some(t) => mk(TExprKind::Builtin(format!("{}.{}", module, member), vec![]), t),
                None => {
                    self.error(line, format!("unknown module member ${}.{}", module, member));
                    mk(TExprKind::Lit(Lit::Nothing), Type::Unit)
                }
            };
        }
        // Namespace access: Class.member on a class with only optional params
        if let ast::Expression::Identifier(n) = object {
            if let Some(Binding::Class(rec)) = self.lookup(n, line) {
                let ctor = match &self.records[rec].kind {
                    RecordKind::Class { ctor, .. } => *ctor,
                    _ => unreachable!(),
                };
                let inst = self.direct_call(ctor, vec![], line);
                let ty = self.store.fresh();
                return self.member_read(inst, member, ty, line);
            }
        }
        let obj = self.infer_expr(object, line);
        let ty = self.store.fresh();
        self.member_read(obj, member, ty, line)
    }

    /// `obj.member` as a read, deferring resolution of the receiver type.
    pub(super) fn member_read(&mut self, obj: TExpr, member: &str, ty: Type, line: usize) -> TExpr {
        self.defer(Pending::Field { recv: obj.ty.clone(), name: member.to_string(), ty: ty.clone(), line });
        self.resolve_pending(false);
        TExpr { kind: TExprKind::Member(Box::new(obj), member.to_string()), ty, line }
    }

    // -- pipelines -----------------------------------------------------------

    fn infer_pipeline(&mut self, left: &ast::Expression, op: ast::PipelineOperator, right: &ast::Expression, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        let l = self.infer_expr(left, line);
        let mentions_dollar = expression_mentions_dollar(right);
        // `!> value` with a plain value
        let is_plain_value = op == ast::PipelineOperator::Handle && !mentions_dollar && !looks_like_function(right);
        let func = if mentions_dollar {
            let params = vec![ast::Param { is_public: false, is_var: false, pattern: ast::Pattern::Identifier("$".into()), default: None }];
            self.infer_lambda(&params, right, None, line)
        } else {
            self.infer_expr(right, line)
        };
        let lt = self.store.shallow(&l.ty);
        match op {
            ast::PipelineOperator::Pipe => {
                let (arg_ty, is_result) = match &lt {
                    Type::Result(_, a) => ((**a).clone(), true),
                    _ => (l.ty.clone(), false),
                };
                let ret = self.store.fresh();
                let expected = self.store.fresh_fn(vec![arg_ty], ret.clone());
                self.unify(&func.ty, &expected, line, "pipeline function");
                let ty = if is_result { self.railway_type(&lt, &ret) } else { ret };
                mk(TExprKind::Pipe { left: Box::new(l), func: Box::new(func) }, ty)
            }
            ast::PipelineOperator::Map | ast::PipelineOperator::Filter => {
                let sop = if op == ast::PipelineOperator::Map { StageOp::Map } else { StageOp::Filter };
                // the input: a list, a range, a stream, or a result of one
                let (inner, wrap_result) = match &lt {
                    Type::Result(_, a) => ((**a).clone(), Some(lt.clone())),
                    _ => (lt.clone(), None),
                };
                let (elem, is_stream) = match self.store.shallow(&inner) {
                    Type::List(e) => ((*e).clone(), false),
                    Type::Range => (Type::Int, false),
                    Type::Stream(e) => ((*e).clone(), true),
                    Type::Var(_) => {
                        let e = self.store.fresh();
                        self.unify(&inner, &Type::list(e.clone()), line, "pipeline input");
                        (e, false)
                    }
                    other => {
                        let n = self.type_name(&other);
                        self.error(line, format!("{} needs a list on its left, found {}", if sop == StageOp::Map { "*>" } else { "?>" }, n));
                        (self.store.fresh(), false)
                    }
                };
                // per-element railway: elements that are results unwrap into the stage
                let (stage_in, elem_result) = match self.store.shallow(&elem) {
                    Type::Result(_, a) => ((*a).clone(), true),
                    _ => (elem.clone(), false),
                };
                let ret = self.store.fresh();
                let expected = self.store.fresh_fn(vec![stage_in], ret.clone());
                self.unify(&func.ty, &expected, line, "pipeline stage");
                let out_elem = if sop == StageOp::Filter {
                    elem.clone()
                } else if elem_result {
                    if let Type::Result(e, _) = self.store.shallow(&elem) {
                        self.railway_type(&Type::result((*e).clone(), Type::Unit), &ret)
                    } else {
                        ret
                    }
                } else {
                    ret
                };
                let out = if is_stream { Type::stream(out_elem) } else { Type::list(out_elem) };
                let ty = match wrap_result {
                    Some(Type::Result(e, _)) => Type::result((*e).clone(), out),
                    _ => out,
                };
                mk(TExprKind::Stage { op: sop, input: Box::new(l), func: Box::new(func) }, ty)
            }
            ast::PipelineOperator::Handle => {
                match &lt {
                    Type::Result(e, a) => {
                        let (e, a) = ((**e).clone(), (**a).clone());
                        if is_plain_value {
                            let h = self.coerce_join(func, &a, line);
                            self.unify(&a, &h.ty, line, "recovery value");
                            mk(TExprKind::Handle { left: Box::new(l), handler: Box::new(h), is_func: false }, a)
                        } else {
                            let ret = self.store.fresh();
                            let expected = self.store.fresh_fn(vec![e], ret.clone());
                            self.unify(&func.ty, &expected, line, "error handler");
                            self.unify(&a, &ret, line, "the !> handler must produce the ok type");
                            mk(TExprKind::Handle { left: Box::new(l), handler: Box::new(func), is_func: true }, a)
                        }
                    }
                    Type::List(elem) => {
                        // elementwise reunion
                        let elem = (**elem).clone();
                        match self.store.shallow(&elem) {
                            Type::Result(e, a) => {
                                let (e, a) = ((*e).clone(), (*a).clone());
                                if is_plain_value {
                                    let h = self.coerce_join(func, &a, line);
                                    self.unify(&a, &h.ty, line, "recovery value");
                                    mk(TExprKind::Handle { left: Box::new(l), handler: Box::new(h), is_func: false }, Type::list(a))
                                } else {
                                    let ret = self.store.fresh();
                                    let expected = self.store.fresh_fn(vec![e], ret.clone());
                                    self.unify(&func.ty, &expected, line, "error handler");
                                    self.join_into(&a, &ret, line);
                                    mk(TExprKind::Handle { left: Box::new(l), handler: Box::new(func), is_func: true }, Type::list(a))
                                }
                            }
                            _ => {
                                // nothing to handle
                                l
                            }
                        }
                    }
                    Type::Var(_) => {
                        self.error(line, "cannot infer whether the left of !> is a result; add a type annotation");
                        l
                    }
                    _ => l,
                }
            }
        }
    }

    /// The type of a railway step: `Result<E, T>` piped into a function
    /// returning `R` is `Result<E, R>`, flattened when R is itself a result.
    fn railway_type(&mut self, left: &Type, ret: &Type) -> Type {
        let e = match self.store.shallow(left) {
            Type::Result(e, _) => (*e).clone(),
            _ => self.store.fresh(),
        };
        match self.store.shallow(ret) {
            Type::Result(e2, a) => {
                self.store.unify(&e, &e2).ok();
                Type::result(e, (*a).clone())
            }
            _ => Type::result(e, ret.clone()),
        }
    }

    // -- comprehensions ------------------------------------------------------

    fn infer_comprehension(&mut self, clauses: &[ast::CompClause], body: &ast::Expression, line: usize) -> TExpr {
        let mk = |kind: TExprKind, ty: Type| TExpr { kind, ty, line };
        if clauses.len() != 1 {
            self.error(line, "only a single `for ... in ... do` clause is supported");
            return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
        }
        let (pattern, iterables) = match &clauses[0] {
            ast::CompClause::For { pattern, iterables } => (pattern, iterables),
            ast::CompClause::While { .. } => {
                self.error(line, "`while ... do` comprehensions are not supported");
                return mk(TExprKind::Lit(Lit::Nothing), Type::Unit);
            }
        };
        let mut iters = Vec::new();
        let mut elem_tys = Vec::new();
        for it in iterables {
            let e = self.infer_expr(it, line);
            let elem = self.store.fresh();
            self.defer(Pending::Iter { recv: e.ty.clone(), elem: elem.clone(), line });
            elem_tys.push(elem);
            iters.push(e);
        }
        self.resolve_pending(false);
        let item_ty = if elem_tys.len() == 1 { elem_tys[0].clone() } else { self.zip_item_type(&elem_tys) };
        self.push_scope();
        self.last_pattern_bindings.clear();
        let pat = self.infer_binding_pattern(pattern, &item_ty, line);
        for (n, t) in self.last_pattern_bindings.clone() {
            self.declare(&n, Binding::Local { ty: t, mutable: false });
        }
        // `if cond do value` without else filters
        let (filter, body_expr) = match body {
            ast::Expression::IfExpr { condition, then_branch, elif_branches, else_branch: None } if elif_branches.is_empty() => {
                let c = self.infer_expr(condition, line);
                (Some(Box::new(c)), self.infer_expr(then_branch, line))
            }
            other => (None, self.infer_expr(other, line)),
        };
        self.pop_scope();
        let ty = Type::list(body_expr.ty.clone());
        mk(TExprKind::Comprehension { pattern: pat, iterables: iters, filter, body: Box::new(body_expr) }, ty)
    }

    // -- match ---------------------------------------------------------------

    /// Match arms; when `result` is None the match is a statement whose
    /// value is not used, so the arms need not agree on a type.
    pub(super) fn infer_arms_opt(&mut self, subject: &Type, arms: &[ast::MatchArm], result: Option<&Type>, _line: usize) -> Vec<TArm> {
        let mut out = Vec::new();
        // a subject of unknown type matched against `nothing` is a maybe
        if let Type::Var(_) = self.store.shallow(subject) {
            let has_nothing = arms.iter().any(|a| match &a.pattern {
                ast::Pattern::Literal(ast::Expression::Nothing) => true,
                ast::Pattern::Typed { type_expr, .. } => match type_expr {
                    ast::Expression::Nothing => true,
                    ast::Expression::Identifier(n) => n == "nothing",
                    _ => false,
                },
                _ => false,
            });
            if has_nothing {
                let inner = self.store.fresh();
                self.unify(subject, &Type::maybe(inner), _line, "match subject");
            }
        }
        // after a `nothing` arm a variable pattern binds the present value
        let mut saw_nothing = false;
        for arm in arms {
            self.push_scope();
            self.last_pattern_bindings.clear();
            let st = self.store.shallow(subject);
            let pat = match (&st, &arm.pattern) {
                (Type::Maybe(inner), ast::Pattern::Identifier(n)) if saw_nothing && n != "_" => {
                    let inner = (**inner).clone();
                    self.last_pattern_bindings.push((n.clone(), inner));
                    TPattern::Some(Box::new(TPattern::Bind(n.clone())))
                }
                _ => self.infer_match_pattern(&arm.pattern, subject, arm.line),
            };
            if matches!(pat, TPattern::None) && arm.guard.is_none() {
                saw_nothing = true;
            }
            for (n, t) in self.last_pattern_bindings.clone() {
                self.declare(&n, Binding::Local { ty: t, mutable: false });
            }
            let guard = arm.guard.as_ref().map(|g| self.infer_expr(g, arm.line));
            // a statement arm that mutates a container: `xs.push(v)` rebinds
            let body = if result.is_none() && super::stmts::is_container_mutation_expr(&arm.body) {
                let st = ast::Stmt { node: ast::Statement::Expression(arm.body.clone()), line: arm.line };
                let stmts = self.infer_stmt(&st);
                TExpr { kind: TExprKind::Block(TBlock { stmts }), ty: Type::Unit, line: arm.line }
            } else {
                self.infer_expr(&arm.body, arm.line)
            };
            let body = match result {
                Some(result) => {
                    let body = self.coerce_join(body, result, arm.line);
                    self.join_into(result, &body.ty, arm.line);
                    body
                }
                None => body,
            };
            self.pop_scope();
            out.push(TArm { pattern: pat, guard, body, line: arm.line });
        }
        // lift earlier arms if a later one made the result maybe/result
        if let Some(result) = result {
            let rt = self.store.shallow(result);
            for arm in out.iter_mut() {
                let b = std::mem::replace(&mut arm.body, TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: arm.line });
                arm.body = self.coerce_join(b, &rt, arm.line);
            }
        }
        out
    }

    /// A match-arm pattern against a subject of type `ty`. Literals, type
    /// tests, and nested shapes are allowed.
    fn infer_match_pattern(&mut self, p: &ast::Pattern, ty: &Type, line: usize) -> TPattern {
        let st = self.store.shallow(ty);
        match p {
            ast::Pattern::Identifier(n) => {
                if n == "_" {
                    return TPattern::Wild;
                }
                self.last_pattern_bindings.push((n.clone(), ty.clone()));
                TPattern::Bind(n.clone())
            }
            ast::Pattern::Literal(e) => {
                let v = self.infer_expr(e, line);
                match (&st, &v.kind) {
                    (Type::Maybe(_), TExprKind::Lit(Lit::Nothing)) => TPattern::None,
                    (_, TExprKind::Lit(l)) => {
                        if let Type::Maybe(inner) = &st {
                            let inner = (**inner).clone();
                            self.unify(&inner, &v.ty, line, "literal pattern");
                            return TPattern::Some(Box::new(TPattern::Lit(l.clone())));
                        }
                        self.unify(ty, &v.ty, line, "literal pattern");
                        TPattern::Lit(l.clone())
                    }
                    _ => {
                        self.error(line, "only literal values can be matched by value");
                        TPattern::Wild
                    }
                }
            }
            ast::Pattern::Typed { pattern, type_expr } => {
                // `n: int` on a maybe: the some case; `x: nothing`: the none case
                let t = self.type_from_expr(type_expr, line);
                if let Type::Maybe(inner) = &st {
                    if let Type::Unit = self.store.shallow(&t) {
                        return TPattern::None;
                    }
                    let inner = (**inner).clone();
                    self.unify(&inner, &t, line, "type pattern");
                    let sub = self.infer_match_pattern(pattern, &inner, line);
                    return TPattern::Some(Box::new(sub));
                }
                self.unify(ty, &t, line, "type pattern");
                self.infer_match_pattern(pattern, ty, line)
            }
            ast::Pattern::List(items) => {
                if let Type::Maybe(inner) = &st {
                    let inner = (**inner).clone();
                    let sub = self.infer_match_pattern(p, &inner, line);
                    return TPattern::Some(Box::new(sub));
                }
                // pair records match two-element list patterns
                if let Type::Record(PAIR_REC, args) = &st {
                    if items.len() == 2 {
                        let a = self.infer_match_pattern(&items[0], &args[0], line);
                        let b = self.infer_match_pattern(&items[1], &args[1], line);
                        return TPattern::Record(PAIR_REC, vec![(0, a), (1, b)]);
                    }
                }
                let elem = self.store.fresh();
                self.unify(ty, &Type::list(elem.clone()), line, "list pattern");
                let mut pats = Vec::new();
                let mut rest = None;
                for it in items {
                    match it {
                        ast::Pattern::Rest(r) => {
                            if let Some(n) = r {
                                self.last_pattern_bindings.push((n.clone(), Type::list(elem.clone())));
                            }
                            rest = Some(r.clone());
                        }
                        other => pats.push(self.infer_match_pattern(other, &elem, line)),
                    }
                }
                TPattern::List(pats, rest)
            }
            ast::Pattern::Object(fields) => {
                if let Type::Maybe(inner) = &st {
                    let inner = (**inner).clone();
                    let sub = self.infer_match_pattern(p, &inner, line);
                    return TPattern::Some(Box::new(sub));
                }
                if fields.len() == 1 && (fields[0].0 == "ok" || fields[0].0 == "err") {
                    let (e, a) = match &st {
                        Type::Result(e, a) => ((**e).clone(), (**a).clone()),
                        _ => {
                            let e = self.store.fresh();
                            let a = self.store.fresh();
                            self.unify(ty, &Type::result(e.clone(), a.clone()), line, "result pattern");
                            (e, a)
                        }
                    };
                    return if fields[0].0 == "ok" {
                        let sub = self.infer_match_pattern(&fields[0].1, &a, line);
                        TPattern::Ok(Box::new(sub))
                    } else {
                        let sub = self.infer_match_pattern(&fields[0].1, &e, line);
                        TPattern::Err(Box::new(sub))
                    };
                }
                let (rec, args) = match &st {
                    Type::Record(r, a) => (*r, a.clone()),
                    Type::Var(_) => {
                        // pick the unique record with all these fields
                        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                        let cands: Vec<RecId> = (0..self.records.len())
                            .filter(|&i| names.iter().all(|n| self.records[i].field_index(n).is_some()))
                            .collect();
                        if cands.len() == 1 {
                            let rec = cands[0];
                            let args: Vec<Type> = self.records[rec].field_vars.iter().map(|_| self.store.fresh()).collect();
                            self.unify(ty, &Type::Record(rec, args.clone()), line, "object pattern");
                            (rec, args)
                        } else {
                            self.error(line, "cannot infer the object type of this match; add a type annotation to the subject");
                            return TPattern::Wild;
                        }
                    }
                    other => {
                        let n = self.type_name(other);
                        self.error(line, format!("object pattern against a value of type {}", n));
                        return TPattern::Wild;
                    }
                };
                let mut out = Vec::new();
                for (fname, sub) in fields {
                    match self.records[rec].field_index(fname) {
                        Some(idx) => {
                            let fty = args[idx].clone();
                            let sp = self.infer_match_pattern(sub, &fty, line);
                            out.push((idx, sp));
                        }
                        None => {
                            self.error(line, format!("{} has no member {}", self.records[rec].name, fname));
                        }
                    }
                }
                TPattern::Record(rec, out)
            }
            ast::Pattern::FString(_) => {
                self.error(line, "f-string patterns are not supported");
                TPattern::Wild
            }
            ast::Pattern::Rest(_) => {
                self.error(line, "unexpected rest pattern");
                TPattern::Wild
            }
            _ => {
                self.error(line, "unsupported match pattern");
                TPattern::Wild
            }
        }
    }

    /// A binding pattern (for-loop target, comprehension variable): names,
    /// list/pair destructuring, and object destructuring, no literals.
    pub(super) fn infer_binding_pattern(&mut self, p: &ast::Pattern, ty: &Type, line: usize) -> TPattern {
        match p {
            ast::Pattern::Identifier(_) | ast::Pattern::List(_) | ast::Pattern::Object(_) | ast::Pattern::Typed { .. } => {
                self.infer_match_pattern(p, ty, line)
            }
            _ => {
                self.error(line, "unsupported loop pattern");
                TPattern::Wild
            }
        }
    }

    // -- type expressions ----------------------------------------------------

    pub(super) fn type_from_expr(&mut self, e: &ast::Expression, line: usize) -> Type {
        match e {
            ast::Expression::Identifier(n) => match n.as_str() {
                "int" | "number" => Type::Int,
                "float" => Type::Float,
                "str" => Type::Str,
                "bool" => Type::Bool,
                "nothing" => Type::Unit,
                "any" => self.store.fresh(),
                "list" => Type::list(self.store.fresh()),
                "object" => self.store.fresh(),
                "fn" => self.store.fresh(),
                "type" => {
                    self.error(line, "`type` values are not supported");
                    self.store.fresh()
                }
                other => match self.lookup(other, line) {
                    Some(Binding::TypeAlias(t)) => t,
                    Some(Binding::Class(rec)) => {
                        let args: Vec<Type> = self.records[rec].field_vars.iter().map(|_| self.store.fresh()).collect();
                        Type::Record(rec, args)
                    }
                    Some(Binding::Local { ty, .. }) => {
                        // a type alias binding (LogLevel = 'a' | 'b') has type str
                        ty
                    }
                    _ => {
                        self.error(line, format!("unknown type '{}'", other));
                        self.store.fresh()
                    }
                },
            },
            ast::Expression::BinaryOp { left, op: ast::BinaryOperator::TypeOr, right } => {
                let l = self.type_from_expr(left, line);
                let r = self.type_from_expr(right, line);
                let ls = self.store.shallow(&l);
                let rs = self.store.shallow(&r);
                match (&ls, &rs) {
                    (Type::Unit, _) => Type::maybe(r),
                    (_, Type::Unit) => Type::maybe(l),
                    (Type::Str, Type::Str) => Type::Str,
                    _ => {
                        self.unify(&l, &r, line, "union type");
                        l
                    }
                }
            }
            ast::Expression::Str(_) | ast::Expression::TString(_) => Type::Str,
            ast::Expression::Number(n) => {
                let v = self.infer_number(n, line);
                v.ty
            }
            ast::Expression::Boolean(_) => Type::Bool,
            ast::Expression::Nothing => Type::Unit,
            _ => {
                self.error(line, "unsupported type expression");
                self.store.fresh()
            }
        }
    }
}

pub fn expression_mentions_dollar(e: &ast::Expression) -> bool {
    use ast::Expression as E;
    match e {
        E::PreviousResult => true,
        E::List(items) => items.iter().any(expression_mentions_dollar),
        E::Object(entries) => entries.iter().any(|en| match en {
            ast::ObjectEntry::KeyValue { value, .. } => expression_mentions_dollar(value),
            _ => false,
        }),
        E::BinaryOp { left, right, .. } => expression_mentions_dollar(left) || expression_mentions_dollar(right),
        E::UnaryOp { operand, .. } => expression_mentions_dollar(operand),
        E::Lambda { .. } => false,
        E::Block(stmts) => stmts.iter().any(|s| match &s.node {
            ast::Statement::Expression(e) | ast::Statement::Return(Some(e)) => expression_mentions_dollar(e),
            ast::Statement::Declaration { value, .. } | ast::Statement::Assignment { value, .. } => expression_mentions_dollar(value),
            _ => false,
        }),
        E::Call { function, args, named_args } => {
            expression_mentions_dollar(function) || args.iter().any(expression_mentions_dollar) || named_args.iter().any(|(_, a)| expression_mentions_dollar(a))
        }
        E::MemberAccess { object, .. } | E::SpreadMember { object } => expression_mentions_dollar(object),
        E::Index { object, index } => expression_mentions_dollar(object) || expression_mentions_dollar(index),
        E::IfExpr { condition, then_branch, elif_branches, else_branch } => {
            expression_mentions_dollar(condition)
                || expression_mentions_dollar(then_branch)
                || elif_branches.iter().any(|(c, b)| expression_mentions_dollar(c) || expression_mentions_dollar(b))
                || else_branch.as_ref().is_some_and(|b| expression_mentions_dollar(b))
        }
        E::Comprehension { body, .. } => expression_mentions_dollar(body),
        E::TypeCheck { expression, .. } => expression_mentions_dollar(expression),
        E::Range { start, end } => {
            start.as_ref().is_some_and(|s| expression_mentions_dollar(s)) || end.as_ref().is_some_and(|e| expression_mentions_dollar(e))
        }
        E::Await(x) | E::Async(x) => expression_mentions_dollar(x),
        E::Pipeline { left, .. } => expression_mentions_dollar(left),
        E::FString(parts) => parts.iter().any(|p| matches!(p, ast::FStringPart::Expression(x, _) if expression_mentions_dollar(x))),
        _ => false,
    }
}

/// Does the RHS of `!>` look like a function (rather than a recovery value)?
fn looks_like_function(e: &ast::Expression) -> bool {
    matches!(e, ast::Expression::Lambda { .. } | ast::Expression::Identifier(_) | ast::Expression::MemberAccess { .. })
}

#[allow(dead_code)]
fn _unused(_: &dyn Fn(&ast::Pattern) -> Option<String>) {
    let _ = param_name;
    let _ = is_constructor;
}
