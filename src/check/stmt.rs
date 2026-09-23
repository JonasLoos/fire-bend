// src/check/stmt.rs
// Statement inference: declarations, assignments (every target form becomes
// a functional update of a variable), control flow, loops.

use super::*;

impl Checker {
    /// Check the statements of a block in the current scope.
    pub(crate) fn check_block_stmts(&mut self, stmts: &[ast::Stmt]) -> Block {
        let mut out = Vec::new();
        for s in stmts {
            self.line = s.line;
            let checked = self.check_stmt(s);
            // mutating calls hoisted out of the statement's expressions come first
            let pending = std::mem::take(&mut self.pending);
            for st in pending.into_iter().chain(checked) {
                for st in self.lift_exits(st) {
                    flatten_into(st, &mut out);
                }
            }
            self.solve_pending();
        }
        Block { stmts: out }
    }

    /// `n = match x` with an arm that leaves (`{err} => return e`) becomes
    /// the statement `match x` whose other arms bind `n`; the lowering moves
    /// the rest of the block into them. A value that may leave anywhere
    /// else (inside a call, an operator) is an error.
    fn lift_exits(&mut self, s: Stmt) -> Vec<Stmt> {
        let line = s.line;
        let out = match s.kind {
            StmtKind::Let { name, value } if value_exits(&value) => exit_binding(&Sink::Let(name), value, line),
            StmtKind::Assign { name, value } if value_exits(&value) => exit_binding(&Sink::Assign(name), value, line),
            StmtKind::Return(value) if value_exits(&value) => exit_binding(&Sink::Return, value, line),
            kind => vec![Stmt { kind, line }],
        };
        for st in &out {
            let exprs: Vec<&Expr> = match &st.kind {
                StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) | StmtKind::Return(value) => vec![value],
                StmtKind::If { cond, .. } => vec![cond],
                StmtKind::Match { subject, .. } => vec![subject],
                StmtKind::While { cond, .. } => vec![cond],
                StmtKind::For { iters, .. } => iters.iter().map(|it| match it {
                    Iter::Items(e, _) | Iter::Counter(e) => e,
                }).collect(),
                StmtKind::Break | StmtKind::Continue | StmtKind::Bind { .. } => vec![],
            };
            // an expression statement that is a block is its statements
            let in_value = |e: &Expr| if let (StmtKind::Expr(_), ExprKind::Block(b)) = (&st.kind, &e.kind) { b.stmts.iter().any(stmt_value_exits) } else { value_exits(e) };
            if exprs.into_iter().any(in_value) {
                self.error(line, "`return`, `break` and `continue` can leave a `match` or `if` whose value is bound (`n = match x`), not one used inside a larger expression: bind the value first");
                break;
            }
        }
        out
    }

    fn stmt(&mut self, kind: StmtKind) -> Stmt {
        Stmt { kind, line: self.line }
    }

    /// Check a block in its own scope.
    pub(crate) fn check_scoped(&mut self, stmts: &[ast::Stmt]) -> Block {
        self.push_scope();
        self.hoist_defs(stmts);
        let b = self.check_block_stmts(stmts);
        self.pop_scope();
        b
    }

    fn check_stmt(&mut self, s: &ast::Stmt) -> Vec<Stmt> {
        let line = s.line;
        match &s.node {
            ast::Statement::Documentation(_) | ast::Statement::Comment(_) => vec![],
            ast::Statement::TypeDecl { .. } | ast::Statement::Law { .. } => {
                if !matches!(self.frame_ref().kind, FrameKind::Main) || self.frame_ref().scopes.len() > 1 {
                    self.error(line, "type and law declarations go at the top level");
                }
                vec![]
            }
            ast::Statement::Def { name, .. } => {
                // hoisted; a nested def with captures becomes a closure here
                if let Some(d) = self.lookup_hoisted(name) {
                    self.ensure_def(d);
                    let nested = self.defs[d].unit != d;
                    if nested && !self.defs[d].captures.is_empty() {
                        let ty = self.defs[d].scheme.as_ref().map(|s| s.ty.clone()).unwrap_or_else(|| self.defs[d].mono.clone());
                        let bound = format!("__def_{}", name);
                        self.declare(&bound, Binding::Local { ty, mutable: false });
                        return vec![self.stmt(StmtKind::Bind { name: bound, def: d })];
                    }
                }
                vec![]
            }
            ast::Statement::Declaration { is_public, is_mutable, pattern, value } => {
                if let FrameKind::Ctor(tid) = self.frame_ref().kind
                    && self.frame_ref().scopes.len() == 1 {
                        return self.check_member_declaration(tid, *is_public, *is_mutable, pattern, value);
                    }
                if *is_public {
                    self.error(line, "`public` is only valid inside a class constructor");
                }
                self.check_let(pattern, value, *is_mutable)
            }
            ast::Statement::Assignment { targets, value } => self.check_assignment(targets, value),
            ast::Statement::Return(v) => {
                let ret = self.frame_ref().ret.clone();
                // a result not known yet guides nothing: the returns are
                // joined at the end (`nothing` on one path lifts the others)
                let expected = match self.shallow(&ret) {
                    Type::Var(_) => None,
                    _ => Some(ret),
                };
                let x = match v {
                    Some(e) => self.check_expr(e, expected.as_ref()),
                    None => self.lit(Lit::Nothing),
                };
                if let FrameKind::Ctor(_) = self.frame_ref().kind {
                    // `return self` at the end of a constructor
                    if let ExprKind::SelfValue(_) = x.kind {
                        return vec![];
                    }
                    self.error(line, "a constructor answers its object; only `return self` is allowed");
                    return vec![];
                }
                if let FrameKind::Main = self.frame_ref().kind {
                    self.error(line, "`return` outside a function");
                    return vec![];
                }
                // an earlier return (or the annotation) may have fixed a `T | nothing`
                let ret = self.frame_ref().ret.clone();
                let x = self.fit(x, &ret);
                vec![self.stmt(StmtKind::Return(x))]
            }
            ast::Statement::Break => {
                if self.frame_ref().loop_depth == 0 {
                    self.error(line, "`break` outside a loop");
                }
                vec![self.stmt(StmtKind::Break)]
            }
            ast::Statement::Continue => {
                if self.frame_ref().loop_depth == 0 {
                    self.error(line, "`continue` outside a loop");
                }
                vec![self.stmt(StmtKind::Continue)]
            }
            ast::Statement::While { condition, body } => {
                if !self.frame_ref().unsafe_ {
                    self.error(line, "a `while` loop may not terminate: write it as a `for` over a range or a list, or mark the enclosing def `unsafe def`");
                }
                // the condition runs again on every pass: a call hoisted in
                // front of the loop would run once
                let before = std::mem::take(&mut self.pending);
                let c = self.check_expr(condition, Some(&Type::Bool));
                self.unify(&Type::Bool, &c.ty, line);
                let hoisted = std::mem::replace(&mut self.pending, before);
                if !hoisted.is_empty() {
                    let name = expr::changed_name(&hoisted).unwrap_or("a variable").to_string();
                    self.error(line, format!("a call that changes `{}` cannot sit in a `while` condition; change it in the loop body", name));
                }
                self.frame().loop_depth += 1;
                let b = self.check_scoped(body);
                self.frame().loop_depth -= 1;
                vec![self.stmt(StmtKind::While { cond: c, body: b })]
            }
            ast::Statement::For { pattern, iterables, body } => {
                self.push_scope();
                let (pats, iters) = self.check_for_header(pattern, iterables);
                let before = std::mem::take(&mut self.pending);
                self.frame().loop_depth += 1;
                self.hoist_defs(body);
                let b = self.check_block_stmts(body);
                self.frame().loop_depth -= 1;
                self.pop_scope();
                self.pending.splice(0..0, before);
                vec![self.stmt(StmtKind::For { patterns: pats, iters, body: b })]
            }
            ast::Statement::If { condition, body, elif_branches, else_body } => {
                let c = self.check_expr(condition, Some(&Type::Bool));
                self.unify(&Type::Bool, &c.ty, line);
                // the condition's hoisted calls run before the branches
                let before = std::mem::take(&mut self.pending);
                let then = self.check_scoped(body);
                let else_ = if let Some((ec, eb)) = elif_branches.first() {
                    let rest = ast::Stmt {
                        node: ast::Statement::If { condition: ec.clone(), body: eb.clone(), elif_branches: elif_branches[1..].to_vec(), else_body: else_body.clone() },
                        line,
                    };
                    Block { stmts: self.check_stmt(&rest) }
                } else {
                    match else_body {
                        Some(eb) => self.check_scoped(eb),
                        None => Block::default(),
                    }
                };
                self.pending.splice(0..0, before);
                vec![self.stmt(StmtKind::If { cond: c, then, else_ })]
            }
            ast::Statement::Match { subject, arms } => {
                let subj = self.check_expr(subject, None);
                // the subject's hoisted calls run before the arms
                let before = std::mem::take(&mut self.pending);
                let arms = self.check_arms(&subj.ty, arms, true);
                self.pending.splice(0..0, before);
                vec![self.stmt(StmtKind::Match { subject: subj, arms })]
            }
            ast::Statement::Expression(e) => {
                let x = self.check_expr(e, None);
                // `xs.push(v)`, `xs.sort()`, `m.set(k, v)` as a statement store back
                if let ast::Expression::Call { function, .. } = e
                    && let ast::Expression::MemberAccess { member, .. } = &**function
                        && matches!(member.as_str(), "push" | "sort" | "set" | "remove" | "delete")
                            && let ExprKind::Dict { id, args } = &x.kind
                                && matches!(&self.store.constraints[*id].class, Class::Method(..)) && self.is_path(&args[0]) {
                                    let recv = args[0].clone();
                                    return self.rebind_change(&recv, x);
                                }
                vec![self.stmt(StmtKind::Expr(x))]
            }
        }
    }

    /// The arms of a match, in statement or expression position. Returns
    /// the arms; the caller unifies their types when it is a value.
    pub(crate) fn check_arms(&mut self, subject: &Type, arms: &[ast::MatchArm], statement: bool) -> Vec<Arm> {
        let mut out = Vec::new();
        let mut result_ty: Option<Type> = None;
        let subject_maybe = self.match_subject_is_maybe(subject, arms);
        for arm in arms {
            self.line = arm.line;
            self.push_scope();
            let pat = self.check_pattern(&arm.pattern, subject, subject_maybe);
            let guard = arm.guard.as_ref().map(|g| {
                let x = self.check_expr(g, Some(&Type::Bool));
                self.unify(&Type::Bool, &x.ty, arm.line);
                x
            });
            let block = match &arm.body {
                ast::Expression::Block(stmts) => {
                    self.hoist_defs(stmts);
                    Some(self.check_block_stmts(stmts))
                }
                // in a statement match an expression arm is a statement
                // (`{ok} => oks.push(ok)` stores back)
                other if statement => {
                    let stmts = vec![ast::Stmt { node: ast::Statement::Expression(other.clone()), line: arm.line }];
                    Some(self.check_block_stmts(&stmts))
                }
                _ => None,
            };
            let body = match block {
                Some(b) => {
                    let ty = match b.stmts.last() {
                        Some(Stmt { kind: StmtKind::Expr(e), .. }) => e.ty.clone(),
                        _ => Type::Unit,
                    };
                    Expr { kind: ExprKind::Block(b), ty, line: arm.line }
                }
                None => self.check_expr(&arm.body, result_ty.as_ref()),
            };
            self.pop_scope();
            if !statement {
                match &result_ty {
                    None => result_ty = Some(body.ty.clone()),
                    Some(t) => {
                        let t = t.clone();
                        self.unify(&t, &body.ty, arm.line);
                    }
                }
            }
            // a mutating call inside an arm body: the hoisted statements
            // become the arm's block
            let body = if self.pending.is_empty() {
                body
            } else {
                let mut stmts = std::mem::take(&mut self.pending);
                let ty = body.ty.clone();
                let l = body.line;
                match body.kind {
                    ExprKind::Block(b) => stmts.extend(b.stmts),
                    other => stmts.push(Stmt { kind: StmtKind::Expr(Expr { kind: other, ty: ty.clone(), line: l }), line: l }),
                }
                Expr { kind: ExprKind::Block(Block { stmts }), ty, line: l }
            };
            out.push(Arm { pat, guard, body, line: arm.line });
        }
        out
    }

    /// A match on `T | nothing`: a `nothing` arm makes plain names bind the
    /// value.
    fn match_subject_is_maybe(&mut self, subject: &Type, arms: &[ast::MatchArm]) -> bool {
        let has_nothing = arms.iter().any(|a| matches!(&a.pattern, ast::Pattern::Literal(ast::Expression::Nothing)));
        if has_nothing
            && let Type::Var(_) = self.shallow(subject) {
                let inner = self.fresh();
                let _ = self.store.unify(subject, &Type::maybe(inner));
            }
        matches!(self.shallow(subject), Type::Data(MAYBE, _)) && has_nothing
    }

    // -- declarations and assignments ----------------------------------------------

    /// `pattern = value` declaring new bindings.
    pub(crate) fn check_let(&mut self, pattern: &ast::Pattern, value: &ast::Expression, mutable: bool) -> Vec<Stmt> {
        let line = self.line;
        // `{sqrt, pi} = $math`
        if let (ast::Pattern::Object(entries), ast::Expression::Import(m)) = (pattern, value) {
            for (key, p) in entries {
                match p {
                    ast::Pattern::Identifier(n) => self.declare(n, Binding::ModuleMember(m.clone(), key.clone())),
                    _ => self.error(line, "destructure a module with plain names: {sqrt, pi} = $math"),
                }
            }
            return vec![];
        }
        let expected = match pattern {
            ast::Pattern::Typed { type_expr, .. } => Some(self.annotation(type_expr, line)),
            _ => None,
        };
        let x = self.check_expr(value, expected.as_ref());
        if let Some(t) = &expected {
            self.unify(t, &x.ty, line);
        }
        // a named lambda: calls by name may leave out its defaults
        if let (ast::Pattern::Identifier(n), ExprKind::Lambda(d)) = (pattern, &x.kind) {
            let d = *d;
            self.frame().scopes.last_mut().unwrap().hoisted.insert(n.clone(), d);
        }
        self.bind_pattern(pattern, x, mutable)
    }

    fn check_assignment(&mut self, targets: &[(ast::Pattern, ast::AssignmentOp)], value: &ast::Expression) -> Vec<Stmt> {
        let line = self.line;
        // `self.{...} = parent`
        if let [(ast::Pattern::SpreadInto { object }, _)] = targets {
            if !matches!(object, ast::Expression::Identifier(n) if n == "self") {
                self.error(line, "adoption is written `self.{...} = parent`");
                return vec![];
            }
            return self.check_adoption(value);
        }
        // a plain name that is not bound yet: a new immutable binding
        if let [(ast::Pattern::Identifier(name), ast::AssignmentOp::Assign)] = targets {
            // a private method declared by assignment in a class body
            if let (Some(Binding::Func(m)), ast::Expression::Lambda { .. }) = (self.lookup(name), value)
                && let FrameKind::Ctor(tid) = self.frame_ref().kind
                    && self.types[tid].method(name) == Some(m) {
                        self.ensure_def(m);
                        return vec![];
                    }
            if self.lookup(name).is_none() && !expr::GLOBALS.contains(&name.as_str()) {
                if let FrameKind::Ctor(tid) = self.frame_ref().kind
                    && self.frame_ref().scopes.len() == 1 {
                        return self.check_member_declaration(tid, false, false, &targets[0].0, value);
                    }
                return self.check_let(&targets[0].0, value, false);
            }
        }
        if let [(pat @ (ast::Pattern::List(_) | ast::Pattern::Object(_) | ast::Pattern::Typed { .. }), ast::AssignmentOp::Assign)] = targets
            && self.pattern_all_new(pat) {
                return self.check_let(pat, value, false);
            }
        // `x = stack.pop()`: a mutating call whose value is bound
        let x = self.check_expr(value, None);
        // chained targets share one evaluation
        let (value_expr, mut stmts) = if targets.len() > 1 {
            let tmp = self.temp("v");
            let t = x.ty.clone();
            let s = self.stmt(StmtKind::Let { name: tmp.clone(), value: x });
            (self.var(&tmp, t), vec![s])
        } else {
            (x, vec![])
        };
        for (target, op) in targets {
            let rhs = value_expr.clone();
            let rhs = match op {
                ast::AssignmentOp::Assign => rhs,
                other => {
                    // compound: read the target, combine, write back
                    let cur = self.read_target(target);
                    let rhs = self.float_literal_if(rhs, matches!(self.shallow(&cur.ty), Type::Float));
                    self.unify(&cur.ty, &rhs.ty, line);
                    let t = cur.ty.clone();
                    let name = match other {
                        ast::AssignmentOp::AddAssign => Some(ArithOp::Add),
                        ast::AssignmentOp::SubAssign => Some(ArithOp::Sub),
                        ast::AssignmentOp::MulAssign => Some(ArithOp::Mul),
                        ast::AssignmentOp::DivAssign => Some(ArithOp::Div),
                        ast::AssignmentOp::ModAssign => Some(ArithOp::Mod),
                        ast::AssignmentOp::PowAssign => Some(ArithOp::Pow),
                        _ => None,
                    };
                    match name {
                        Some(aop) => self.dict(Class::Arith(aop), t.clone(), vec![cur, rhs], t, line),
                        None => {
                            self.unify(&Type::Int, &t, line);
                            let b = match other {
                                ast::AssignmentOp::BitAndAssign => "int.and",
                                ast::AssignmentOp::BitOrAssign => "int.or",
                                ast::AssignmentOp::BitXorAssign => "int.xor",
                                ast::AssignmentOp::ShlAssign => "int.shl",
                                ast::AssignmentOp::ShrAssign => "int.shr",
                                _ => "int.ushr",
                            };
                            self.expr(ExprKind::Builtin(b.into(), vec![cur, rhs]), Type::Int)
                        }
                    }
                }
            };
            stmts.extend(self.write_target(target, rhs));
        }
        stmts
    }

    /// Whether every name a destructuring pattern binds is new.
    fn pattern_all_new(&mut self, p: &ast::Pattern) -> bool {
        match p {
            ast::Pattern::Identifier(n) => self.lookup(n).is_none(),
            ast::Pattern::Typed { pattern, .. } => self.pattern_all_new(pattern),
            ast::Pattern::List(items) => items.iter().all(|i| self.pattern_all_new(i)),
            ast::Pattern::Rest(Some(n)) => self.lookup(n).is_none(),
            ast::Pattern::Rest(None) => true,
            ast::Pattern::Object(entries) => entries.iter().all(|(_, p)| self.pattern_all_new(p)),
            _ => false,
        }
    }

    /// Whether an expression names a place a mutation can be stored back
    /// into: a variable, or fields and elements of one.
    pub(crate) fn is_path(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Var(_) => true,
            ExprKind::Field(inner, _, _) => self.is_path(inner),
            ExprKind::Dict { id, args } => {
                matches!(self.store.constraints[*id].class, Class::Field(..) | Class::Index(..)) && !args.is_empty() && self.is_path(&args[0])
            }
            ExprKind::Builtin(name, args) if name == "maybe.unwrap" => self.is_path(&args[0]),
            _ => false,
        }
    }

    /// The current value of an assignment target.
    fn read_target(&mut self, target: &ast::Pattern) -> Expr {
        let line = self.line;
        match target {
            ast::Pattern::Identifier(n) => self.check_expr(&ast::Expression::Identifier(n.clone()), None),
            ast::Pattern::Member { object, member } => {
                let o = self.check_expr(object, None);
                self.check_member_of(o, member)
            }
            ast::Pattern::Index { object, index } => {
                let o = self.check_expr(object, None);
                let i = self.check_expr(index, None);
                // the element itself: a missing dictionary key aborts
                let elem = self.fresh();
                let subject = o.ty.clone();
                let x = self.dict(Class::Index(i.ty.clone(), elem.clone()), subject, vec![o, i], elem.clone(), line);
                self.unwrap_index(x)
            }
            _ => {
                self.error(line, "a compound assignment needs a single target");
                self.lit(Lit::Nothing)
            }
        }
    }

    /// `d[k]` read for an update: a dictionary lookup answers `T | nothing`,
    /// and the update needs the value, so a missing key aborts.
    pub(crate) fn unwrap_index(&mut self, x: Expr) -> Expr {
        let is_index = matches!(&x.kind, ExprKind::Dict { id, .. } if matches!(self.store.constraints[*id].class, Class::Index(..)));
        if !is_index {
            return x;
        }
        if let Type::Data(MAYBE, args) = self.shallow(&x.ty) {
            self.effect(Effect::ABORT);
            let inner = args[0].clone();
            return self.expr(ExprKind::Builtin("maybe.unwrap".into(), vec![x]), inner);
        }
        x
    }

    /// Store a value into an assignment target: rebinding a variable, or a
    /// variable rebuilt with a field or element replaced.
    pub(crate) fn write_target(&mut self, target: &ast::Pattern, value: Expr) -> Vec<Stmt> {
        let line = self.line;
        match target {
            ast::Pattern::Identifier(name) => self.assign_name(name, value),
            ast::Pattern::Typed { pattern, type_expr } => {
                let t = self.annotation(type_expr, line);
                self.unify(&t, &value.ty, line);
                self.write_target(pattern, value)
            }
            ast::Pattern::Member { object, member } => {
                let o = self.check_expr(object, None);
                let o = self.unwrap_index(o);
                let updated = self.set_field_of(o.clone(), member, value);
                self.rebind_change(&o, updated)
            }
            ast::Pattern::Index { object, index } => {
                let o = self.check_expr(object, None);
                let o = self.unwrap_index(o);
                let i = self.check_expr(index, None);
                let subject = o.ty.clone();
                // into a list or dictionary of `T | nothing` a value lifts
                let value = match self.shallow(&subject) {
                    Type::List(e) | Type::Map(e) => self.fit(value, &e),
                    _ => value,
                };
                let updated = self.dict(Class::IndexSet(i.ty.clone(), value.ty.clone()), subject.clone(), vec![o.clone(), i, value], subject, line);
                self.rebind_change(&o, updated)
            }
            ast::Pattern::List(_) | ast::Pattern::Object(_) => self.bind_pattern(target, value, false),
            _ => {
                self.error(line, "invalid assignment target");
                vec![]
            }
        }
    }

    /// `o.member = value` as the updated record.
    pub(crate) fn set_field_of(&mut self, o: Expr, member: &str, value: Expr) -> Expr {
        let line = self.line;
        let subject = o.ty.clone();
        self.dict(Class::SetField(member.to_string(), value.ty.clone()), subject.clone(), vec![o, value], subject, line)
    }

    /// Assign to a name: a `var`, a member, or (inside a mutation) any local.
    pub(crate) fn assign_name(&mut self, name: &str, value: Expr) -> Vec<Stmt> {
        let line = self.line;
        match self.lookup(name) {
            Some(Binding::Local { ty, mutable }) => {
                if !mutable && !self.frame_ref().scopes.iter().any(|s| s.names.contains_key(name)) {
                    self.error(line, format!("cannot assign to '{}': it belongs to an enclosing function (closures capture values)", name));
                } else if !mutable {
                    self.error(line, format!("cannot reassign immutable binding '{}'; declare it with `var`", name));
                }
                let value = self.fit(value, &ty);
                self.unify(&ty, &value.ty, line);
                vec![self.stmt(StmtKind::Assign { name: name.to_string(), value })]
            }
            Some(b @ Binding::Member { .. }) => self.assign_member(&b, value),
            Some(_) => {
                self.error(line, format!("cannot assign to '{}'", name));
                vec![]
            }
            None => {
                self.error(line, format!("unknown name '{}'", name));
                vec![]
            }
        }
    }

    /// A rebinding whose only effect is the change: nothing may read the
    /// value it computes but the binding (see `lost.rs`).
    pub(crate) fn rebind_change(&mut self, path: &Expr, new_value: Expr) -> Vec<Stmt> {
        let was = std::mem::replace(&mut self.noting_change, true);
        let out = self.rebind_path(path, new_value);
        self.noting_change = was;
        out
    }

    /// Rebind the variable at the root of an expression path (`x`,
    /// `x.a`, `x[i].b`, ...) to a rebuilt value. Any binding may be rebound
    /// by a mutation of its contents; a temporary is dropped.
    pub(crate) fn rebind_path(&mut self, path: &Expr, new_value: Expr) -> Vec<Stmt> {
        let line = self.line;
        match &path.kind {
            ExprKind::Var(name) => {
                let name = name.clone();
                match self.lookup(&name) {
                    Some(Binding::Local { ty, .. }) => {
                        // a capture is copied into the lambda's first scope
                        let f = self.frame_ref();
                        let captured = f.captures.iter().any(|(n, _)| *n == name) && !f.scopes[1..].iter().any(|s| s.names.contains_key(&name));
                        if captured || !f.scopes.iter().any(|s| s.names.contains_key(&name)) {
                            self.error(line, format!("cannot modify '{}' here: a lambda or nested def captures it by value", name));
                        }
                        self.unify(&ty, &new_value.ty, line);
                        if self.noting_change {
                            let d = self.current_def();
                            self.changes.insert((d, line, name.clone()));
                        }
                        vec![self.stmt(StmtKind::Assign { name, value: new_value })]
                    }
                    Some(b @ Binding::Member { .. }) => self.assign_member(&b, new_value),
                    _ => {
                        self.error(line, format!("cannot modify '{}'", name));
                        vec![]
                    }
                }
            }
            ExprKind::Field(inner, tid, idx) => {
                let inner = (**inner).clone();
                let rebuilt = self.expr(ExprKind::SetField(Box::new(inner.clone()), *tid, *idx, Box::new(new_value)), inner.ty.clone());
                self.rebind_path(&inner, rebuilt)
            }
            ExprKind::Dict { id, args } => {
                let c = self.store.constraints[*id].clone();
                match c.class {
                    Class::Field(name, _) => {
                        let inner = args[0].clone();
                        let rebuilt = self.set_field_of(inner.clone(), &name, new_value);
                        self.rebind_path(&inner, rebuilt)
                    }
                    Class::Index(it, _) => {
                        let inner = args[0].clone();
                        let idx = args[1].clone();
                        let subject = inner.ty.clone();
                        let rebuilt = self.dict(Class::IndexSet(it, new_value.ty.clone()), subject.clone(), vec![inner.clone(), idx, new_value], subject, line);
                        self.rebind_path(&inner, rebuilt)
                    }
                    _ => {
                        // a mutation of a temporary: the result is dropped
                        vec![]
                    }
                }
            }
            ExprKind::SelfValue(tid) => {
                // a mutating method called on self: every member is refreshed
                let tid = *tid;
                if !matches!(self.frame_ref().kind, FrameKind::Method(_)) {
                    self.error(line, "a method that modifies the object can only be called from another method");
                    return vec![];
                }
                self.frame().mutates_member = true;
                let tmp = self.temp("self");
                let selft = self.class_self_type(tid);
                let mut out = vec![self.stmt(StmtKind::Let { name: tmp.clone(), value: new_value })];
                let fields = self.types[tid].ctors[0].fields.clone();
                for (i, f) in fields.iter().enumerate() {
                    let t = self.var(&tmp, selft.clone());
                    let v = self.expr(ExprKind::Field(Box::new(t), tid, i), f.ty.clone());
                    out.push(self.stmt(StmtKind::Assign { name: f.name.clone(), value: v }));
                }
                out
            }
            ExprKind::Builtin(name, args) if name == "maybe.unwrap" => {
                // d[k].push(v): the element read for update
                let inner = args[0].clone();
                self.rebind_path(&inner, new_value)
            }
            _ => vec![],
        }
    }

    // -- loops ----------------------------------------------------------------------

    /// The header of a `for`: one pattern per iterable, each iterable
    /// classified. Declares the bound names in the current scope.
    pub(crate) fn check_for_header(&mut self, pattern: &ast::Pattern, iterables: &[ast::Expression]) -> (Vec<Pat>, Vec<Iter>) {
        let line = self.line;
        let mut iters = Vec::new();
        let mut elems = Vec::new();
        let mut counters = 0;
        for it in iterables {
            match it {
                ast::Expression::Range { start, end: None } => {
                    let s = match start {
                        Some(s) => self.check_expr(s, Some(&Type::Int)),
                        None => self.lit(Lit::Int(0)),
                    };
                    self.unify(&Type::Int, &s.ty, line);
                    iters.push(Iter::Counter(s));
                    elems.push(Type::Int);
                    counters += 1;
                }
                other => {
                    let x = self.check_expr(other, None);
                    let elem = self.fresh();
                    let id = self.constrain(Class::Iter(elem.clone()), x.ty.clone(), line);
                    iters.push(Iter::Items(x, id));
                    elems.push(elem);
                }
            }
        }
        if counters == iterables.len() {
            self.error(line, "a `for` over an open range never ends: add a finite iterable alongside it, or use a range with an end");
        }
        let pats = if iterables.len() == 1 {
            vec![self.check_pattern(pattern, &elems[0], false)]
        } else {
            match pattern {
                ast::Pattern::List(items) if items.len() == iterables.len() => {
                    items.iter().zip(elems.iter()).map(|(p, t)| self.check_pattern(p, t, false)).collect()
                }
                _ => {
                    self.error(line, format!("{} iterables need {} loop targets", iterables.len(), iterables.len()));
                    elems.iter().map(|_| Pat::Wild).collect()
                }
            }
        };
        (pats, iters)
    }
}

/// Whether a statement's own expressions (not its blocks) may leave.
fn stmt_value_exits(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) | StmtKind::Return(value) => value_exits(value),
        StmtKind::If { cond, .. } | StmtKind::While { cond, .. } => value_exits(cond),
        StmtKind::Match { subject, .. } => value_exits(subject),
        _ => false,
    }
}

/// Where a value some branches of which leave goes.
enum Sink {
    Let(String),
    Assign(String),
    Return,
}

/// Bind (or return) a value some branches of which leave: the branches
/// that fall through bind it, the others keep their exits.
fn exit_binding(sink: &Sink, v: Expr, line: usize) -> Vec<Stmt> {
    let bind = |v: Expr| {
        let kind = match sink {
            Sink::Let(name) => StmtKind::Let { name: name.clone(), value: v },
            Sink::Assign(name) => StmtKind::Assign { name: name.clone(), value: v },
            Sink::Return => StmtKind::Return(v),
        };
        vec![Stmt { kind, line }]
    };
    let branch = |v: Expr| -> Block {
        match v.kind {
            ExprKind::Block(b) if always_exits(&b.stmts) => b,
            kind => Block { stmts: exit_binding(sink, Expr { kind, ty: v.ty, line: v.line }, line) },
        }
    };
    match v.kind {
        ExprKind::Block(b) if contains_exit(&b.stmts) => {
            let mut stmts = b.stmts;
            match stmts.pop() {
                Some(Stmt { kind: StmtKind::Expr(last), .. }) => stmts.extend(exit_binding(sink, last, line)),
                Some(other) => stmts.push(other),
                None => {}
            }
            stmts
        }
        ExprKind::If(c, t, e) if value_exits(&t) || value_exits(&e) => {
            vec![Stmt { kind: StmtKind::If { cond: *c, then: branch(*t), else_: branch(*e) }, line }]
        }
        ExprKind::Match(s, arms) if arms.iter().any(|a| value_exits(&a.body)) => {
            let arms = arms.into_iter().map(|a| Arm { body: Expr { kind: ExprKind::Block(branch(a.body)), ty: Type::Unit, line: a.line }, ..a }).collect();
            vec![Stmt { kind: StmtKind::Match { subject: *s, arms }, line }]
        }
        kind => bind(Expr { kind, ty: v.ty, line: v.line }),
    }
}

/// A block expression used as a statement (`if c do x = 1`) is its
/// statements: they belong to the enclosing block.
fn flatten_into(s: Stmt, out: &mut Vec<Stmt>) {
    match s.kind {
        StmtKind::Expr(Expr { kind: ExprKind::Block(b), .. }) => {
            for st in b.stmts {
                flatten_into(st, out);
            }
        }
        kind => out.push(Stmt { kind, line: s.line }),
    }
}
