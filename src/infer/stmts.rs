// src/bend/infer/stmts.rs
// Statements, function definitions, classes, and the main block.

use std::collections::HashSet;

use super::*;

/// Is this def a constructor? Same rule as the interpreter: its params or
/// its body syntactically declare `public`, or it uses `self.{...} =`.
pub(super) fn is_constructor(params: &[ast::Param], body: &[ast::Stmt]) -> bool {
    params.iter().any(|p| p.is_public) || body.iter().any(|s| stmt_declares_public(&s.node))
}

fn stmt_declares_public(s: &ast::Statement) -> bool {
    match s {
        ast::Statement::Declaration { is_public: true, .. } => true,
        ast::Statement::Def { is_public: true, .. } => true,
        ast::Statement::Assignment { targets, .. } => targets.iter().any(|(p, _)| matches!(p, ast::Pattern::SpreadInto { .. })),
        ast::Statement::If { body, elif_branches, else_body, .. } => {
            body.iter().any(|s| stmt_declares_public(&s.node))
                || elif_branches.iter().any(|(_, b)| b.iter().any(|s| stmt_declares_public(&s.node)))
                || else_body.as_ref().is_some_and(|b| b.iter().any(|s| stmt_declares_public(&s.node)))
        }
        _ => false,
    }
}

#[derive(Debug, Clone)]
pub struct HoistEntry {
    pub stmt: ast::Stmt,
    pub state: HoistState,
}

impl Infer {
    // -- program -------------------------------------------------------------

    pub(super) fn infer_main(&mut self, stmts: &[ast::Stmt]) -> DefId {
        let id = self.new_def("main", DefKind::Main, 0);
        self.frames.push(Frame {
            def: id,
            kind: FrameKind::Main,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: Type::Unit,
            mutates_member: false,
        });
        self.lazy_copies.push(Vec::new());
        let body = self.infer_block(stmts);
        self.finish_lazy_copies();
        let frame = self.frames.pop().unwrap();
        let scheme = Scheme { vars: vec![], ty: self.store.fresh_fn(vec![], Type::Unit) };
        self.defs[id] = Some(TDef {
            id,
            name: "main".into(),
            kind: DefKind::Main,
            params: vec![],
            captures: frame.captures,
            scheme,
            ret: Type::Unit,
            body,
            effect: Effect::Io,
            closure_id: id,
            line: 0,
            template: None,
            template_of: None,
        });
        id
    }

    pub(super) fn new_def(&mut self, name: &str, kind: DefKind, line: usize) -> DefId {
        self.defs.push(None);
        let id = self.defs.len() - 1;
        // a placeholder so that `def_value_type` works for defs in progress
        let _ = (name, kind, line);
        id
    }

    // -- blocks --------------------------------------------------------------

    pub(super) fn infer_block(&mut self, stmts: &[ast::Stmt]) -> TBlock {
        self.push_scope();
        // hoist defs of this block so that earlier code (and each other) can
        // reference them
        let in_ctor = matches!(self.frames.last().unwrap().kind, FrameKind::Ctor(_));
        for s in stmts {
            let hoist = match &s.node {
                ast::Statement::Def { name, .. } => Some(name.clone()),
                // a named lambda in a class body is a method its siblings may call
                ast::Statement::Declaration { pattern: ast::Pattern::Identifier(name), value: ast::Expression::Lambda { .. }, .. } if in_ctor => Some(name.clone()),
                _ => None,
            };
            if let Some(name) = hoist {
                let scope = self.frame().scopes.last_mut().unwrap();
                scope.hoisted.insert(name, HoistEntry { stmt: s.clone(), state: HoistState::NotYet });
            }
        }
        let mut out = Vec::new();
        for s in stmts {
            let mut lowered = self.infer_stmt(s);
            out.append(&mut lowered);
        }
        self.pop_scope();
        TBlock { stmts: out }
    }

    /// Infer a def declared later in the block, on demand.
    pub(super) fn infer_hoisted(&mut self, frame: usize, scope: usize, name: &str) {
        let entry = self.frames[frame].scopes[scope].hoisted.get(name).cloned();
        if let Some(entry) = entry {
            // temporarily make `scope` the innermost scope for declarations
            let saved: Vec<Scope> = self.frames[frame].scopes.drain(scope + 1..).collect();
            let stmts = self.infer_stmt(&entry.stmt);
            // the Bind statement (if any) is dropped here: the def's
            // environment is captured where the def statement appears
            let _ = stmts;
            self.frames[frame].scopes.extend(saved);
        }
    }

    // -- statements ----------------------------------------------------------

    pub(super) fn infer_stmt(&mut self, stmt: &ast::Stmt) -> Vec<TStmt> {
        let line = stmt.line;
        match &stmt.node {
            ast::Statement::Documentation(_) | ast::Statement::Comment(_) => vec![],
            ast::Statement::Declaration { is_public, is_mutable, pattern, value } => {
                // `y = xs.pop()`: the last element, then the container without it
                if let Some((recv, "pop", _)) = container_mutation(value) {
                    let v = self.infer_expr(value, line);
                    let mut out = self.bind_pattern(pattern, v, *is_mutable, *is_public, line);
                    out.extend(self.pop_rebind(recv, line));
                    return out;
                }
                // {sqrt, pi} = $math
                if let (ast::Pattern::Object(fields), ast::Expression::Import(module)) = (pattern, value) {
                    for (fname, sub) in fields {
                        let local = match sub {
                            ast::Pattern::Identifier(n) => n.clone(),
                            _ => fname.clone(),
                        };
                        if sigs::module_member(&mut self.store, module, fname, 1).is_none() {
                            self.error(line, format!("unknown module member ${}.{}", module, fname));
                        }
                        self.declare(&local, Binding::ModuleMember(module.clone(), fname.clone()));
                    }
                    return vec![];
                }
                // a type alias: Level = 'a' | 'b' (`flags = a | b` on ints is a value)
                if let (ast::Pattern::Identifier(name), ast::Expression::BinaryOp { op: ast::BinaryOperator::TypeOr, .. }) = (pattern, value) {
                    if self.looks_like_type_expr(value) {
                        let t = self.type_from_expr(value, line);
                        self.declare(name, Binding::TypeAlias(t));
                        return vec![];
                    }
                }
                // a named lambda: recursion by name, a method inside a class
                if let (ast::Pattern::Identifier(name), ast::Expression::Lambda { params, body }) = (pattern, value) {
                    // already inferred on demand (a sibling called it first)?
                    let hoist_state = self.frame().scopes.last().unwrap().hoisted.get(name).map(|e| e.state);
                    match hoist_state {
                        Some(HoistState::Done) => {
                            if let Some(Binding::Func { def }) = self.frame().scopes.last().unwrap().names.get(name).cloned() {
                                if self.def_has_env(def) {
                                    return vec![TStmt { kind: TStmtKind::Bind { name: name.clone(), def }, line }];
                                }
                            }
                            return vec![];
                        }
                        Some(HoistState::NotYet) => {
                            self.frame().scopes.last_mut().unwrap().hoisted.get_mut(name).unwrap().state = HoistState::InProgress;
                        }
                        _ => {}
                    }
                    let v = self.infer_lambda(params, body, Some((name, *is_public)), line);
                    if let Some(e) = self.frame().scopes.last_mut().unwrap().hoisted.get_mut(name) {
                        e.state = HoistState::Done;
                    }
                    return match v.kind {
                        TExprKind::Lambda(def) => vec![TStmt { kind: TStmtKind::Bind { name: name.clone(), def }, line }],
                        _ => vec![],
                    };
                }
                let v = self.infer_expr(value, line);
                self.bind_pattern(pattern, v, *is_mutable, *is_public, line)
            }
            ast::Statement::Assignment { targets, value } => {
                // `name = <lambda>` / `Name = <type>` / `{a, b} = $module` on a
                // fresh name are declarations
                if let [(pattern, ast::AssignmentOp::Assign)] = targets.as_slice() {
                    let fresh = match pattern {
                        ast::Pattern::Identifier(n) => {
                            let k = self.frames.len();
                            self.lookup_in_frame(k - 1, n).is_none()
                        }
                        ast::Pattern::Object(_) => matches!(value, ast::Expression::Import(_)),
                        _ => false,
                    };
                    if fresh {
                        let decl = ast::Stmt { node: ast::Statement::Declaration { is_public: false, is_mutable: false, pattern: pattern.clone(), value: value.clone() }, line };
                        let special = matches!(value, ast::Expression::Lambda { .. } | ast::Expression::Import(_))
                            || (matches!(value, ast::Expression::BinaryOp { op: ast::BinaryOperator::TypeOr, .. }) && self.looks_like_type_expr(value));
                        if special {
                            return self.infer_stmt(&decl);
                        }
                    }
                }
                let mut out = self.infer_assignment(targets, value, line);
                if let Some((recv, "pop", _)) = container_mutation(value) {
                    out.extend(self.pop_rebind(recv, line));
                }
                out
            }
            ast::Statement::Return(e) => {
                let kind = self.frames.last().unwrap().kind;
                match e {
                    Some(x) => {
                        if let FrameKind::Ctor(_) = kind {
                            if !matches!(x, ast::Expression::Identifier(n) if n == "self") {
                                self.error(line, "a constructor cannot return a value (only `return self`)");
                            }
                            return vec![TStmt { kind: TStmtKind::Return(None), line }];
                        }
                        let v = self.infer_expr(x, line);
                        let ret = self.frames.last().unwrap().ret.clone();
                        let v = self.coerce_join(v, &ret, line);
                        // joined into the result type when the body is finished
                        let is_int_lit = matches!(v.kind, TExprKind::Lit(Lit::Int(_)));
                        self.frame().returns.push((v.ty.clone(), is_int_lit));
                        vec![TStmt { kind: TStmtKind::Return(Some(v)), line }]
                    }
                    None => {
                        if !matches!(kind, FrameKind::Ctor(_)) {
                            let ret = self.frames.last().unwrap().ret.clone();
                            self.join_into(&ret, &Type::Unit, line);
                            self.frame().returns.push((Type::Unit, false));
                        }
                        vec![TStmt { kind: TStmtKind::Return(None), line }]
                    }
                }
            }
            ast::Statement::Break => {
                if self.frames.last().unwrap().loop_depth == 0 {
                    self.error(line, "break outside a loop");
                }
                vec![TStmt { kind: TStmtKind::Break, line }]
            }
            ast::Statement::Continue => {
                if self.frames.last().unwrap().loop_depth == 0 {
                    self.error(line, "continue outside a loop");
                }
                vec![TStmt { kind: TStmtKind::Continue, line }]
            }
            ast::Statement::While { condition, body } => {
                let cond = self.infer_expr(condition, line);
                self.frame().loop_depth += 1;
                let body = self.infer_block(body);
                self.frame().loop_depth -= 1;
                vec![TStmt { kind: TStmtKind::While { cond, body }, line }]
            }
            ast::Statement::For { pattern, iterables, body } => {
                let (pat, iters) = self.infer_for_header(pattern, iterables, line);
                self.frame().loop_depth += 1;
                // the loop pattern's names live in the body scope
                self.push_scope();
                for (n, t) in self.last_pattern_bindings.clone() {
                    self.declare(&n, Binding::Local { ty: t, mutable: false });
                }
                let body = self.infer_block(body);
                self.pop_scope();
                self.frame().loop_depth -= 1;
                vec![TStmt { kind: TStmtKind::For { pattern: pat, iterables: iters, body }, line }]
            }
            ast::Statement::If { condition, body, elif_branches, else_body } => {
                let cond = self.infer_expr(condition, line);
                let then = self.infer_block(body);
                let mut elifs = Vec::new();
                for (c, b) in elif_branches {
                    let c = self.infer_expr(c, line);
                    let b = self.infer_block(b);
                    elifs.push((c, b));
                }
                let else_ = else_body.as_ref().map(|b| self.infer_block(b));
                vec![TStmt { kind: TStmtKind::If { cond, then, elifs, else_ }, line }]
            }
            ast::Statement::Match { subject, arms } => {
                let subject = self.infer_expr(subject, line);
                // a statement: the arms only need a common type when the
                // block's value is used (see `block_value_type`)
                let arms = self.infer_arms_opt(&subject.ty, arms, None, line);
                vec![TStmt { kind: TStmtKind::Match { subject, arms }, line }]
            }
            ast::Statement::Def { is_public, name, params, return_type, body } => {
                self.infer_def_stmt(*is_public, name, params, return_type.as_ref(), body, line)
            }
            ast::Statement::Expression(ast::Expression::Block(inner)) => {
                // a `do` body: its statements belong to the enclosing block
                let b = self.infer_block(inner);
                b.stmts
            }
            ast::Statement::Expression(e) => {
                // `xs.push(v)` / `xs.pop()` as a statement: rebind the container
                if let Some((recv, method, args)) = container_mutation(e) {
                    let recv_e = self.infer_write_target(recv, line);
                    self.pin_list_receiver(&recv_e.ty, method, line);
                    let rt = self.store.shallow(&recv_e.ty);
                    if matches!(rt, Type::List(_) | Type::Var(_)) {
                        let targs: Vec<TExpr> = args.iter().map(|a| self.infer_expr(a, line)).collect();
                        let new_value = if method == "push" {
                            self.method_call_pub(recv_e.clone(), "push", targs, line)
                        } else {
                            self.method_call_pub(recv_e.clone(), "drop_last", vec![], line)
                        };
                        if let Type::List(_) = self.store.shallow(&new_value.ty) {
                            return self.rebind_root(recv_e, new_value, line);
                        }
                    }
                }
                let v = self.infer_expr(e, line);
                vec![TStmt { kind: TStmtKind::Expr(v), line }]
            }
        }
    }

    /// `for pattern in iterables`: types the iterables, builds the pattern
    /// and records its bindings in `last_pattern_bindings`.
    fn infer_for_header(&mut self, pattern: &ast::Pattern, iterables: &[ast::Expression], line: usize) -> (TPattern, Vec<TExpr>) {
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
        let item_ty = if elem_tys.len() == 1 {
            elem_tys[0].clone()
        } else {
            // several iterables zip: the item is a pair chain
            self.zip_item_type(&elem_tys)
        };
        self.last_pattern_bindings.clear();
        let pat = self.infer_binding_pattern(pattern, &item_ty, line);
        (pat, iters)
    }

    /// The item type of a zip over several iterables: nested pairs
    /// (a, (b, c)) built from the pair record.
    pub(super) fn zip_item_type(&mut self, elems: &[Type]) -> Type {
        let mut t = elems[elems.len() - 1].clone();
        for e in elems[..elems.len() - 1].iter().rev() {
            t = Type::Record(PAIR_REC, vec![e.clone(), t]);
        }
        t
    }

    // -- declarations and assignment ----------------------------------------

    /// `[public] [var] pattern = value`
    pub(super) fn bind_pattern(&mut self, pattern: &ast::Pattern, value: TExpr, mutable: bool, is_public: bool, line: usize) -> Vec<TStmt> {
        match pattern {
            ast::Pattern::Identifier(name) => {
                if name == "self" {
                    self.error(line, "cannot bind `self`");
                }
                let mut value = value;
                // a public member of a class under construction: unify with its field
                if let FrameKind::Ctor(rec) = self.frames.last().unwrap().kind {
                    if let Some(idx) = self.records[rec].field_index(name) {
                        let fty = self.records[rec].field_vars[idx].clone();
                        value = self.coerce_join(value, &fty, line);
                        self.unify(&fty, &value.ty, line, &format!("member {}", name));
                    } else if is_public {
                        self.error(line, format!("internal: public member {} not pre-declared", name));
                    }
                }
                self.declare(name, Binding::Local { ty: value.ty.clone(), mutable });
                let (mut prefix, value) = Self::unwrap_block_value(value, line);
                prefix.push(TStmt { kind: TStmtKind::Let { name: name.clone(), mutable, value }, line });
                prefix
            }
            ast::Pattern::Typed { pattern, type_expr } => {
                let ty = self.type_from_expr(type_expr, line);
                let value = self.coerce_join(value, &ty, line);
                self.unify(&ty, &value.ty, line, "type annotation");
                self.bind_pattern(pattern, value, mutable, is_public, line)
            }
            ast::Pattern::List(_) | ast::Pattern::Object(_) => {
                // destructure: bind the value to a temporary, then each part
                let tmp = self.fresh_name("d");
                let ty = value.ty.clone();
                let mut out = vec![TStmt { kind: TStmtKind::Let { name: tmp.clone(), mutable: false, value }, line }];
                self.declare(&tmp, Binding::Local { ty: ty.clone(), mutable: false });
                self.destructure_into(pattern, TExpr { kind: TExprKind::Local(tmp), ty, line }, mutable, is_public, line, &mut out);
                out
            }
            ast::Pattern::FString(_) => {
                self.error(line, "f-string destructuring is not supported");
                vec![]
            }
            ast::Pattern::Literal(_) | ast::Pattern::Rest(_) => {
                self.error(line, "invalid binding pattern");
                vec![]
            }
            ast::Pattern::Member { .. } | ast::Pattern::Index { .. } | ast::Pattern::SpreadInto { .. } => {
                self.error(line, "invalid declaration target");
                vec![]
            }
        }
    }

    /// A `match`/`if` in value position parses as a block holding one
    /// statement. When the block is that single statement, use the
    /// expression itself (a match expression), or, for a statement without
    /// a value (its branches only assign), run the statement first and bind
    /// `nothing`.
    fn unwrap_block_value(value: TExpr, line: usize) -> (Vec<TStmt>, TExpr) {
        if let TExprKind::Block(b) = &value.kind {
            if b.stmts.len() == 1 {
                match &b.stmts[0].kind {
                    TStmtKind::Expr(v) => return (vec![], v.clone()),
                    TStmtKind::Match { .. } | TStmtKind::If { .. } if matches!(value.ty, Type::Unit) => {
                        let nothing = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
                        return (vec![b.stmts[0].clone()], nothing);
                    }
                    _ => {}
                }
            }
        }
        (vec![], value)
    }

    /// Expand a destructuring pattern over an already-bound expression.
    fn destructure_into(&mut self, pattern: &ast::Pattern, value: TExpr, mutable: bool, is_public: bool, line: usize, out: &mut Vec<TStmt>) {
        match pattern {
            ast::Pattern::Identifier(_) | ast::Pattern::Typed { .. } => {
                let mut stmts = self.bind_pattern(pattern, value, mutable, is_public, line);
                out.append(&mut stmts);
            }
            ast::Pattern::List(items) => {
                let vt = self.store.shallow(&value.ty);
                // a two-element list pattern on a pair record: fields
                if let Type::Record(PAIR_REC, args) = &vt {
                    if items.len() == 2 && !items.iter().any(|p| matches!(p, ast::Pattern::Rest(_))) {
                        for (i, item) in items.iter().enumerate() {
                            let f = TExpr { kind: TExprKind::Field(Box::new(value.clone()), PAIR_REC, i), ty: args[i].clone(), line };
                            self.destructure_into(item, f, mutable, is_public, line, out);
                        }
                        return;
                    }
                }
                // `[a, b]` on a value of unknown type: a list or a pair, decided
                // once the type is known (lambda parameters over `entries()`)
                if matches!(vt, Type::Var(_)) && items.len() == 2 && !items.iter().any(|p| matches!(p, ast::Pattern::Rest(_))) {
                    for (i, item) in items.iter().enumerate() {
                        let ret = self.store.fresh();
                        let idx = int_lit(i as i64, line);
                        self.defer(Pending::Index { recv: value.ty.clone(), idx: idx.ty.clone(), ret: ret.clone(), lit: Some(i as i64), line });
                        let get = TExpr { kind: TExprKind::Builtin("index".into(), vec![value.clone(), idx]), ty: ret, line };
                        self.destructure_into(item, get, mutable, is_public, line, out);
                    }
                    return;
                }
                let elem = self.store.fresh();
                self.unify(&value.ty, &Type::list(elem.clone()), line, "list destructuring");
                let rest_at = items.iter().position(|p| matches!(p, ast::Pattern::Rest(_)));
                for (i, item) in items.iter().enumerate() {
                    match item {
                        ast::Pattern::Rest(Some(name)) => {
                            let drop = TExpr {
                                kind: TExprKind::MethodCall { recv: Box::new(value.clone()), name: "drop".into(), args: vec![int_lit(i as i64, line)] },
                                ty: Type::list(elem.clone()),
                                line,
                            };
                            self.declare(name, Binding::Local { ty: drop.ty.clone(), mutable });
                            out.push(TStmt { kind: TStmtKind::Let { name: name.clone(), mutable, value: drop }, line });
                        }
                        ast::Pattern::Rest(None) => {}
                        _ => {
                            let idx = match rest_at {
                                Some(r) if i > r => int_lit(-((items.len() - i) as i64), line),
                                _ => int_lit(i as i64, line),
                            };
                            let get = TExpr { kind: TExprKind::Builtin("index".into(), vec![value.clone(), idx]), ty: elem.clone(), line };
                            self.destructure_into(item, get, mutable, is_public, line, out);
                        }
                    }
                }
            }
            ast::Pattern::Object(fields) => {
                let vt = self.store.shallow(&value.ty);
                // {ok} / {err} destructuring on a result: the loud unwrap
                if fields.len() == 1 && (fields[0].0 == "ok" || fields[0].0 == "err") {
                    let (e, a) = match &vt {
                        Type::Result(e, a) => ((**e).clone(), (**a).clone()),
                        _ => {
                            let e = self.store.fresh();
                            let a = self.store.fresh();
                            self.unify(&value.ty, &Type::result(e.clone(), a.clone()), line, "result destructuring");
                            (e, a)
                        }
                    };
                    let (name, ty) = if fields[0].0 == "ok" { ("unwrap_ok", a) } else { ("unwrap_err", e) };
                    let get = TExpr { kind: TExprKind::Builtin(name.into(), vec![value]), ty, line };
                    self.destructure_into(&fields[0].1, get, mutable, is_public, line, out);
                    return;
                }
                for (fname, sub) in fields {
                    let fty = self.store.fresh();
                    let get = self.member_read(value.clone(), fname, fty, line);
                    self.destructure_into(sub, get, mutable, is_public, line, out);
                }
            }
            ast::Pattern::Rest(_) => {}
            _ => {
                self.error(line, "unsupported destructuring pattern");
            }
        }
    }

    fn infer_assignment(&mut self, targets: &[(ast::Pattern, ast::AssignmentOp)], value: &ast::Expression, line: usize) -> Vec<TStmt> {
        let mut out = Vec::new();
        let v = self.infer_expr(value, line);
        // chained assignment evaluates once
        let (v, tmp_stmt) = if targets.len() > 1 {
            let tmp = self.fresh_name("a");
            self.declare(&tmp, Binding::Local { ty: v.ty.clone(), mutable: false });
            let ty = v.ty.clone();
            (TExpr { kind: TExprKind::Local(tmp.clone()), ty, line }, Some(TStmt { kind: TStmtKind::Let { name: tmp, mutable: false, value: v }, line }))
        } else {
            (v, None)
        };
        if let Some(s) = tmp_stmt {
            out.push(s);
        }
        for (target, op) in targets {
            let mut stmts = self.assign_target(target, *op, v.clone(), line);
            out.append(&mut stmts);
        }
        out
    }

    fn assign_target(&mut self, target: &ast::Pattern, op: ast::AssignmentOp, value: TExpr, line: usize) -> Vec<TStmt> {
        match target {
            ast::Pattern::Identifier(name) => {
                // inside a constructor, the first `name = v` for a member is its declaration
                if let FrameKind::Ctor(_) = self.frames.last().unwrap().kind {
                    let n = self.frames.len();
                    if op == ast::AssignmentOp::Assign && self.lookup_in_frame(n - 1, name).is_none() && self.lookup_member(name).is_some() {
                        return self.bind_pattern(target, value, false, false, line);
                    }
                }
                let existing = self.lookup(name, line);
                match existing {
                    None => {
                        if op != ast::AssignmentOp::Assign {
                            self.error(line, format!("undefined name '{}'", name));
                            return vec![];
                        }
                        // a new immutable binding
                        self.bind_pattern(target, value, false, false, line)
                    }
                    Some(Binding::Local { ty, mutable }) => {
                        if !mutable && !self.is_container_mutation(&ty, op) {
                            // `=` on an existing name in an *inner* scope shadows? Fire: reassigns.
                            self.error(line, format!("cannot reassign immutable binding '{}' (declare it with var)", name));
                        }
                        let cur = TExpr { kind: TExprKind::Local(name.clone()), ty: ty.clone(), line };
                        let new_value = self.apply_compound(op, cur, value, line);
                        let new_value = self.coerce_join(new_value, &ty, line);
                        self.unify(&ty, &new_value.ty, line, &format!("assignment to {}", name));
                        let (mut prefix, new_value) = Self::unwrap_block_value(new_value, line);
                        prefix.push(TStmt { kind: TStmtKind::Assign { name: name.clone(), value: new_value }, line });
                        prefix
                    }
                    Some(Binding::Member { path, ty, mutable }) => {
                        if !mutable {
                            self.error(line, format!("cannot reassign immutable member '{}' (declare it with var)", name));
                        }
                        self.frame().mutates_member = true;
                        let cur = self.member_path_read(&path, line);
                        let new_value = self.apply_compound(op, cur, value, line);
                        let new_value = self.coerce_join(new_value, &ty, line);
                        self.unify(&ty, &new_value.ty, line, &format!("assignment to {}", name));
                        self.member_path_write(&path, new_value, line)
                    }
                    Some(_) => {
                        self.error(line, format!("cannot assign to '{}'", name));
                        vec![]
                    }
                }
            }
            ast::Pattern::Member { object, member } => {
                // obj.member = v  → rebind obj's root local with the field replaced
                let obj = self.infer_write_target(object, line);
                let fty = self.store.fresh();
                let cur = self.member_read(obj.clone(), member, fty.clone(), line);
                let new_value = self.apply_compound(op, cur, value, line);
                let new_value = self.coerce_join(new_value, &fty, line);
                self.unify(&fty, &new_value.ty, line, &format!("assignment to .{}", member));
                self.resolve_pending(false);
                self.rebuild_path_assign(obj, member, new_value, line)
            }
            ast::Pattern::Index { object, index } => {
                let obj = self.infer_write_target(object, line);
                let idx = self.infer_expr(index, line);
                let Some((cur, set_name)) = self.index_slot(&obj, &idx, line) else {
                    return vec![];
                };
                let vty = cur.ty.clone();
                let new_value = if op == ast::AssignmentOp::Assign { value } else { self.apply_compound(op, cur, value, line) };
                let new_value = self.coerce_join(new_value, &vty, line);
                let updated = self.index_write(obj.clone(), idx, new_value, set_name, &vty, line);
                self.rebind_root(obj, updated, line)
            }
            ast::Pattern::SpreadInto { object } => {
                if !matches!(object, ast::Expression::Identifier(n) if n == "self") {
                    self.error(line, "only `self.{...} = parent` is supported");
                    return vec![];
                }
                let rec = match self.frames.last().unwrap().kind {
                    FrameKind::Ctor(r) => r,
                    _ => {
                        self.error(line, "`self.{...} =` is only valid inside a constructor");
                        return vec![];
                    }
                };
                let pidx = match self.records[rec].parent_field() {
                    Some(p) => p,
                    None => {
                        self.error(line, "internal: no parent field");
                        return vec![];
                    }
                };
                let pty = self.records[rec].field_vars[pidx].clone();
                self.unify(&pty, &value.ty, line, "parent object");
                self.resolve_pending(false);
                if !matches!(self.store.shallow(&value.ty), Type::Record(_, _)) {
                    self.error(line, "the parent of `self.{...} =` must be an object built by a constructor");
                }
                let pname = self.records[rec].fields[pidx].name.clone();
                if pname != "__parent" {
                    // the parent field is the class-body binding itself
                    if let TExprKind::Local(n) = &value.kind {
                        if n == &pname {
                            return vec![];
                        }
                    }
                    return vec![TStmt { kind: TStmtKind::Assign { name: pname, value }, line }];
                }
                self.declare("__parent", Binding::Local { ty: pty, mutable: false });
                vec![TStmt { kind: TStmtKind::Let { name: "__parent".into(), mutable: false, value }, line }]
            }
            ast::Pattern::List(_) | ast::Pattern::Object(_) | ast::Pattern::Typed { .. } => {
                if op != ast::AssignmentOp::Assign {
                    self.error(line, "compound assignment needs a single name");
                }
                self.bind_pattern(target, value, false, false, line)
            }
            ast::Pattern::FString(_) => {
                self.error(line, "f-string destructuring is not supported");
                vec![]
            }
            _ => {
                self.error(line, "invalid assignment target");
                vec![]
            }
        }
    }

    /// The container of a write, like `infer_expr` except that a nested
    /// `a[i]` reads the element about to be written back (so a missing
    /// dictionary key aborts instead of yielding `nothing`): the `rows[r]`
    /// of `rows[r][c] = v`.
    fn infer_write_target(&mut self, e: &ast::Expression, line: usize) -> TExpr {
        if let ast::Expression::Index { object, index } = e {
            let obj = self.infer_write_target(object, line);
            let idx = self.infer_expr(index, line);
            return match self.index_slot(&obj, &idx, line) {
                Some((cur, _)) => cur,
                None => TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: self.store.fresh(), line },
            };
        }
        self.infer_expr(e, line)
    }

    /// `obj[idx]` as a slot to write: the current element, and the builtin
    /// that writes it (`list_set`, `map_set`, or `index_set` while the
    /// container's type is still open).
    fn index_slot(&mut self, obj: &TExpr, idx: &TExpr, line: usize) -> Option<(TExpr, &'static str)> {
        let elem = self.store.fresh();
        self.defer(Pending::Index { recv: obj.ty.clone(), idx: idx.ty.clone(), ret: elem.clone(), lit: None, line });
        self.resolve_pending(false);
        let ot = self.store.shallow(&obj.ty);
        match ot {
            Type::Map(v) => {
                let cur = TExpr { kind: TExprKind::Builtin("map_get_or".into(), vec![obj.clone(), idx.clone()]), ty: (*v).clone(), line };
                Some((cur, "map_set"))
            }
            Type::List(e) => {
                let cur = TExpr { kind: TExprKind::Builtin("index".into(), vec![obj.clone(), idx.clone()]), ty: (*e).clone(), line };
                Some((cur, "list_set"))
            }
            Type::Var(_) => {
                // a parameter: list or dictionary, decided when known
                let cur = TExpr { kind: TExprKind::Builtin("index_cur".into(), vec![obj.clone(), idx.clone()]), ty: elem.clone(), line };
                self.pending.retain(|p| !matches!(p, Pending::Index { ret, .. } if ret == &elem));
                self.defer(Pending::IndexCur { recv: obj.ty.clone(), idx: idx.ty.clone(), ret: elem.clone(), line });
                Some((cur, "index_set"))
            }
            other => {
                let n = self.type_name(&other);
                self.error(line, format!("cannot assign into a value of type {}", n));
                None
            }
        }
    }

    /// `obj[idx] = value` as a value: the container with the element
    /// replaced.
    fn index_write(&mut self, obj: TExpr, idx: TExpr, value: TExpr, set_name: &str, elem_ty: &Type, line: usize) -> TExpr {
        if set_name == "index_set" {
            self.defer(Pending::IndexSet { recv: obj.ty.clone(), idx: idx.ty.clone(), value: value.ty.clone(), line });
            self.resolve_pending(false);
        } else {
            self.unify(elem_ty, &value.ty, line, "assignment");
        }
        let ty = obj.ty.clone();
        TExpr { kind: TExprKind::Builtin(set_name.into(), vec![obj, idx, value]), ty, line }
    }

    /// Container mutation (`xs.push`, `m[k] = v`) is allowed on immutable
    /// bindings in Fire; the backend rebinds instead.
    fn is_container_mutation(&self, ty: &Type, _op: ast::AssignmentOp) -> bool {
        let _ = ty;
        false
    }

    pub(super) fn apply_compound(&mut self, op: ast::AssignmentOp, cur: TExpr, value: TExpr, line: usize) -> TExpr {
        let bop = match op {
            ast::AssignmentOp::Assign => return value,
            ast::AssignmentOp::AddAssign => BinOp::Add,
            ast::AssignmentOp::SubAssign => BinOp::Sub,
            ast::AssignmentOp::MulAssign => BinOp::Mul,
            ast::AssignmentOp::DivAssign => BinOp::Div,
            ast::AssignmentOp::ModAssign => BinOp::Mod,
            ast::AssignmentOp::PowAssign => BinOp::Pow,
            ast::AssignmentOp::BitAndAssign => BinOp::BitAnd,
            ast::AssignmentOp::BitOrAssign => BinOp::BitOr,
            ast::AssignmentOp::BitXorAssign => BinOp::BitXor,
            ast::AssignmentOp::ShlAssign => BinOp::Shl,
            ast::AssignmentOp::ShrAssign => BinOp::Shr,
            ast::AssignmentOp::UShrAssign => BinOp::UShr,
        };
        self.binop(bop, cur, value, line)
    }

    /// Read a member through a path from `self` (member locals in a method
    /// are plain locals named after the field; deeper paths go through
    /// `__parent`).
    pub(super) fn member_path_read(&mut self, path: &[(RecId, usize)], line: usize) -> TExpr {
        let (rec0, idx0) = path[0];
        let f0 = &self.records[rec0].fields[idx0];
        let name0 = f0.name.clone();
        let mut e = TExpr { kind: TExprKind::Local(name0), ty: self.records[rec0].field_vars[idx0].clone(), line };
        for (rec, idx) in &path[1..] {
            let ty = self.records[*rec].field_vars[*idx].clone();
            e = TExpr { kind: TExprKind::Field(Box::new(e), *rec, *idx), ty, line };
        }
        e
    }

    /// Assign to a member through a path: rebinds the first local (a field
    /// local, or `__parent` rebuilt with the nested field replaced).
    fn member_path_write(&mut self, path: &[(RecId, usize)], value: TExpr, line: usize) -> Vec<TStmt> {
        let (rec0, idx0) = path[0];
        let name0 = self.records[rec0].fields[idx0].name.clone();
        if path.len() == 1 {
            return vec![TStmt { kind: TStmtKind::Assign { name: name0, value }, line }];
        }
        // rebuild nested: local0 with field path[1..] replaced
        let root = TExpr { kind: TExprKind::Local(name0.clone()), ty: self.records[rec0].field_vars[idx0].clone(), line };
        let new_root = self.set_nested(root, &path[1..], value, line);
        vec![TStmt { kind: TStmtKind::Assign { name: name0, value: new_root }, line }]
    }

    fn set_nested(&mut self, obj: TExpr, path: &[(RecId, usize)], value: TExpr, line: usize) -> TExpr {
        let (rec, idx) = path[0];
        if path.len() == 1 {
            let ty = obj.ty.clone();
            return TExpr { kind: TExprKind::SetField(Box::new(obj), rec, idx, Box::new(value)), ty, line };
        }
        let inner_ty = self.records[rec].field_vars[idx].clone();
        let inner = TExpr { kind: TExprKind::Field(Box::new(obj.clone()), rec, idx), ty: inner_ty, line };
        let new_inner = self.set_nested(inner, &path[1..], value, line);
        let ty = obj.ty.clone();
        TExpr { kind: TExprKind::SetField(Box::new(obj), rec, idx, Box::new(new_inner)), ty, line }
    }

    /// `obj.member = value` where obj is a local or a field path rooted at
    /// a local: rebind the root.
    fn rebuild_path_assign(&mut self, obj: TExpr, member: &str, value: TExpr, line: usize) -> Vec<TStmt> {
        let ot = self.store.shallow(&obj.ty);
        let rec = match ot {
            Type::Record(r, _) => r,
            other => {
                let n = self.type_name(&other);
                self.error(line, format!("cannot assign a member on a value of type {}", n));
                return vec![];
            }
        };
        let path = match self.member_path(rec, member, Vec::new()) {
            Some(Binding::Member { path, mutable, .. }) => {
                if !mutable {
                    self.error(line, format!("member {} is not declared var", member));
                }
                path
            }
            _ => {
                self.error(line, format!("{} has no member {}", self.records[rec].name, member));
                return vec![];
            }
        };
        let updated = self.set_nested(obj.clone(), &path, value, line);
        self.rebind_root(obj, updated, line)
    }

    /// Rebind the root local of an expression (a local, or field reads off
    /// a local) to `updated`, which is the whole root value with the change
    /// applied at the obj's position.
    pub(super) fn rebind_root(&mut self, obj: TExpr, updated: TExpr, line: usize) -> Vec<TStmt> {
        match &obj.kind {
            TExprKind::Local(name) => {
                let name = name.clone();
                // container mutation is allowed on immutable bindings; member
                // assignment requires the member to be var (checked by caller)
                if let Some(Binding::Member { path, .. }) = self.lookup(&name, line) {
                    self.frame().mutates_member = true;
                    return self.member_path_write(&path, updated, line);
                }
                vec![TStmt { kind: TStmtKind::Assign { name, value: updated }, line }]
            }
            TExprKind::Field(inner, rec, idx) => {
                let inner = (**inner).clone();
                let ty = inner.ty.clone();
                let new_inner = TExpr { kind: TExprKind::SetField(Box::new(inner.clone()), *rec, *idx, Box::new(updated)), ty, line };
                self.rebind_root(inner, new_inner, line)
            }
            TExprKind::Member(inner, name) => {
                // `obj.member[i] = v` / `obj.member.push(v)`: rebuild the member
                let inner = (**inner).clone();
                let name = name.clone();
                self.resolve_pending(false);
                self.rebuild_path_assign(inner, &name, updated, line)
            }
            TExprKind::Builtin(name, args) if matches!(name.as_str(), "index" | "index_cur" | "map_get_or") && args.len() == 2 => {
                // `xs[i][j] = v` / `xs[i].push(v)` / `xs[i].field = v`: write the
                // element back into its container, then rebind that
                let inner = args[0].clone();
                let idx = args[1].clone();
                let set_name = match self.store.shallow(&inner.ty) {
                    Type::Map(_) => "map_set",
                    Type::List(_) => "list_set",
                    _ => "index_set",
                };
                let elem_ty = obj.ty.clone();
                let new_inner = self.index_write(inner.clone(), idx, updated, set_name, &elem_ty, line);
                self.rebind_root(inner, new_inner, line)
            }
            _ => {
                self.error(line, "assignment target must be a variable or a member path of a variable (`x`, `x.a`, `x[i]`, `x[i].a`, ...)");
                vec![]
            }
        }
    }

    // -- defs ----------------------------------------------------------------

    fn infer_def_stmt(&mut self, is_public: bool, name: &str, params: &[ast::Param], return_type: Option<&ast::Expression>, body: &[ast::Stmt], line: usize) -> Vec<TStmt> {
        // already inferred through hoisting?
        {
            let frame = self.frames.last_mut().unwrap();
            let scope = frame.scopes.last_mut().unwrap();
            if let Some(entry) = scope.hoisted.get_mut(name) {
                match entry.state {
                    HoistState::Done => {
                        // emit the Bind for a def with an environment
                        if let Some(Binding::Func { def }) = scope.names.get(name).cloned() {
                            if self.def_has_env(def) {
                                return vec![TStmt { kind: TStmtKind::Bind { name: name.to_string(), def }, line }];
                            }
                        }
                        return vec![];
                    }
                    HoistState::InProgress => {}
                    HoistState::NotYet => {
                        entry.state = HoistState::InProgress;
                    }
                }
            }
        }
        let result = if is_constructor(params, body) {
            self.infer_class(is_public, name, params, body, line)
        } else {
            self.infer_named_function(is_public, name, params, return_type, body, line)
        };
        let frame = self.frames.last_mut().unwrap();
        let scope = frame.scopes.last_mut().unwrap();
        if let Some(entry) = scope.hoisted.get_mut(name) {
            entry.state = HoistState::Done;
        }
        result
    }

    fn infer_named_function(&mut self, is_public: bool, name: &str, params: &[ast::Param], return_type: Option<&ast::Expression>, body: &[ast::Stmt], line: usize) -> Vec<TStmt> {
        let in_ctor = matches!(self.frames.last().unwrap().kind, FrameKind::Ctor(_));
        let kind = if in_ctor {
            let rec = match self.frames.last().unwrap().kind {
                FrameKind::Ctor(r) => r,
                _ => unreachable!(),
            };
            if is_public || self.is_prescanned_method(rec, name) || self.references_members(rec, params, body) {
                DefKind::Method { rec, mutates: false }
            } else {
                DefKind::Plain
            }
        } else {
            DefKind::Plain
        };
        let id = self.new_def(name, kind.clone(), line);
        self.declare(name, Binding::Func { def: id });
        if let DefKind::Method { rec, .. } = kind {
            if let RecordKind::Class { methods, .. } = &mut self.records[rec].kind {
                methods.push((name.to_string(), id));
            }
        }
        let decl = (self.frames.len() - 1, self.frames.last().unwrap().scopes.len() - 1);
        self.infer_function(id, name, kind.clone(), params, return_type, Some(body), None, line);
        if let DefKind::Plain = kind {
            if let Some(d) = self.defs[id].as_mut() {
                d.template = Some(Box::new(TemplateSrc { params: params.to_vec(), return_type: return_type.cloned(), body: body.to_vec(), decl }));
            }
        }
        if let DefKind::Method { .. } = kind {
            return vec![];
        }
        if self.def_has_env(id) {
            vec![TStmt { kind: TStmtKind::Bind { name: name.to_string(), def: id }, line }]
        } else {
            vec![]
        }
    }

    /// Does a function defined inside a constructor mention any member of
    /// the class (so that it needs `self`)?
    pub(super) fn references_members(&self, rec: RecId, params: &[ast::Param], body: &[ast::Stmt]) -> bool {
        let mut names = HashSet::new();
        free_names_block(body, &mut names);
        for p in params {
            if let Some(d) = &p.default {
                free_names_expr(d, &mut names);
            }
        }
        names.contains("self") || names.iter().any(|n| self.member_path(rec, n, Vec::new()).is_some()) || names.iter().any(|n| self.records[rec].method(n).is_some())
    }

    pub(super) fn references_members_expr(&self, rec: RecId, params: &[ast::Param], body: &ast::Expression) -> bool {
        let mut names = HashSet::new();
        free_names_expr(body, &mut names);
        for p in params {
            if let Some(d) = &p.default {
                free_names_expr(d, &mut names);
            }
        }
        names.contains("self") || names.iter().any(|n| self.member_path(rec, n, Vec::new()).is_some()) || names.iter().any(|n| self.records[rec].method(n).is_some())
    }

    /// Infer a function's body in a fresh frame and store its TDef.
    /// Exactly one of `body_stmts` / `body_expr` is given.
    pub(super) fn infer_function(
        &mut self,
        id: DefId,
        name: &str,
        kind: DefKind,
        params: &[ast::Param],
        return_type: Option<&ast::Expression>,
        body_stmts: Option<&[ast::Stmt]>,
        body_expr: Option<&ast::Expression>,
        line: usize,
    ) {
        self.infer_function_with(id, name, kind, params, return_type, body_stmts, body_expr, line, None)
    }

    /// `infer_function` with the parameter types of a template copy known
    /// up front (they come from the call site).
    pub(super) fn infer_function_with(
        &mut self,
        id: DefId,
        name: &str,
        kind: DefKind,
        params: &[ast::Param],
        return_type: Option<&ast::Expression>,
        body_stmts: Option<&[ast::Stmt]>,
        body_expr: Option<&ast::Expression>,
        line: usize,
        param_hints: Option<&[Type]>,
    ) {
        self.in_progress.push(id);
        self.lazy_copies.push(Vec::new());
        self.store.enter_level();
        let frame_kind = match &kind {
            DefKind::Method { rec, .. } => FrameKind::Method(*rec),
            DefKind::Ctor(rec) => FrameKind::Ctor(*rec),
            _ => FrameKind::Plain,
        };
        let ret = match return_type {
            Some(t) => self.type_from_expr(t, line),
            None => self.store.fresh(),
        };
        self.frames.push(Frame {
            def: id,
            kind: frame_kind,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: ret.clone(),
            mutates_member: false,
        });
        // parameters
        let mut tparams = Vec::new();
        let mut param_tys = Vec::new();
        let mut seen_default = false;
        let mut destructures: Vec<(ast::Pattern, String)> = Vec::new();
        for p in params {
            let (pname, pty) = match &p.pattern {
                ast::Pattern::Identifier(n) => (n.clone(), self.store.fresh()),
                ast::Pattern::Typed { pattern, type_expr } => {
                    let t = self.type_from_expr(type_expr, line);
                    match &**pattern {
                        ast::Pattern::Identifier(n) => (n.clone(), t),
                        other => {
                            let tmp = self.fresh_name("p");
                            destructures.push((other.clone(), tmp.clone()));
                            (tmp, t)
                        }
                    }
                }
                other => {
                    let tmp = self.fresh_name("p");
                    destructures.push((other.clone(), tmp.clone()));
                    (tmp, self.store.fresh())
                }
            };
            let default = match &p.default {
                Some(d) => {
                    seen_default = true;
                    let dv = self.infer_expr(d, line);
                    let dv = self.coerce_join(dv, &pty, line);
                    self.unify(&pty, &dv.ty, line, &format!("default of {}", pname));
                    Some(dv)
                }
                None => {
                    if seen_default {
                        self.error(line, format!("parameter {} without a default follows one with a default", pname));
                    }
                    None
                }
            };
            // a public parameter of a constructor is also a member
            if let FrameKind::Ctor(rec) = frame_kind {
                if let Some(idx) = self.records[rec].field_index(&pname) {
                    let fty = self.records[rec].field_vars[idx].clone();
                    self.unify(&fty, &pty, line, &format!("member {}", pname));
                }
            }
            if let Some(h) = param_hints.and_then(|h| h.get(param_tys.len())) {
                self.unify(&pty, h, line, "template parameter");
            }
            self.declare(&pname, Binding::Local { ty: pty.clone(), mutable: p.is_var });
            param_tys.push(pty.clone());
            tparams.push(TParam { name: pname, ty: pty, default });
        }
        // the function's own (monomorphic) type, for recursion
        let mut full_params = param_tys.clone();
        if let DefKind::Method { rec, .. } = &kind {
            let self_ty = Type::Record(*rec, self.records[*rec].field_vars.clone());
            full_params.insert(0, self_ty);
        }
        let ret_for_type = match &kind {
            DefKind::Ctor(rec) => Type::Record(*rec, self.records[*rec].field_vars.clone()),
            _ => ret.clone(),
        };
        let own_clos = self.store.clos_singleton(id);
        let own_ty = Type::Fn(full_params.clone(), Box::new(ret_for_type.clone()), own_clos);
        self.frame().scopes[0].names.insert("__self_type".into(), Binding::Local { ty: own_ty.clone(), mutable: false });

        // destructuring parameters bind their parts first
        let mut prologue = Vec::new();
        for (pat, tmp) in &destructures {
            let ty = self.frame().scopes[0].names.get(tmp).and_then(|b| if let Binding::Local { ty, .. } = b { Some(ty.clone()) } else { None }).unwrap();
            let v = TExpr { kind: TExprKind::Local(tmp.clone()), ty, line };
            let mut stmts = self.bind_pattern(pat, v, false, false, line);
            prologue.append(&mut stmts);
        }
        // body
        let mut body = match (body_stmts, body_expr) {
            (Some(stmts), _) => {
                let b = self.infer_block(stmts);
                self.finish_body(b, &kind, &ret, line)
            }
            (_, Some(e)) if self.body_mutates_container(e, &tparams) => {
                // `v => items.push(v)`: the body is the mutation statement, so
                // the container rebinds as it would in a block; `pop` also
                // answers the element
                let stmts = self.container_mutation_body(e, line);
                let b = self.infer_block(&stmts);
                self.finish_body(b, &kind, &ret, line)
            }
            (_, Some(e)) => {
                let v = self.infer_expr(e, line);
                let v = self.coerce_join(v, &ret, line);
                self.unify(&ret, &v.ty, line, "function result");
                TBlock { stmts: vec![TStmt { kind: TStmtKind::Return(Some(v)), line }] }
            }
            _ => TBlock::default(),
        };
        if !prologue.is_empty() {
            prologue.append(&mut body.stmts);
            body.stmts = prologue;
        }
        self.resolve_pending(false);
        self.finish_lazy_copies();
        let frame = self.frames.pop().unwrap();
        self.store.leave_level();
        self.in_progress.pop();

        let kind = match kind {
            DefKind::Method { rec, .. } => DefKind::Method { rec, mutates: frame.mutates_member },
            k => k,
        };
        let ret_final = match &kind {
            DefKind::Ctor(_) => ret_for_type.clone(),
            _ => self.store.resolve(&ret),
        };
        let fn_ty = Type::Fn(full_params, Box::new(ret_final.clone()), own_clos);
        // Generalize named functions over their unconstrained variables;
        // variables a pending constraint mentions stay monomorphic (the
        // monomorphism restriction), and lambdas are never generalized.
        for pnd in self.pending.clone() {
            for t in pnd.types() {
                self.store.pin(&t);
            }
        }
        let scheme = if matches!(kind, DefKind::Lambda) {
            self.store.pin(&fn_ty);
            Scheme { vars: vec![], ty: self.store.resolve(&fn_ty) }
        } else {
            self.store.generalize(&fn_ty)
        };
        self.defs[id] = Some(TDef {
            id,
            name: name.to_string(),
            kind,
            params: tparams,
            captures: frame.captures,
            scheme,
            ret: ret_final,
            body,
            effect: Effect::Pure,
            closure_id: id,
            line,
            template: None,
            template_of: None,
        });
    }

    /// The block's value: its last expression statement is the result
    /// (unless the function returns explicitly).
    fn finish_body(&mut self, mut body: TBlock, kind: &DefKind, ret: &Type, line: usize) -> TBlock {
        if let DefKind::Ctor(_) = kind {
            return body;
        }
        self.returnify_tail(&mut body, ret);
        self.tail_to_expr(&mut body);
        // the result type joins every `return` and the trailing value;
        // `nothing` and maybes go first so a plain `T` lifts into `T | nothing`
        let mut types: Vec<(Type, bool)> = self.frames.last().unwrap().returns.clone();
        if let Some(TStmt { kind: TStmtKind::Expr(v), .. }) = body.stmts.last() {
            let is_int_lit = matches!(v.kind, TExprKind::Lit(Lit::Int(_)));
            if let Some(t) = self.block_value_type(&body, line) {
                types.push((t, is_int_lit));
            }
        }
        // int literals last: they become floats if another path answers one
        let rank = |st: &Type, lit: bool| match st {
            Type::Unit => 0,
            Type::Maybe(_) => 1,
            _ if lit => 4,
            Type::Var(_) => 3,
            _ => 2,
        };
        let mut ranked: Vec<(usize, Type, bool)> = types.into_iter().map(|(t, lit)| (rank(&self.store.shallow(&t), lit), t, lit)).collect();
        ranked.sort_by_key(|(r, _, _)| *r);
        for (_, t, lit) in ranked {
            let target = self.store.shallow(ret);
            let float_target = matches!(target, Type::Float) || matches!(&target, Type::Maybe(i) if matches!(self.store.shallow(i), Type::Float));
            if lit && float_target {
                continue;
            }
            self.join_into(ret, &t, line);
        }
        let body_done = self.finish_body_inner(body, kind, ret, line);
        let mut body = body_done;
        let ret_final = self.store.resolve(ret);
        self.recoerce_returns(&mut body, &ret_final);
        body
    }

    /// A trailing `if` statement whose branches end in values becomes an
    /// `if` whose branches `return` those values, so branches may hold
    /// loops and nested statements (an if-expression could not).
    fn returnify_tail(&mut self, b: &mut TBlock, ret: &Type) {
        fn has_value(b: &TBlock) -> bool {
            match b.stmts.last() {
                Some(TStmt { kind: TStmtKind::Expr(_), .. }) => true,
                Some(TStmt { kind: TStmtKind::If { then, elifs, else_, .. }, .. }) => {
                    has_value(then) || elifs.iter().any(|(_, b)| has_value(b)) || else_.as_ref().is_some_and(has_value)
                }
                _ => false,
            }
        }
        if !matches!(b.stmts.last(), Some(TStmt { kind: TStmtKind::If { .. }, .. })) || !has_value(b) {
            return;
        }
        let line = b.stmts.last().map(|s| s.line).unwrap_or(0);
        if let Some(TStmt { kind: TStmtKind::If { then, elifs, else_, .. }, .. }) = b.stmts.last_mut() {
            let mut branches: Vec<&mut TBlock> = vec![then];
            for (_, eb) in elifs.iter_mut() {
                branches.push(eb);
            }
            let mut missing_else = false;
            match else_ {
                Some(eb) => branches.push(eb),
                None => missing_else = true,
            }
            let ret = ret.clone();
            for br in branches {
                self.returnify_branch(br, &ret, line);
            }
            if missing_else {
                let n = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
                let v = self.coerce_join(n, &ret, line);
                self.frame().returns.push((v.ty.clone(), false));
                *else_ = Some(TBlock { stmts: vec![TStmt { kind: TStmtKind::Return(Some(v)), line }] });
            }
        }
    }

    fn returnify_branch(&mut self, b: &mut TBlock, ret: &Type, line: usize) {
        if block_terminates(b) {
            return;
        }
        if matches!(b.stmts.last(), Some(TStmt { kind: TStmtKind::If { .. }, .. })) {
            self.returnify_tail(b, ret);
            if block_terminates(b) {
                return;
            }
        }
        let v = match b.stmts.pop() {
            Some(TStmt { kind: TStmtKind::Expr(v), .. }) => v,
            Some(other) => {
                b.stmts.push(other);
                TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line }
            }
            None => TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line },
        };
        let is_int_lit = matches!(v.kind, TExprKind::Lit(Lit::Int(_)));
        let v = self.coerce_join(v, ret, line);
        self.frame().returns.push((v.ty.clone(), is_int_lit));
        b.stmts.push(TStmt { kind: TStmtKind::Return(Some(v)), line });
    }

    /// Lift `return v` values into the final return type (a `T` returned
    /// where another path made the result `T | nothing`).
    fn recoerce_returns(&mut self, b: &mut TBlock, ret: &Type) {
        for s in b.stmts.iter_mut() {
            match &mut s.kind {
                TStmtKind::Return(Some(v)) => {
                    let line = v.line;
                    let taken = std::mem::replace(v, TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line });
                    *v = self.coerce_join(taken, ret, line);
                }
                TStmtKind::If { then, elifs, else_, .. } => {
                    self.recoerce_returns(then, ret);
                    for (_, b) in elifs.iter_mut() {
                        self.recoerce_returns(b, ret);
                    }
                    if let Some(b) = else_ {
                        self.recoerce_returns(b, ret);
                    }
                }
                TStmtKind::While { body, .. } | TStmtKind::For { body, .. } => self.recoerce_returns(body, ret),
                _ => {}
            }
        }
    }

    fn finish_body_inner(&mut self, mut body: TBlock, _kind: &DefKind, ret: &Type, line: usize) -> TBlock {
        let last_is_expr = matches!(body.stmts.last(), Some(TStmt { kind: TStmtKind::Expr(_), .. }));
        if last_is_expr {
            if let Some(TStmt { kind: TStmtKind::Expr(v), line: l }) = body.stmts.pop() {
                let v = self.coerce_join(v, ret, l);
                self.unify(ret, &v.ty, l, "function result");
                body.stmts.push(TStmt { kind: TStmtKind::Return(Some(v)), line: l });
            }
        } else {
            let ends_with_return = block_terminates(&body);
            if !ends_with_return {
                // falls off the end: nothing
                let r = self.store.shallow(ret);
                match r {
                    Type::Var(_) => {
                        self.store.unify(ret, &Type::Unit).ok();
                    }
                    Type::Unit => {}
                    Type::Maybe(_) => {}
                    _ => {
                        if self.frames.last().unwrap().returns.is_empty() {
                            self.store.unify(ret, &Type::Unit).ok();
                        } else {
                            // some paths return a value, this one nothing: the result is maybe
                            let inner = self.store.fresh();
                            let m = Type::maybe(inner.clone());
                            // only possible if ret was unconstrained; otherwise it's an error
                            let msg = format!("function can fall off the end without a value; its result type is {}", self.type_name(&r));
                            self.error(line, msg);
                            let _ = m;
                        }
                    }
                }
            }
        }
        body
    }

    // -- classes ---------------------------------------------------------------

    fn infer_class(&mut self, _is_public: bool, name: &str, params: &[ast::Param], body: &[ast::Stmt], line: usize) -> Vec<TStmt> {
        // fields: public params, public declarations, private bindings that
        // methods reference, and a hidden parent
        let mut field_names: Vec<String> = Vec::new();
        let mut public: Vec<bool> = Vec::new();
        let mut mutable: Vec<bool> = Vec::new();
        let add = |n: &str, p: bool, m: bool, field_names: &mut Vec<String>, public: &mut Vec<bool>, mutable: &mut Vec<bool>| {
            if let Some(i) = field_names.iter().position(|f| f == n) {
                public[i] |= p;
                mutable[i] |= m;
            } else {
                field_names.push(n.to_string());
                public.push(p);
                mutable.push(m);
            }
        };
        let mut has_parent: Option<Option<String>> = None;
        for p in params {
            if let Some(n) = param_name(&p.pattern) {
                if p.is_public {
                    add(&n, true, p.is_var, &mut field_names, &mut public, &mut mutable);
                }
            }
        }
        // declared names, the lambdas/defs of the body with their free names
        let mut declared: Vec<(String, bool, bool)> = Vec::new(); // (name, public, mutable)
        let mut funcs: Vec<(String, bool, HashSet<String>)> = Vec::new(); // (name, public, free names)
        collect_class_body(body, &mut declared, &mut funcs, &mut has_parent);
        let mut scope_names: HashSet<String> = declared.iter().map(|d| d.0.clone()).collect();
        for p in params {
            if let Some(n) = param_name(&p.pattern) {
                scope_names.insert(n);
            }
        }
        // a function is a method when it is public or mentions the class scope
        let mut method_names: Vec<String> = Vec::new();
        for (n, pub_, free) in &funcs {
            if *pub_ || free.contains("self") || free.iter().any(|f| f != n && scope_names.contains(f)) {
                method_names.push(n.clone());
            }
        }
        // a private function that a method calls is a method too: the call
        // dispatches through `self`, so the helper never has to live in a
        // field as a closure (which could not be called)
        loop {
            let more: Vec<String> = funcs
                .iter()
                .filter(|(n, _, _)| !method_names.contains(n))
                .filter(|(n, _, _)| funcs.iter().any(|(m, _, free)| m != n && method_names.contains(m) && free.contains(n)))
                .map(|(n, _, _)| n.clone())
                .collect();
            if more.is_empty() {
                break;
            }
            method_names.extend(more);
        }
        let mut method_free: HashSet<String> = HashSet::new();
        for (n, _, free) in &funcs {
            if method_names.contains(n) {
                method_free.extend(free.iter().cloned());
            }
        }
        for p in params {
            if let Some(n) = param_name(&p.pattern) {
                if !p.is_public && method_free.contains(&n) {
                    add(&n, false, p.is_var, &mut field_names, &mut public, &mut mutable);
                }
            }
        }
        for (n, pub_, mut_) in &declared {
            if method_names.contains(n) || n == "__spread" {
                continue;
            }
            if *pub_ || method_free.contains(n) {
                add(n, *pub_, *mut_, &mut field_names, &mut public, &mut mutable);
            }
        }
        let parent_idx = match has_parent {
            Some(Some(src)) if declared.iter().any(|(n, _, _)| n == &src && n != "__spread") && !method_names.contains(&src) => {
                add(&src, false, false, &mut field_names, &mut public, &mut mutable);
                field_names.iter().position(|f| f == &src)
            }
            Some(_) => {
                add("__parent", false, false, &mut field_names, &mut public, &mut mutable);
                Some(field_names.len() - 1)
            }
            None => None,
        };
        let ctor_id = self.new_def(name, DefKind::Plain, line);
        // display order: parameters, then declarations, the parent at the spread
        let mut show_order: Vec<usize> = Vec::new();
        for p in params {
            if let Some(n) = param_name(&p.pattern) {
                if let Some(i) = field_names.iter().position(|f| f == &n) {
                    show_order.push(i);
                }
            }
        }
        for (n, _, _) in &declared {
            if n == "__spread" {
                if let Some(pi) = parent_idx {
                    if !show_order.contains(&pi) {
                        show_order.push(pi);
                    }
                }
            } else if let Some(i) = field_names.iter().position(|f| f == n) {
                if !show_order.contains(&i) && Some(i) != parent_idx {
                    show_order.push(i);
                }
            }
        }
        for i in 0..field_names.len() {
            if !show_order.contains(&i) {
                show_order.push(i);
            }
        }
        let rec = self.new_record(name, RecordKind::Class { ctor: ctor_id, methods: Vec::new(), method_names, parent: parent_idx, show_order }, field_names, public, mutable);
        self.declare(name, Binding::Class(rec));
        self.infer_function(ctor_id, name, DefKind::Ctor(rec), params, None, Some(body), None, line);
        // methods do not capture the constructor's frame; the class is
        // referenced by name, so no Bind is needed unless the ctor captured
        if self.def_has_env(ctor_id) {
            return vec![TStmt { kind: TStmtKind::Bind { name: name.to_string(), def: ctor_id }, line }];
        }
        vec![]
    }

    // -- helpers ---------------------------------------------------------------

    pub(super) fn fresh_name(&mut self, prefix: &str) -> String {
        self.lambda_counter += 1;
        format!("__{}{}", prefix, self.lambda_counter)
    }

    /// Unify `ty` with `new` allowing the nothing/result joins: if one side
    /// is `T` and the other `T | nothing` (or a result), the plain side is
    /// lifted. Only the *types* are joined here; `coerce_join` lifts the
    /// expression.
    pub(super) fn join_into(&mut self, target: &Type, new: &Type, line: usize) {
        let t = self.store.shallow(target);
        let n = self.store.shallow(new);
        match (&t, &n) {
            (Type::Var(_), Type::Unit) => {
                let inner = self.store.fresh();
                self.store.unify(target, &Type::maybe(inner)).ok();
            }
            (Type::Maybe(inner), Type::Unit) => {
                let _ = inner;
            }
            (Type::Maybe(inner), other) if !matches!(other, Type::Maybe(_) | Type::Var(_)) => {
                let inner = (**inner).clone();
                self.unify(&inner, new, line, "value");
            }
            (Type::Result(_, a), other) if !matches!(other, Type::Result(_, _) | Type::Var(_)) => {
                let a = (**a).clone();
                self.unify(&a, new, line, "value");
            }
            (_, Type::Maybe(inner)) if !matches!(t, Type::Maybe(_) | Type::Var(_) | Type::Unit) => {
                let inner = (**inner).clone();
                self.unify(target, &inner, line, "value");
            }
            (Type::Unit, Type::Maybe(_)) => {}
            _ => {
                self.unify(target, new, line, "value");
            }
        }
    }

    /// Lift `value` into `target`'s shape when target is `T | nothing` or a
    /// result and the value is a plain `T` (or `nothing`).
    pub(super) fn coerce_join(&mut self, value: TExpr, target: &Type, line: usize) -> TExpr {
        let t = self.store.shallow(target);
        let v = self.store.shallow(&value.ty);
        // an integer literal in a float position is a float literal
        if let (Type::Float, TExprKind::Lit(Lit::Int(i))) = (&t, &value.kind) {
            return TExpr { kind: TExprKind::Lit(Lit::Float(*i as f64)), ty: Type::Float, line };
        }
        if let (Type::Float, TExprKind::Neg(inner)) = (&t, &value.kind) {
            if let TExprKind::Lit(Lit::Int(i)) = inner.kind {
                return TExpr { kind: TExprKind::Lit(Lit::Float(-(i as f64))), ty: Type::Float, line };
            }
        }
        match (&t, &v) {
            (Type::Maybe(inner), Type::Unit) => {
                let _ = inner;
                Self::unit_as_nothing(value, t.clone(), line)
            }
            (Type::Maybe(inner), other) if !matches!(other, Type::Maybe(_)) => {
                let inner = (**inner).clone();
                self.unify(&inner, &value.ty, line, "value");
                TExpr { kind: TExprKind::MakeSome(Box::new(value)), ty: t.clone(), line }
            }
            (Type::Result(_, a), other) if !matches!(other, Type::Result(_, _) | Type::Var(_)) => {
                let a = (**a).clone();
                self.unify(&a, &value.ty, line, "value");
                TExpr { kind: TExprKind::MakeOk(Box::new(value)), ty: t.clone(), line }
            }
            (Type::Var(_), Type::Unit) => {
                let inner = self.store.fresh();
                let m = Type::maybe(inner);
                self.store.unify(target, &m).ok();
                Self::unit_as_nothing(value, m, line)
            }
            _ => value,
        }
    }

    /// A unit-typed value in a `T | nothing` position is `nothing`; an
    /// expression with effects (a call) still runs first.
    fn unit_as_nothing(value: TExpr, m: Type, line: usize) -> TExpr {
        let nothing = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: m.clone(), line };
        match &value.kind {
            TExprKind::Lit(_) | TExprKind::Local(_) => nothing,
            _ => {
                let stmts = vec![TStmt { kind: TStmtKind::Expr(value), line }, TStmt { kind: TStmtKind::Expr(nothing), line }];
                TExpr { kind: TExprKind::Block(TBlock { stmts }), ty: m, line }
            }
        }
    }
}

impl Infer {
    pub(super) fn is_prescanned_method(&self, rec: RecId, name: &str) -> bool {
        match &self.records[rec].kind {
            RecordKind::Class { method_names, .. } => method_names.iter().any(|m| m == name),
            _ => false,
        }
    }

    /// The value type of a block: its last expression statement, or the
    /// join of the branches of a trailing if/match statement. None when
    /// the block always leaves through `return`/`break`/`continue`.
    pub(super) fn block_value_type(&mut self, b: &TBlock, line: usize) -> Option<Type> {
        if block_terminates(b) {
            return None;
        }
        match b.stmts.last() {
            Some(TStmt { kind: TStmtKind::Expr(v), .. }) => Some(v.ty.clone()),
            Some(TStmt { kind: TStmtKind::If { then, elifs, else_, .. }, .. }) => {
                let mut vals: Vec<Option<Type>> = vec![self.block_value_type(then, line)];
                for (_, b) in elifs {
                    vals.push(self.block_value_type(b, line));
                }
                match else_ {
                    Some(b) => vals.push(self.block_value_type(b, line)),
                    None => vals.push(Some(Type::Unit)),
                }
                if vals.iter().all(|v| v.is_none()) {
                    return None;
                }
                // branches that only assign (or are missing) give the statement
                // no value; a branch with a value makes the others `nothing`
                if vals.iter().all(|v| matches!(v, None | Some(Type::Unit))) {
                    return Some(Type::Unit);
                }
                // a branch of a not yet known type (a method call resolved later)
                // beside a valueless one: leave the statement without a value
                let unknown = vals.iter().any(|v| matches!(v, Some(t) if matches!(self.store.shallow(t), Type::Var(_))));
                let valueless = vals.iter().any(|v| matches!(v, None | Some(Type::Unit)));
                if unknown && valueless {
                    return Some(Type::Unit);
                }
                let r = self.store.fresh();
                // `nothing` first so that plain values lift into `T | nothing`
                let mut ordered: Vec<Type> = vals.into_iter().flatten().collect();
                ordered.sort_by_key(|t| if matches!(self.store.shallow(t), Type::Unit) { 0 } else { 1 });
                for t in ordered {
                    self.join_into(&r, &t, line);
                }
                Some(r)
            }
            Some(TStmt { kind: TStmtKind::Match { arms, .. }, .. }) => {
                // arms of plainly different concrete types: the match was a
                // statement (e.g. pushing to different lists) with no value
                let tys: Vec<Type> = arms.iter().map(|a| self.store.resolve(&a.body.ty)).collect();
                let concrete = |t: &Type| {
                    let mut vs = Vec::new();
                    self_free_vars(&self.store, t, &mut vs);
                    vs.is_empty() && !matches!(t, Type::Unit | Type::Maybe(_) | Type::Result(_, _))
                };
                if tys.iter().all(concrete) && tys.windows(2).any(|w| w[0] != w[1]) {
                    return Some(Type::Unit);
                }
                if tys.iter().all(|t| matches!(t, Type::Unit)) {
                    return Some(Type::Unit);
                }
                let r = self.store.fresh();
                let mut ordered: Vec<Type> = arms.iter().map(|a| a.body.ty.clone()).collect();
                ordered.sort_by_key(|t| if matches!(self.store.shallow(t), Type::Unit) { 0 } else { 1 });
                for t in ordered {
                    self.join_into(&r, &t, line);
                }
                Some(r)
            }
            _ => Some(Type::Unit),
        }
    }

    /// Rewrite a trailing if/match statement into an expression statement
    /// so the block has a value.
    pub(super) fn tail_to_expr(&mut self, b: &mut TBlock) {
        let line = b.stmts.last().map(|s| s.line).unwrap_or(0);
        let ty = match self.block_value_type(b, line) {
            Some(t) => t,
            None => return,
        };
        let ty = self.store.shallow(&ty);
        if let Type::Unit = ty {
            return;
        }
        match b.stmts.pop() {
            Some(TStmt { kind: TStmtKind::If { cond, mut then, elifs, else_ }, line }) => {
                self.tail_to_expr(&mut then);
                let then_e = self.block_as_expr(then, &ty, line);
                let mut else_e: Option<TExpr> = match else_ {
                    Some(mut eb) => {
                        self.tail_to_expr(&mut eb);
                        Some(self.block_as_expr(eb, &ty, line))
                    }
                    None => None,
                };
                for (c, mut eb) in elifs.into_iter().rev() {
                    self.tail_to_expr(&mut eb);
                    let be = self.block_as_expr(eb, &ty, line);
                    let ee = match else_e.take() {
                        Some(e) => e,
                        None => {
                            let n = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
                            self.coerce_join(n, &ty, line)
                        }
                    };
                    else_e = Some(TExpr { kind: TExprKind::If { cond: Box::new(c), then: Box::new(be), else_: Box::new(ee) }, ty: ty.clone(), line });
                }
                let else_e = match else_e {
                    Some(e) => e,
                    None => {
                        let n = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
                        self.coerce_join(n, &ty, line)
                    }
                };
                let e = TExpr { kind: TExprKind::If { cond: Box::new(cond), then: Box::new(then_e), else_: Box::new(else_e) }, ty: ty.clone(), line };
                b.stmts.push(TStmt { kind: TStmtKind::Expr(e), line });
            }
            Some(TStmt { kind: TStmtKind::Match { subject, arms }, line }) => {
                let arms: Vec<TArm> = arms
                    .into_iter()
                    .map(|a| {
                        let body = self.coerce_join(a.body, &ty, a.line);
                        TArm { pattern: a.pattern, guard: a.guard, body, line: a.line }
                    })
                    .collect();
                let e = TExpr { kind: TExprKind::Match { subject: Box::new(subject), arms }, ty: ty.clone(), line };
                b.stmts.push(TStmt { kind: TStmtKind::Expr(e), line });
            }
            Some(other) => b.stmts.push(other),
            None => {}
        }
    }

    /// A block as an expression of type `ty` (its trailing expression
    /// coerced into `ty`).
    fn block_as_expr(&mut self, mut b: TBlock, ty: &Type, line: usize) -> TExpr {
        if block_terminates(&b) {
            return TExpr { kind: TExprKind::Block(b), ty: ty.clone(), line };
        }
        if let Some(TStmt { kind: TStmtKind::Expr(v), line: l }) = b.stmts.pop() {
            let v = self.coerce_join(v, ty, l);
            self.unify(ty, &v.ty, l, "branch value");
            b.stmts.push(TStmt { kind: TStmtKind::Expr(v), line: l });
        } else {
            let n = TExpr { kind: TExprKind::Lit(Lit::Nothing), ty: Type::Unit, line };
            let n = self.coerce_join(n, ty, line);
            b.stmts.push(TStmt { kind: TStmtKind::Expr(n), line });
        }
        TExpr { kind: TExprKind::Block(b), ty: ty.clone(), line }
    }
}

/// Does every path through the block end in return/break/continue?
pub fn block_terminates(b: &TBlock) -> bool {
    match b.stmts.last() {
        Some(TStmt { kind: TStmtKind::Return(_) | TStmtKind::Break | TStmtKind::Continue, .. }) => true,
        Some(TStmt { kind: TStmtKind::If { then, elifs, else_: Some(e), .. }, .. }) => {
            block_terminates(then) && elifs.iter().all(|(_, b)| block_terminates(b)) && block_terminates(e)
        }
        _ => false,
    }
}

pub(super) fn param_name(p: &ast::Pattern) -> Option<String> {
    match p {
        ast::Pattern::Identifier(n) => Some(n.clone()),
        ast::Pattern::Typed { pattern, .. } => param_name(pattern),
        _ => None,
    }
}

/// Scan a constructor body: declared bindings (name, public, mutable), the
/// free names of every function defined in it, and whether it spreads a
/// parent.
/// The free names of a lambda: those of its body and defaults, minus its
/// parameters.
fn lambda_free_names(params: &[ast::Param], body: &ast::Expression) -> HashSet<String> {
    let mut free = HashSet::new();
    free_names_expr(body, &mut free);
    for p in params {
        if let Some(d) = &p.default {
            free_names_expr(d, &mut free);
        }
        if let Some(pn) = param_name(&p.pattern) {
            free.remove(&pn);
        }
    }
    free
}

/// The binding an access chain starts from: `xs` in `xs[i].items`; `$`
/// for the piped value.
fn access_root(e: &ast::Expression) -> Option<&str> {
    match e {
        ast::Expression::Identifier(n) => Some(n.as_str()),
        ast::Expression::PreviousResult => Some("$"),
        ast::Expression::MemberAccess { object, .. } | ast::Expression::Index { object, .. } => access_root(object),
        _ => None,
    }
}

fn collect_class_body(body: &[ast::Stmt], declared: &mut Vec<(String, bool, bool)>, funcs: &mut Vec<(String, bool, HashSet<String>)>, has_parent: &mut Option<Option<String>>) {
    for s in body {
        match &s.node {
            ast::Statement::Declaration { is_public, is_mutable, pattern, value } => {
                if let (ast::Pattern::Identifier(n), ast::Expression::Lambda { params, body }) = (pattern, value) {
                    funcs.push((n.clone(), *is_public, lambda_free_names(params, body)));
                    declared.push((n.clone(), *is_public, *is_mutable));
                    continue;
                }
                let mut names = Vec::new();
                pattern_names(pattern, &mut names);
                for n in names {
                    declared.push((n, *is_public, *is_mutable));
                }
            }
            ast::Statement::Def { is_public, name, params, body: fbody, .. } => {
                let mut free = HashSet::new();
                free_names_block(fbody, &mut free);
                for p in params {
                    if let Some(d) = &p.default {
                        free_names_expr(d, &mut free);
                    }
                    if let Some(pn) = param_name(&p.pattern) {
                        free.remove(&pn);
                    }
                }
                funcs.push((name.clone(), *is_public, free));
                declared.push((name.clone(), *is_public, false));
            }
            ast::Statement::Assignment { targets, value } => {
                // `helper = (a, b) => ...` (no `public`/`var`) parses as an
                // assignment; it is a private function of the body
                if let ([(ast::Pattern::Identifier(n), ast::AssignmentOp::Assign)], ast::Expression::Lambda { params, body }) = (targets.as_slice(), value) {
                    funcs.push((n.clone(), false, lambda_free_names(params, body)));
                    declared.push((n.clone(), false, false));
                    continue;
                }
                for (t, _) in targets {
                    if let ast::Pattern::SpreadInto { .. } = t {
                        // `self.{...} = parent` where `parent` is a binding of the
                        // class body: that binding is the parent field itself
                        let src = match value {
                            ast::Expression::Identifier(n) if targets.len() == 1 => Some(n.clone()),
                            _ => None,
                        };
                        *has_parent = Some(src);
                        // remember where the inherited members appear
                        declared.push(("__spread".into(), false, false));
                    }
                    if let ast::Pattern::Identifier(n) = t {
                        declared.push((n.clone(), false, false));
                    }
                }
            }
            ast::Statement::If { body, elif_branches, else_body, .. } => {
                collect_class_body(body, declared, funcs, has_parent);
                for (_, b) in elif_branches {
                    collect_class_body(b, declared, funcs, has_parent);
                }
                if let Some(b) = else_body {
                    collect_class_body(b, declared, funcs, has_parent);
                }
            }
            ast::Statement::For { body, .. } | ast::Statement::While { body, .. } => {
                collect_class_body(body, declared, funcs, has_parent);
            }
            _ => {}
        }
    }
}

fn pattern_names(p: &ast::Pattern, out: &mut Vec<String>) {
    match p {
        ast::Pattern::Identifier(n) => out.push(n.clone()),
        ast::Pattern::Typed { pattern, .. } => pattern_names(pattern, out),
        ast::Pattern::List(items) => {
            for i in items {
                pattern_names(i, out);
            }
        }
        ast::Pattern::Rest(Some(n)) => out.push(n.clone()),
        ast::Pattern::Object(fields) => {
            for (_, p) in fields {
                pattern_names(p, out);
            }
        }
        _ => {}
    }
}

pub(super) fn int_lit(v: i64, line: usize) -> TExpr {
    TExpr { kind: TExprKind::Lit(Lit::Int(v)), ty: Type::Int, line }
}

fn self_free_vars(store: &crate::types::TypeStore, t: &Type, out: &mut Vec<crate::types::TVar>) {
    store.free_vars(t, out);
}

pub(super) fn is_container_mutation_expr(e: &ast::Expression) -> bool {
    container_mutation(e).is_some()
}

/// `recv.push(args)` / `recv.pop()` at the top of an expression.
fn container_mutation(e: &ast::Expression) -> Option<(&ast::Expression, &str, &[ast::Expression])> {
    if let ast::Expression::Call { function, args, named_args } = e {
        if let ast::Expression::MemberAccess { object, member, safe: false } = &**function {
            if named_args.is_empty() && (member == "push" || member == "pop") {
                return Some((object, member.as_str(), args.as_slice()));
            }
        }
    }
    None
}

impl Infer {
    /// `xs.push(v)` / `xs.pop()` on a receiver whose type is still open (a
    /// parameter, or a member typed by one). The statement is rewritten to
    /// rebind the container *now*, while it is being typed, so the receiver
    /// has to be decided now too: push and pop are list methods, so fix it
    /// as a list. Leaving it open would compile the mutation to a discarded
    /// expression once the type turned out to be a list.
    ///
    /// When a class in the program declares a method of the same name the
    /// receiver is left open (it may be that class); a list arriving there
    /// later is reported instead of silently dropped.
    pub(super) fn pin_list_receiver(&mut self, recv: &Type, method: &str, line: usize) {
        if !matches!(self.store.shallow(recv), Type::Var(_)) {
            return;
        }
        let class_has_method = (0..self.records.len()).any(|r| self.records[r].method(method).is_some() || self.is_prescanned_method(r, method));
        if class_has_method {
            self.defer(Pending::ListMutation { recv: recv.clone(), method: method.to_string(), line });
            return;
        }
        let elem = self.store.fresh();
        self.unify(recv, &Type::list(elem), line, &format!("receiver of .{}()", method));
    }

    /// Is an expression-bodied function's body `xs.push(v)` / `xs.pop()`
    /// on something outside the function (a member, an outer binding)?
    /// On one of its own parameters (or `$`) nothing outside could see the
    /// rebinding, so the body stays a value: `*> $.push(0)` maps to the
    /// extended lists.
    fn body_mutates_container(&self, e: &ast::Expression, params: &[TParam]) -> bool {
        match container_mutation(e).and_then(|(recv, _, _)| access_root(recv)) {
            Some("$") | None => false,
            Some(root) => !params.iter().any(|p| p.name == root),
        }
    }

    /// The statements a mutation-bodied function runs: the mutation, and
    /// for `pop` the element it answers.
    fn container_mutation_body(&mut self, e: &ast::Expression, line: usize) -> Vec<ast::Stmt> {
        match container_mutation(e) {
            Some((_, "pop", _)) => {
                let r = self.fresh_name("r");
                vec![
                    ast::Stmt { node: ast::Statement::Declaration { is_public: false, is_mutable: false, pattern: ast::Pattern::Identifier(r.clone()), value: e.clone() }, line },
                    ast::Stmt { node: ast::Statement::Expression(ast::Expression::Identifier(r)), line },
                ]
            }
            _ => vec![ast::Stmt { node: ast::Statement::Expression(e.clone()), line }],
        }
    }

    /// After `xs.pop()` was read as a value: `xs = xs.drop_last()`.
    fn pop_rebind(&mut self, recv: &ast::Expression, line: usize) -> Vec<TStmt> {
        let recv_e = self.infer_expr(recv, line);
        self.pin_list_receiver(&recv_e.ty, "pop", line);
        if let Type::List(_) = self.store.shallow(&recv_e.ty) {
            let new_value = self.method_call_pub(recv_e.clone(), "drop_last", vec![], line);
            return self.rebind_root(recv_e, new_value, line);
        }
        vec![]
    }
}

impl Infer {
    /// The def to call for `def(args)`: the def itself when its parameter
    /// types accept the arguments, else a copy of its source re-inferred at
    /// the argument types (memoized by those types).
    pub(super) fn template_instance(&mut self, def: DefId, args: &[TExpr], line: usize) -> DefId {
        let (scheme, src, name) = match &self.defs[def] {
            Some(d) => match &d.template {
                Some(t) => (d.scheme.clone(), t.clone(), d.name.clone()),
                None => return def,
            },
            None => return def,
        };
        let (decl_frame, decl_scope) = src.decl;
        if decl_frame >= self.frames.len() || decl_scope >= self.frames[decl_frame].scopes.len() {
            return def;
        }
        // do the argument types fit the def as it is?
        let saved = self.store.clone();
        let (fty, _) = self.store.instantiate(&scheme);
        let params = match self.store.shallow(&fty) {
            Type::Fn(params, _, _) => params,
            _ => return def,
        };
        if params.len() != args.len() {
            return def;
        }
        // an argument whose type is not known yet against a parameter the
        // def has already fixed: decided once the argument type is known
        let undecided = params.iter().zip(args).any(|(p, a)| !matches!(self.store.shallow(p), Type::Var(_)) && matches!(self.store.shallow(&a.ty), Type::Var(_)));
        let fits = params.iter().zip(args).all(|(p, a)| self.store.unify(p, &a.ty).is_ok());
        self.store = saved;
        if fits && !undecided {
            return def;
        }
        if fits {
            // a placeholder def with the argument types; its body is inferred
            // when the enclosing function is done (see `finish_lazy_copies`)
            let id = self.new_def(&name, DefKind::Plain, line);
            let ps: Vec<Type> = args.iter().map(|a| a.ty.clone()).collect();
            let r = self.store.fresh();
            let placeholder = self.store.fresh_fn(ps, r);
            self.placeholders.insert(id, placeholder.clone());
            if let Some(list) = self.lazy_copies.last_mut() {
                list.push(LazyCopy { id, def, placeholder, line });
            }
            return id;
        }
        let arg_tys: Vec<Type> = args.iter().map(|a| self.store.resolve(&a.ty)).collect();
        let key = arg_tys.iter().map(|t| self.type_name(t)).collect::<Vec<_>>().join(", ");
        if let Some(&c) = self.copies.get(&(def, key.clone())) {
            return c;
        }
        let id = self.new_def(&name, DefKind::Plain, line);
        self.infer_copy(id, def, &key, &arg_tys, line);
        id
    }

    /// Infer `id` as a copy of `def` at the argument types, in the scope
    /// where `def` was declared.
    fn infer_copy(&mut self, id: DefId, def: DefId, key: &str, arg_tys: &[Type], line: usize) {
        let (src, name) = match &self.defs[def] {
            Some(d) => (d.template.clone().unwrap(), d.name.clone()),
            None => return,
        };
        let (decl_frame, decl_scope) = src.decl;
        self.copies.insert((def, key.to_string()), id);
        let inner_frames: Vec<Frame> = self.frames.drain(decl_frame + 1..).collect();
        let inner_scopes: Vec<Scope> = self.frames[decl_frame].scopes.drain(decl_scope + 1..).collect();
        let saved_pending = std::mem::take(&mut self.pending);
        self.infer_function_with(id, &name, DefKind::Plain, &src.params, src.return_type.as_ref(), Some(&src.body), None, line, Some(arg_tys));
        let mut copy_pending = std::mem::replace(&mut self.pending, saved_pending);
        self.pending.append(&mut copy_pending);
        self.frames[decl_frame].scopes.extend(inner_scopes);
        self.frames.extend(inner_frames);
        if let Some(d) = self.defs[id].as_mut() {
            d.template_of = Some(def);
        }
    }

    /// The lazy copies requested while inferring the function that just
    /// finished: infer each at its (now known) argument types, or fall back
    /// to the def itself when they are still unknown.
    pub(super) fn finish_lazy_copies(&mut self) {
        let list = match self.lazy_copies.pop() {
            Some(l) => l,
            None => return,
        };
        for lc in list {
            let LazyCopy { id, def, placeholder, line } = lc;
            let (params, ret) = match self.store.shallow(&placeholder) {
                Type::Fn(p, r, _) => (p, *r),
                _ => continue,
            };
            let arg_tys: Vec<Type> = params.iter().map(|p| self.store.resolve(p)).collect();
            let known = arg_tys.iter().all(|t| {
                let mut vs = Vec::new();
                self.store.free_vars(t, &mut vs);
                vs.is_empty()
            });
            let decl_ok = match &self.defs[def] {
                Some(d) => d.template.as_ref().is_some_and(|t| t.decl.0 < self.frames.len() && t.decl.1 < self.frames[t.decl.0].scopes.len()),
                None => false,
            };
            // does the def itself fit now?
            let saved = self.store.clone();
            let fits = match &self.defs[def] {
                Some(d) => {
                    let (fty, _) = self.store.instantiate(&d.scheme);
                    match self.store.shallow(&fty) {
                        Type::Fn(ps, _, _) => ps.iter().zip(arg_tys.iter()).all(|(p, a)| self.store.unify(p, a).is_ok()),
                        _ => true,
                    }
                }
                None => true,
            };
            self.store = saved;
            let target: DefId = if fits || !known || !decl_ok {
                def
            } else {
                let key = arg_tys.iter().map(|t| self.type_name(t)).collect::<Vec<_>>().join(", ");
                match self.copies.get(&(def, key.clone())) {
                    Some(&c) => c,
                    None => {
                        self.infer_copy(id, def, &key, &arg_tys, line);
                        id
                    }
                }
            };
            self.placeholders.remove(&id);
            if target != id {
                // the placeholder stands for an existing def: same body
                let (fty, tdef) = match &self.defs[target] {
                    Some(d) => {
                        let (t, _) = self.store.instantiate(&d.scheme);
                        (t, d.clone())
                    }
                    None => {
                        let t = self.def_value_type(target, line);
                        (t, TDef { id, ..self.defs[def].clone().unwrap() })
                    }
                };
                let mut copy = tdef;
                copy.id = id;
                copy.template = None;
                copy.template_of = Some(self.defs[target].as_ref().and_then(|d| d.template_of).unwrap_or(target));
                self.defs[id] = Some(copy);
                self.unify(&placeholder, &fty, line, "template call");
            } else {
                let fty = self.def_value_type(id, line);
                let _ = ret;
                self.unify(&placeholder, &fty, line, "template call");
            }
        }
    }
}

pub struct LazyCopy {
    pub id: DefId,
    pub def: DefId,
    pub placeholder: Type,
    pub line: usize,
}
