// src/check/classes.rs
// Classes (a `def` with `public` members) and declared data types.
//
// A class is a data type with one constructor whose fields are every
// binding the constructor declares (public ones show and compare, the rest
// are private state), plus a def per method. Inside the constructor and
// the methods, members are locals: the constructor ends by building the
// object from them, and a method opens its receiver into them (the
// lowering emits that match) and, when it assigned one, rebuilds the
// receiver at its end. An adopted parent (`self.{...} = parent`) is a
// private field; its public members are reached through it.

use super::*;

impl Checker {
    // -- declared types ------------------------------------------------------------

    /// First pass: the type with its parameters (one per untyped field, in
    /// order of first appearance) and its constructors, fields untyped.
    pub(crate) fn declare_type(&mut self, name: &str, ctors: &[ast::CtorDecl], line: usize) {
        if self.type_names.contains_key(name) {
            self.error(line, format!("type {} is declared twice", name));
            return;
        }
        let mut params: Vec<(String, TVar)> = Vec::new();
        let mut cs = Vec::new();
        for c in ctors {
            let mut fields = Vec::new();
            for (f, t) in &c.fields {
                let ty = match t {
                    None => {
                        let v = self.store.fresh_var();
                        params.push((f.clone(), v));
                        Type::Var(v)
                    }
                    Some(_) => self.fresh(),
                };
                fields.push(FieldDef { name: f.clone(), ty, public: true });
            }
            cs.push(Ctor { name: c.name.clone(), fields });
        }
        let id = self.types.len();
        self.types.push(DataType { name: name.to_string(), params: params.iter().map(|(_, v)| *v).collect(), ctors: cs, kind: DataKind::Declared, line });
        self.type_names.insert(name.to_string(), id);
        for (ci, c) in ctors.iter().enumerate() {
            if self.ctor_names.contains_key(&c.name) || self.type_names.contains_key(&c.name) {
                self.error(line, format!("constructor {} is declared twice", c.name));
            }
            self.ctor_names.insert(c.name.clone(), (id, ci));
            // constructors are global names
            self.frames[0].scopes[0].names.insert(c.name.clone(), Binding::Ctor(id, ci));
        }
    }

    /// Second pass: typed fields, which may mention any declared type,
    /// including the one being declared (with the same parameters).
    pub(crate) fn fill_type(&mut self, name: &str, ctors: &[ast::CtorDecl], line: usize) {
        let id = match self.type_names.get(name) {
            Some(id) => *id,
            None => return,
        };
        let self_ty = Type::Data(id, self.types[id].params.iter().map(|v| Type::Var(*v)).collect());
        for (ci, c) in ctors.iter().enumerate() {
            for (fi, (_, t)) in c.fields.iter().enumerate() {
                if let Some(t) = t {
                    let ty = match t {
                        ast::Expression::Identifier(n) if n == name => self_ty.clone(),
                        ast::Expression::List(items) if items.len() == 1 && matches!(&items[0], ast::Expression::Identifier(n) if n == name) => Type::list(self_ty.clone()),
                        ast::Expression::BinaryOp { left, op: ast::BinaryOperator::TypeOr, right }
                            if matches!(&**left, ast::Expression::Identifier(n) if n == name) && matches!(&**right, ast::Expression::Nothing | ast::Expression::Identifier(_)) =>
                        {
                            Type::maybe(self_ty.clone())
                        }
                        other => self.annotation(other, line),
                    };
                    let fty = self.types[id].ctors[ci].fields[fi].ty.clone();
                    self.unify(&fty, &ty, line);
                }
            }
        }
    }

    // -- classes ---------------------------------------------------------------------

    /// Declare a class type for a constructor def; its fields are filled
    /// when the constructor is checked. The names of its methods are noted
    /// now, so that a call on a receiver of unknown type can find them.
    pub(crate) fn declare_class(&mut self, name: &str, ctor: DefId, body: &[ast::Stmt], line: usize) -> TypeId {
        let id = self.types.len();
        for s in body {
            let method = match &s.node {
                ast::Statement::Def { name, .. } => Some(name.clone()),
                ast::Statement::Declaration { pattern: ast::Pattern::Identifier(n), value: ast::Expression::Lambda { .. }, .. } => Some(n.clone()),
                ast::Statement::Assignment { targets, value: ast::Expression::Lambda { .. } } => match targets.as_slice() {
                    [(ast::Pattern::Identifier(n), _)] => Some(n.clone()),
                    _ => None,
                },
                _ => None,
            };
            if let Some(m) = method {
                self.class_method_names.entry(m).or_default().push(id);
            }
        }
        self.types.push(DataType {
            name: name.to_string(),
            params: vec![],
            ctors: vec![Ctor { name: name.to_string(), fields: vec![] }],
            kind: DataKind::Class { ctor, methods: vec![], parent: None, show_order: vec![] },
            line,
        });
        if self.type_names.contains_key(name) {
            self.error(line, format!("{} is declared twice", name));
        }
        self.type_names.insert(name.to_string(), id);
        id
    }

    /// The type of the object being built or received: the class applied
    /// to its field variables.
    pub(crate) fn class_self_type(&self, tid: TypeId) -> Type {
        Type::Data(tid, self.types[tid].params.iter().map(|v| Type::Var(*v)).collect())
    }

    /// Add a field to a class (during its constructor) and return its index.
    fn add_field(&mut self, tid: TypeId, name: &str, public: bool) -> (usize, Type) {
        let v = self.store.fresh_var();
        self.types[tid].params.push(v);
        self.types[tid].ctors[0].fields.push(FieldDef { name: name.to_string(), ty: Type::Var(v), public });
        let idx = self.types[tid].ctors[0].fields.len() - 1;
        if public
            && let DataKind::Class { show_order, .. } = &mut self.types[tid].kind {
                show_order.push(idx);
            }
        (idx, Type::Var(v))
    }

    /// Check a class constructor: parameters and body declare the members,
    /// lambdas and defs assigned to members are the methods, and the body
    /// ends by building the object.
    pub(crate) fn check_ctor_body(&mut self, id: DefId, tid: TypeId, source: &Source) -> (Vec<Param>, Block) {
        let line = self.defs[id].line;
        // parameters: every one is a member (public ones show)
        let mut params = Vec::new();
        for (i, p) in source.params.iter().enumerate() {
            let name = match &p.pattern {
                ast::Pattern::Identifier(n) => n.clone(),
                ast::Pattern::Typed { pattern, .. } => match &**pattern {
                    ast::Pattern::Identifier(n) => n.clone(),
                    _ => format!("__p{}", i),
                },
                _ => {
                    self.error(line, "class parameters are plain names");
                    format!("__p{}", i)
                }
            };
            let ty = match &p.pattern {
                ast::Pattern::Typed { type_expr, .. } => self.annotation(type_expr, line),
                _ => self.fresh(),
            };
            let (_, fty) = self.add_field(tid, &name, p.is_public);
            self.unify(&fty, &ty, line);
            self.declare(&name, Binding::Member { root: name.clone(), root_ty: fty.clone(), path: vec![], ty: fty.clone(), mutable: p.is_var });
            params.push(Param { name, ty: fty });
        }
        // defaults, in the constructor's own frame
        let defaults: Vec<Option<Expr>> = source.params.iter().zip(params.iter()).map(|(p, cp)| {
            p.default.as_ref().map(|d| {
                let x = self.check_expr(d, Some(&cp.ty));
                self.unify(&cp.ty, &x.ty, line);
                x
            })
        }).collect();
        self.defs[id].defaults = defaults;
        // every member and method the body declares, before any type
        // mentions the class (its parameters are its fields)
        self.prescan_members(tid, &source.body);
        self.hoist_defs(&source.body);
        // the monomorphic type is visible from here on
        let ptys: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();
        let selft = self.class_self_type(tid);
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(ptys, Box::new(selft), c);
        let mono = self.defs[id].mono.clone();
        self.unify(&mono, &fty, line);
        self.defs[id].params = params.clone();
        let mut body = self.check_block_stmts(&source.body);
        // the methods, while the constructor's scope is in place
        let methods: Vec<DefId> = match &self.types[tid].kind {
            DataKind::Class { methods, .. } => methods.iter().map(|(_, m)| *m).collect(),
            _ => vec![],
        };
        for m in methods {
            self.ensure_def(m, line);
        }
        // the object
        let fields: Vec<(String, Type)> = self.types[tid].ctors[0].fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
        let values: Vec<Expr> = fields.iter().map(|(n, t)| Expr { kind: ExprKind::Var(n.clone()), ty: t.clone(), line }).collect();
        let selft = self.class_self_type(tid);
        let obj = Expr { kind: ExprKind::Con(tid, 0, values), ty: selft, line };
        body.stmts.push(Stmt { kind: StmtKind::Return(obj), line });
        (params, body)
    }

    /// Members declared by the top-level statements of a constructor body.
    fn prescan_members(&mut self, tid: TypeId, body: &[ast::Stmt]) {
        for s in body {
            match &s.node {
                ast::Statement::Declaration { is_public, is_mutable, pattern, value } => {
                    let name = match pattern {
                        ast::Pattern::Identifier(n) => n.clone(),
                        ast::Pattern::Typed { pattern, .. } => match &**pattern {
                            ast::Pattern::Identifier(n) => n.clone(),
                            _ => continue,
                        },
                        _ => continue,
                    };
                    if let ast::Expression::Lambda { params, body } = value {
                        // a method
                        let stmts = match &**body {
                            ast::Expression::Block(stmts) => stmts.clone(),
                            other => vec![ast::Stmt { node: ast::Statement::Expression(other.clone()), line: s.line }],
                        };
                        self.declare_method(tid, &name, params, None, stmts, false, s.line);
                        continue;
                    }
                    if self.types[tid].field_index(&name).is_some() {
                        continue;
                    }
                    let (_, fty) = self.add_field(tid, &name, *is_public);
                    self.declare(&name, Binding::Member { root: name.clone(), root_ty: fty.clone(), path: vec![], ty: fty, mutable: *is_mutable });
                }
                ast::Statement::Assignment { targets, .. } if matches!(targets.as_slice(), [(ast::Pattern::SpreadInto { .. }, _)]) => {
                    // the adopted parent's members show where it is adopted
                    if let DataKind::Class { show_order, .. } = &mut self.types[tid].kind {
                        show_order.push(usize::MAX);
                    }
                }
                ast::Statement::Assignment { targets, value } => {
                    if let [(ast::Pattern::Identifier(name), ast::AssignmentOp::Assign)] = targets.as_slice() {
                        if let ast::Expression::Lambda { params, body } = value {
                            // a private method
                            let stmts = match &**body {
                                ast::Expression::Block(stmts) => stmts.clone(),
                                other => vec![ast::Stmt { node: ast::Statement::Expression(other.clone()), line: s.line }],
                            };
                            self.declare_method(tid, name, params, None, stmts, false, s.line);
                            continue;
                        }
                        if self.types[tid].field_index(name).is_none() && self.lookup(name).is_none() {
                            let (_, fty) = self.add_field(tid, name, false);
                            self.declare(name, Binding::Member { root: name.clone(), root_ty: fty.clone(), path: vec![], ty: fty, mutable: false });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// `public var count = start` (or any binding) inside a constructor.
    pub(crate) fn check_member_declaration(&mut self, tid: TypeId, is_public: bool, is_mutable: bool, pattern: &ast::Pattern, value: &ast::Expression) -> Vec<Stmt> {
        let line = self.line;
        let name = match pattern {
            ast::Pattern::Identifier(n) => n.clone(),
            ast::Pattern::Typed { pattern, .. } => match &**pattern {
                ast::Pattern::Identifier(n) => n.clone(),
                _ => {
                    self.error(line, "members are declared with plain names");
                    return vec![];
                }
            },
            _ => {
                if is_public {
                    self.error(line, "members are declared with plain names");
                    return vec![];
                }
                return self.check_let(pattern, value, is_mutable);
            }
        };
        if let ast::Expression::Lambda { .. } = value {
            // a method: declared by the prescan, checked after the body
            if let Some(m) = self.types[tid].method(&name) {
                self.ensure_def(m, line);
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
        let fty = match self.lookup(&name) {
            Some(Binding::Member { ty, .. }) => ty,
            _ => {
                let (_, fty) = self.add_field(tid, &name, is_public);
                fty
            }
        };
        self.unify(&fty, &x.ty, line);
        self.declare(&name, Binding::Member { root: name.clone(), root_ty: fty.clone(), path: vec![], ty: fty, mutable: is_mutable });
        vec![Stmt { kind: StmtKind::Let { name, value: x }, line }]
    }

    /// `self.{...} = parent`: the parent object becomes a private field and
    /// its public members and methods are reachable through it.
    pub(crate) fn check_adoption(&mut self, value: &ast::Expression) -> Vec<Stmt> {
        let line = self.line;
        let tid = match self.frame_ref().kind {
            FrameKind::Ctor(t) => t,
            _ => {
                self.error(line, "`self.{...} = parent` is only valid inside a class constructor");
                return vec![];
            }
        };
        let pname = match value {
            ast::Expression::Identifier(n) => n.clone(),
            _ => {
                self.error(line, "adopt a named parent: `parent = Animal(name)` then `self.{...} = parent`");
                return vec![];
            }
        };
        let (root_ty, pidx) = match self.lookup(&pname) {
            Some(Binding::Member { root_ty, path, .. }) if path.is_empty() => {
                let idx = self.types[tid].field_index(&pname).unwrap();
                (root_ty, idx)
            }
            _ => {
                self.error(line, format!("'{}' must be a member of this object to be adopted", pname));
                return vec![];
            }
        };
        let ptid = match self.shallow(&root_ty) {
            Type::Data(ptid, _) if matches!(self.types[ptid].kind, DataKind::Class { .. }) => ptid,
            _ => {
                self.error(line, "only an object can be adopted");
                return vec![];
            }
        };
        let already = self.types[tid].parent_field().is_some();
        if already {
            self.error(line, "an object adopts one parent");
        }
        if let DataKind::Class { parent, show_order, .. } = &mut self.types[tid].kind {
            *parent = Some(pidx);
            match show_order.iter().position(|&i| i == usize::MAX) {
                Some(k) => show_order[k] = pidx,
                None => show_order.push(pidx),
            }
        }
        // inherited members
        let pargs = match self.shallow(&root_ty) {
            Type::Data(_, a) => a,
            _ => vec![],
        };
        self.declare_inherited(&pname, &root_ty, ptid, &pargs, vec![]);
        vec![]
    }

    /// Declare the public members and methods of a parent class (and of
    /// its own parents) as reachable through `root` along `path`.
    fn declare_inherited(&mut self, root: &str, root_ty: &Type, ptid: TypeId, pargs: &[Type], path: Vec<(TypeId, usize)>) {
        let ftys = self.ctor_field_types(ptid, 0, pargs);
        let fields = self.types[ptid].ctors[0].fields.clone();
        for (i, f) in fields.iter().enumerate() {
            if f.public {
                let mut p = path.clone();
                p.push((ptid, i));
                self.declare(&f.name, Binding::Member { root: root.to_string(), root_ty: root_ty.clone(), path: p, ty: ftys[i].clone(), mutable: false });
            }
        }
        let methods: Vec<(String, DefId)> = match &self.types[ptid].kind {
            DataKind::Class { methods, .. } => methods.clone(),
            _ => vec![],
        };
        for (n, m) in methods {
            self.declare(&n, Binding::Func(m));
        }
        if let Some(gp) = self.types[ptid].parent_field()
            && let Type::Data(gtid, gargs) = self.shallow(&ftys[gp]) {
                let mut p = path.clone();
                p.push((ptid, gp));
                self.declare_inherited(root, root_ty, gtid, &gargs, p);
            }
    }

    /// Read a member: the root local, projected along the path.
    pub(crate) fn member_expr(&mut self, b: &Binding) -> Expr {
        match b {
            Binding::Member { root, root_ty, path, ty, .. } => {
                let mut e = self.var(root, root_ty.clone());
                let n = path.len();
                for (i, (tid, idx)) in path.iter().enumerate() {
                    let t = if i + 1 == n {
                        ty.clone()
                    } else {
                        let args = match self.shallow(&e.ty) {
                            Type::Data(_, a) => a,
                            _ => vec![],
                        };
                        self.ctor_field_types(*tid, 0, &args)[*idx].clone()
                    };
                    e = self.expr(ExprKind::Field(Box::new(e), *tid, *idx), t);
                }
                e
            }
            _ => unreachable!(),
        }
    }

    /// Assign a member: rebind the root local, rebuilt along the path.
    pub(crate) fn assign_member(&mut self, b: &Binding, value: Expr) -> Vec<Stmt> {
        let line = self.line;
        let (root, root_ty, path, ty, mutable) = match b {
            Binding::Member { root, root_ty, path, ty, mutable } => (root.clone(), root_ty.clone(), path.clone(), ty.clone(), *mutable),
            _ => unreachable!(),
        };
        if let FrameKind::Method(_) = self.frame_ref().kind {
            self.frame().mutates_member = true;
            if !mutable && path.is_empty() {
                self.error(line, format!("cannot assign to member '{}': declare it with `var`", root));
            }
        } else if let FrameKind::Ctor(_) = self.frame_ref().kind {
            // the constructor initializes freely
        } else {
            // a lambda inside a method: captured by value
            self.error(line, format!("cannot assign to '{}' from a lambda; state that changes lives in the object", root));
        }
        self.unify(&ty, &value.ty, line);
        if path.is_empty() {
            return vec![Stmt { kind: StmtKind::Assign { name: root, value }, line }];
        }
        // rebuild along the path
        let mut readers = vec![self.var(&root, root_ty.clone())];
        for (i, (tid, idx)) in path.iter().enumerate() {
            let prev = readers[i].clone();
            let args = match self.shallow(&prev.ty) {
                Type::Data(_, a) => a,
                _ => vec![],
            };
            let t = self.ctor_field_types(*tid, 0, &args)[*idx].clone();
            readers.push(self.expr(ExprKind::Field(Box::new(prev), *tid, *idx), t));
        }
        let mut acc = value;
        for (i, (tid, idx)) in path.iter().enumerate().rev() {
            let holder = readers[i].clone();
            let ht = holder.ty.clone();
            acc = self.expr(ExprKind::SetField(Box::new(holder), *tid, *idx, Box::new(acc)), ht);
        }
        vec![Stmt { kind: StmtKind::Assign { name: root, value: acc }, line }]
    }

    /// Declare a method of a class from its source; it is checked when
    /// first needed or after the constructor body.
    pub(crate) fn declare_method(&mut self, tid: TypeId, name: &str, params: &[ast::Param], return_type: Option<ast::Expression>, body: Vec<ast::Stmt>, is_unsafe: bool, line: usize) {
        let frame_index = self.frames.len() - 1;
        let id = self.new_def(name, DefKind::Method { rec: tid, mutates: false, returns_value: false }, None, line);
        self.defs[id].unsafe_ = is_unsafe || self.frame_ref().unsafe_;
        self.defs[id].class = Some(tid);
        self.defs[id].source = Some(Source {
            params: params.to_vec(),
            return_type,
            body,
            frame: frame_index,
            depth: 0,
        });
        if let DataKind::Class { methods, .. } = &mut self.types[tid].kind {
            methods.retain(|(n, _)| n != name);
            methods.push((name.to_string(), id));
        }
        self.declare(name, Binding::Func(id));
    }

    /// Check a method: `self` first, then its own parameters, members as
    /// locals; a mutating method's return is rewritten by the caller.
    pub(crate) fn check_method_body(&mut self, id: DefId, tid: TypeId, source: &Source) -> (Vec<Param>, Block) {
        let line = self.defs[id].line;
        let mut params = self.method_prologue(tid);
        let own = self.check_params(&source.params, line);
        if let Some(rt) = &source.return_type {
            let t = self.annotation(rt, line);
            let ret = self.frame_ref().ret.clone();
            self.unify(&ret, &t, line);
        }
        let mut defaults: Vec<Option<Expr>> = vec![None];
        defaults.extend(source.params.iter().zip(own.iter()).map(|(p, cp)| {
            p.default.as_ref().map(|d| {
                let x = self.check_expr(d, Some(&cp.ty));
                self.unify(&cp.ty, &x.ty, line);
                x
            })
        }));
        let mut param_stmts = Vec::new();
        for (p, ast_p) in own.iter().zip(source.params.iter()) {
            param_stmts.extend(self.destructure_param(p, &ast_p.pattern));
        }
        params.extend(own);
        let ptys: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();
        let ret = self.frame_ref().ret.clone();
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(ptys, Box::new(ret), c);
        let mono = self.defs[id].mono.clone();
        self.unify(&mono, &fty, line);
        self.defs[id].params = params.clone();
        self.defs[id].defaults = defaults;
        self.hoist_defs(&source.body);
        let mut body = self.check_block_stmts(&source.body);
        param_stmts.append(&mut body.stmts);
        body.stmts = param_stmts;
        self.finish_body_value(&mut body, line);
        (params, body)
    }

    /// The `self` parameter of a method, with every member (own and
    /// inherited) declared as reachable from it.
    pub(crate) fn method_prologue(&mut self, tid: TypeId) -> Vec<Param> {
        let selft = self.class_self_type(tid);
        let self_name = "self".to_string();
        self.declare(&self_name, Binding::Local { ty: selft.clone(), mutable: false });
        let fields = self.types[tid].ctors[0].fields.clone();
        for f in &fields {
            // own members: locals opened from self by the lowering
            self.declare(&f.name, Binding::Member { root: f.name.clone(), root_ty: f.ty.clone(), path: vec![], ty: f.ty.clone(), mutable: true });
        }
        if let Some(pidx) = self.types[tid].parent_field() {
            let pf = fields[pidx].clone();
            if let Type::Data(ptid, pargs) = self.shallow(&pf.ty) {
                self.declare_inherited(&pf.name, &pf.ty, ptid, &pargs, vec![]);
            }
        }
        // own methods, by bare name
        let methods: Vec<(String, DefId)> = match &self.types[tid].kind {
            DataKind::Class { methods, .. } => methods.clone(),
            _ => vec![],
        };
        for (n, m) in methods {
            self.declare(&n, Binding::Func(m));
        }
        vec![Param { name: self_name, ty: selft }]
    }

    /// A mutating method answers the rebuilt receiver (and its value).
    pub(crate) fn method_epilogue(&mut self, tid: TypeId, body: &mut Block, returns_value: bool) {
        let selft = self.class_self_type(tid);
        rewrite_returns(body, &mut |e: Expr| {
            let line = e.line;
            let sv = Expr { kind: ExprKind::SelfValue(tid), ty: selft.clone(), line };
            if returns_value {
                let t = Type::pair(selft.clone(), e.ty.clone());
                Expr { kind: ExprKind::Con(PAIR, 0, vec![sv, e]), ty: t, line }
            } else {
                sv
            }
        });
    }

    /// The type a method's receiver has: its own class.
    pub(crate) fn class_self_type_for_method(&self, m: DefId) -> Type {
        match self.defs[m].class {
            Some(tid) => self.class_self_type(tid),
            None => Type::Unit,
        }
    }

    /// The object a method is called on: the receiver itself, or the
    /// adopted parent that owns the method.
    pub(crate) fn receiver_for(&mut self, recv: Expr, tid: TypeId, m: DefId) -> Expr {
        let owner = self.defs[m].class.unwrap_or(tid);
        if owner == tid {
            return recv;
        }
        let pidx = match self.types[tid].parent_field() {
            Some(p) => p,
            None => return recv,
        };
        let args = match self.shallow(&recv.ty) {
            Type::Data(_, a) => a,
            _ => vec![],
        };
        let pty = self.ctor_field_types(tid, 0, &args)[pidx].clone();
        let parent = self.expr(ExprKind::Field(Box::new(recv), tid, pidx), pty.clone());
        match self.shallow(&pty) {
            Type::Data(ptid, _) => self.receiver_for(parent, ptid, m),
            _ => parent,
        }
    }

    /// After a mutating method: store the new object back where the
    /// receiver came from, wrapping a parent back into its child.
    /// `recv` is the receiver as the method sees it (already the adopted
    /// parent when the method is inherited).
    pub(crate) fn rebind_receiver(&mut self, recv: &Expr, new_obj: Expr, _tid: TypeId, _m: DefId) -> Vec<Stmt> {
        self.rebind_path(recv, new_obj)
    }
}

/// Apply `f` to the value of every `return` in a block (not inside nested
/// defs, which are separate).
pub(crate) fn rewrite_returns(b: &mut Block, f: &mut dyn FnMut(Expr) -> Expr) {
    for s in &mut b.stmts {
        match &mut s.kind {
            StmtKind::Return(e) => {
                let v = std::mem::replace(e, Expr { kind: ExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: 0 });
                *e = f(v);
            }
            StmtKind::If { then, else_, .. } => {
                rewrite_returns(then, f);
                rewrite_returns(else_, f);
            }
            StmtKind::Match { arms, .. } => {
                for a in arms {
                    if let ExprKind::Block(b) = &mut a.body.kind {
                        rewrite_returns(b, f);
                    }
                }
            }
            StmtKind::For { body, .. } | StmtKind::While { body, .. } => rewrite_returns(body, f),
            _ => {}
        }
    }
}
