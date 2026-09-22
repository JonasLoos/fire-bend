// src/check/solve.rs
// Constraint solving: once a constraint's subject type is known, check that
// the type supports the class, unify the class's component types with what
// the type provides, and record how the lowering implements it. Also the
// table of builtin methods, which is what `Method` constraints on builtin
// types are solved against.

use super::*;

/// The signature of a builtin method call `recv.name(args)` for a receiver
/// of a known type: the parameter types (excluding the receiver), the
/// result type and the effect, or None if the type has no such method.
pub(crate) fn method_sig(store: &mut TypeStore, recv: &Type, name: &str, nargs: usize) -> Option<(Vec<Type>, Type, Effect)> {
    let pure = Effect::PURE;
    let fresh = |s: &mut TypeStore| s.fresh();
    let r = match recv {
        Type::Str => match name {
            "length" => (vec![], Type::Int, pure),
            "upper" | "lower" | "trim" | "trim_start" | "trim_end" => (vec![], Type::Str, pure),
            "split" => (if nargs == 0 { vec![] } else { vec![Type::Str] }, Type::list(Type::Str), pure),
            "lines" => (vec![], Type::list(Type::Str), pure),
            "replace" => (vec![Type::Str, Type::Str], Type::Str, pure),
            "contains" | "starts_with" | "ends_with" => (vec![Type::Str], Type::Bool, pure),
            "index_of" => (vec![Type::Str], Type::maybe(Type::Int), pure),
            "chars" => (vec![], Type::list(Type::Str), pure),
            "repeat" => (vec![Type::Int], Type::Str, pure),
            "to_int" => (vec![], Type::Int, Effect::ABORT),
            "to_float" => (vec![], Type::Float, Effect::ABORT),
            "parse_int" => (vec![], Type::result(Type::Str, Type::Int), pure),
            "parse_float" => (vec![], Type::result(Type::Str, Type::Float), pure),
            "is_empty" => (vec![], Type::Bool, pure),
            "reverse" | "reversed" => (vec![], Type::Str, pure),
            "join" => (vec![Type::list(Type::Str)], Type::Str, pure),
            "to_str" => (vec![], Type::Str, pure),
            "char_code" => (vec![], Type::Int, pure),
            "take" | "drop" => (vec![Type::Int], Type::Str, pure),
            "slice" => (vec![Type::range()], Type::Str, pure),
            _ => return None,
        },
        Type::Int => match name {
            "abs" => (vec![], Type::Int, pure),
            "to_str" => (vec![], Type::Str, pure),
            "to_float" => (vec![], Type::Float, pure),
            "to_int" => (vec![], Type::Int, pure),
            "sqrt" => (vec![], Type::Float, pure),
            "floor" | "ceil" | "round" => (vec![], Type::Int, pure),
            _ => return None,
        },
        Type::Float => match name {
            "abs" | "floor" | "ceil" | "sqrt" => (vec![], Type::Float, pure),
            "round" => (if nargs == 0 { vec![] } else { vec![Type::Int] }, Type::Float, pure),
            "to_str" => (vec![], Type::Str, pure),
            "to_int" => (vec![], Type::Int, pure),
            "to_float" => (vec![], Type::Float, pure),
            _ => return None,
        },
        Type::Bool => match name {
            "to_str" => (vec![], Type::Str, pure),
            _ => return None,
        },
        Type::List(elem) => {
            let e = (**elem).clone();
            match name {
                "length" => (vec![], Type::Int, pure),
                "map" => {
                    let b = fresh(store);
                    let f = store.fresh_fn(vec![e], b.clone());
                    (vec![f], Type::list(b), pure)
                }
                "filter" => {
                    let f = store.fresh_fn(vec![e.clone()], Type::Bool);
                    (vec![f], Type::list(e), pure)
                }
                "each" => {
                    let r = fresh(store);
                    let f = store.fresh_fn(vec![e], r);
                    (vec![f], Type::Unit, pure)
                }
                "reduce" => {
                    if nargs == 1 {
                        let f = store.fresh_fn(vec![e.clone(), e.clone()], e.clone());
                        (vec![f], e, Effect::ABORT)
                    } else {
                        let acc = fresh(store);
                        let f = store.fresh_fn(vec![acc.clone(), e], acc.clone());
                        (vec![f, acc.clone()], acc, pure)
                    }
                }
                "any" | "all" => {
                    let f = store.fresh_fn(vec![e], Type::Bool);
                    (vec![f], Type::Bool, pure)
                }
                "find" => {
                    let f = store.fresh_fn(vec![e.clone()], Type::Bool);
                    (vec![f], Type::maybe(e), pure)
                }
                "count" => {
                    let f = store.fresh_fn(vec![e], Type::Bool);
                    (vec![f], Type::Int, pure)
                }
                "sum" => (vec![], e, pure),
                "min" | "max" => (vec![], e, Effect::ABORT),
                "join" => (vec![Type::Str], Type::Str, pure),
                "contains" => (vec![e], Type::Bool, pure),
                "index_of" => (vec![e], Type::maybe(Type::Int), pure),
                "first" | "last" => (vec![], Type::maybe(e), pure),
                "reverse" | "reversed" => (vec![], Type::list(e), pure),
                "sort" | "sorted" => {
                    if nargs == 0 {
                        (vec![], Type::list(e), pure)
                    } else {
                        let k = fresh(store);
                        let f = store.fresh_fn(vec![e.clone()], k);
                        (vec![f], Type::list(e), pure)
                    }
                }
                "push" => ((0..nargs).map(|_| e.clone()).collect(), Type::list(e), pure),
                "pop" => (vec![], Type::pair(Type::list(e.clone()), e), Effect::ABORT),
                "drop_last" => (vec![], Type::list(e), pure),
                "take" | "drop" => (vec![Type::Int], Type::list(e), pure),
                "slice" => (vec![Type::range()], Type::list(e), pure),
                "to_list" => (vec![], Type::list(e), pure),
                "is_empty" => (vec![], Type::Bool, pure),
                "flatten" => {
                    let inner = fresh(store);
                    store.unify(&e, &Type::list(inner.clone())).ok()?;
                    (vec![], Type::list(inner), pure)
                }
                "enumerate" => (vec![], Type::list(Type::pair(Type::Int, e)), pure),
                "zip" => {
                    let other = fresh(store);
                    (vec![Type::list(other.clone())], Type::list(Type::pair(e, other)), pure)
                }
                _ => return None,
            }
        }
        Type::Data(RANGE, _) => match name {
            "to_list" | "reversed" | "reverse" => (vec![], Type::list(Type::Int), pure),
            "map" => {
                let b = fresh(store);
                let f = store.fresh_fn(vec![Type::Int], b.clone());
                (vec![f], Type::list(b), pure)
            }
            "filter" => {
                let f = store.fresh_fn(vec![Type::Int], Type::Bool);
                (vec![f], Type::list(Type::Int), pure)
            }
            "each" => {
                let r = fresh(store);
                let f = store.fresh_fn(vec![Type::Int], r);
                (vec![f], Type::Unit, pure)
            }
            "sum" | "length" => (vec![], Type::Int, pure),
            "min" | "max" | "first" | "last" => (vec![], Type::Int, Effect::ABORT),
            "contains" => (vec![Type::Int], Type::Bool, pure),
            "take" | "drop" => (vec![Type::Int], Type::list(Type::Int), pure),
            "slice" => (vec![Type::range()], Type::range(), pure),
            "reduce" => {
                let acc = fresh(store);
                let f = store.fresh_fn(vec![acc.clone(), Type::Int], acc.clone());
                (vec![f, acc.clone()], acc, pure)
            }
            _ => return None,
        },
        Type::Map(v) => {
            let v = (**v).clone();
            match name {
                "keys" => (vec![], Type::list(Type::Str), pure),
                "values" => (vec![], Type::list(v), pure),
                "entries" => (vec![], Type::list(Type::pair(Type::Str, v)), pure),
                "has" => (vec![Type::Str], Type::Bool, pure),
                "length" | "size" => (vec![], Type::Int, pure),
                "get" => (vec![Type::Str], Type::maybe(v), pure),
                "set" => (vec![Type::Str, v.clone()], Type::map(v), pure),
                "remove" | "delete" => (vec![Type::Str], Type::map(v), pure),
                _ => return None,
            }
        }
        _ => return None,
    };
    Some(r)
}

/// Builtin methods that exist on exactly one builtin type, used to fix a
/// receiver whose type is not known yet.
pub(crate) fn unique_receiver(store: &mut TypeStore, name: &str) -> Option<Type> {
    let str_only = ["upper", "lower", "trim", "trim_start", "trim_end", "split", "lines", "replace", "starts_with", "ends_with", "chars", "repeat", "to_int", "parse_int", "parse_float", "char_code"];
    let list_only = ["map", "filter", "each", "reduce", "any", "all", "find", "push", "pop", "drop_last", "sort", "sorted", "flatten", "enumerate", "zip", "count"];
    let map_only = ["keys", "values", "entries", "has", "set", "remove", "delete"];
    if str_only.contains(&name) {
        Some(Type::Str)
    } else if list_only.contains(&name) {
        let e = store.fresh();
        Some(Type::list(e))
    } else if map_only.contains(&name) {
        let v = store.fresh();
        Some(Type::map(v))
    } else {
        None
    }
}

pub fn describe_class(c: &Class) -> String {
    match c {
        Class::Eq => "equality (==)".into(),
        Class::Ord => "ordering (<, sorted, min, max)".into(),
        Class::Show => "printing".into(),
        Class::Arith(op) => format!("the operator {}", op.symbol()),
        Class::OrElse(..) => "or".into(),
        Class::Len => "len".into(),
        Class::Zero => "a zero to sum from".into(),
        Class::Iter(_) => "iteration".into(),
        Class::Index(..) => "indexing".into(),
        Class::IndexSet(..) => "index assignment".into(),
        Class::Field(n, _) => format!("the field .{}", n),
        Class::SetField(n, _) => format!("assignment to .{}", n),
        Class::Method(n, _, _) => format!("the method .{}()", n),
        Class::Convert(n, _) => format!("{}()", n),
    }
}

impl Checker {
    /// The def that performs what a constraint provides: for an instance of
    /// a generic def's dictionary, that generic def.
    fn effect_owner(&self, id: ConstraintId) -> DefId {
        self.store.constraints[id].user
    }

    fn note_effect(&mut self, id: ConstraintId, eff: Effect) {
        if !eff.is_pure() {
            let owner = self.effect_owner(id);
            self.defs[owner].own_effect = self.defs[owner].own_effect.join(eff);
        }
    }

    /// Try to solve one constraint. Returns true when it was solved (or
    /// reported), false when its subject is still unknown.
    pub(crate) fn solve_one(&mut self, id: ConstraintId) -> bool {
        if self.store.constraints[id].solution.is_some() {
            return false;
        }
        let c = self.store.constraints[id].clone();
        let subject = self.shallow(&c.subject);
        if let Type::Var(_) = subject {
            // a method name that only one builtin type has fixes the receiver
            if let Class::Method(name, _, _) = &c.class {
                let has_class_method = self.types.iter().any(|t| t.method(name).is_some());
                if !has_class_method
                    && let Some(t) = unique_receiver(&mut self.store, name)
                        && self.store.unify(&subject, &t).is_ok() {
                            return self.solve_one(id);
                        }
            }
            return false;
        }
        let line = c.line;
        let ok = match &c.class {
            Class::Eq | Class::Ord | Class::Show => match &subject {
                Type::Fn(..) => Err("functions"),
                _ => {
                    // the parts: a list's elements, a data type's arguments
                    let parts: Vec<Type> = match &subject {
                        Type::List(e) | Type::Map(e) => vec![(**e).clone()],
                        Type::Data(_, args) => args.clone(),
                        _ => vec![],
                    };
                    let owner = c.owner;
                    let user = c.user;
                    let class = c.class.clone();
                    let subs: Vec<ConstraintId> = parts.iter().map(|p| self.store.constrain(class.clone(), p.clone(), owner, user, line)).collect();
                    for s in &subs {
                        self.solve_one(*s);
                    }
                    Ok(Solution::Concrete(subs))
                }
            },
            Class::Arith(op) => {
                let op = *op;
                match &subject {
                    Type::Int | Type::Float => Ok(Solution::Concrete(vec![])),
                    Type::Str | Type::List(_) if op == ArithOp::Add => Ok(Solution::Concrete(vec![])),
                    Type::Data(tid, _) => match self.class_operator(*tid, op.symbol()) {
                        Some(m) => {
                            self.ensure_def(m, line);
                            let (owner, user) = (self.store.constraints[id].owner, self.store.constraints[id].user);
                            let (mt, targs, dicts) = self.instantiate_def_type_for(m, owner, user, line);
                            // self, other -> result (unary minus: self -> result)
                            let params = if op == ArithOp::Neg { vec![subject.clone()] } else { vec![subject.clone(), subject.clone()] };
                            let want = self.store.fresh_fn(params, subject.clone());
                            match self.store.unify(&mt, &want) {
                                Ok(()) => {
                                    self.note_call(m, line);
                                    Ok(Solution::Method(m, targs, dicts))
                                }
                                Err(_) => Err("operator"),
                            }
                        }
                        None => Err("operator"),
                    },
                    _ => Err("operator"),
                }
            }
            Class::OrElse(rhs, ret) => match &subject {
                Type::Bool => {
                    self.unify(rhs, &Type::Bool, line);
                    self.unify(ret, &Type::Bool, line);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Data(MAYBE, args) => {
                    let inner = args[0].clone();
                    self.unify(rhs, &inner, line);
                    self.unify(ret, &inner, line);
                    Ok(Solution::Concrete(vec![]))
                }
                _ => Err("or"),
            },
            Class::Zero => match &subject {
                Type::Int | Type::Float | Type::Str | Type::List(_) => Ok(Solution::Concrete(vec![])),
                _ => Err("sum"),
            },
            Class::Len => match &subject {
                Type::List(_) | Type::Str | Type::Map(_) | Type::Data(RANGE, _) => Ok(Solution::Concrete(vec![])),
                _ => Err("len"),
            },
            Class::Iter(elem) => {
                let item = match &subject {
                    Type::List(e) => Some((**e).clone()),
                    Type::Data(RANGE, _) => Some(Type::Int),
                    Type::Str => Some(Type::Str),
                    Type::Map(v) => Some(Type::pair(Type::Str, (**v).clone())),
                    _ => None,
                };
                match item {
                    Some(t) => {
                        self.unify(elem, &t, line);
                        Ok(Solution::Concrete(vec![]))
                    }
                    None => Err("iteration"),
                }
            }
            Class::Index(idx, elem, lit) => match &subject {
                Type::List(e) => {
                    let e = (**e).clone();
                    self.unify(idx, &Type::Int, line);
                    self.unify(elem, &e, line);
                    self.note_effect(id, Effect::ABORT);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Str => {
                    self.unify(idx, &Type::Int, line);
                    self.unify(elem, &Type::Str, line);
                    self.note_effect(id, Effect::ABORT);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Data(RANGE, _) => {
                    self.unify(idx, &Type::Int, line);
                    self.unify(elem, &Type::Int, line);
                    self.note_effect(id, Effect::ABORT);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Map(v) => {
                    let v = (**v).clone();
                    self.unify(idx, &Type::Str, line);
                    self.unify(elem, &Type::maybe(v), line);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Data(PAIR, args) => {
                    // a pair indexes as [0] / [1]
                    self.unify(idx, &Type::Int, line);
                    let (a, b) = (args[0].clone(), args[1].clone());
                    match lit {
                        Some(0) => self.unify(elem, &a, line),
                        Some(1) => self.unify(elem, &b, line),
                        _ => {
                            self.error(line, "a pair is indexed by a literal 0 or 1");
                            true
                        }
                    };
                    Ok(Solution::Concrete(vec![]))
                }
                _ => Err("indexing"),
            },
            Class::IndexSet(idx, val) => match &subject {
                Type::List(e) => {
                    let e = (**e).clone();
                    self.unify(idx, &Type::Int, line);
                    self.unify(val, &e, line);
                    self.note_effect(id, Effect::ABORT);
                    Ok(Solution::Concrete(vec![]))
                }
                Type::Map(v) => {
                    let v = (**v).clone();
                    self.unify(idx, &Type::Str, line);
                    self.unify(val, &v, line);
                    Ok(Solution::Concrete(vec![]))
                }
                _ => Err("index assignment"),
            },
            Class::Field(name, ty) => match &subject {
                Type::Data(tid, args) => {
                    let tid = *tid;
                    match self.field_through_parents(tid, name) {
                        Some((path, fty_template)) => {
                            let args = args.clone();
                            let fty = self.field_type_at(tid, name, &args).unwrap_or(fty_template);
                            self.unify(ty, &fty, line);
                            Ok(Solution::Field(self.field_path(tid, &path)))
                        }
                        None => Err("field"),
                    }
                }
                _ => Err("field"),
            },
            Class::SetField(name, ty) => match &subject {
                Type::Data(tid, args) => {
                    let tid = *tid;
                    let args = args.clone();
                    match self.field_through_parents(tid, name) {
                        Some((path, fty_template)) => {
                            let fty = self.field_type_at(tid, name, &args).unwrap_or(fty_template);
                            self.unify(ty, &fty, line);
                            Ok(Solution::Field(self.field_path(tid, &path)))
                        }
                        None => Err("field"),
                    }
                }
                _ => Err("field"),
            },
            Class::Method(name, args, ret) => {
                let name = name.clone();
                let args = args.clone();
                let ret = ret.clone();
                match &subject {
                    Type::Data(tid, _) if !matches!(self.types[*tid].kind, DataKind::Builtin) => {
                        let tid = *tid;
                        match self.method_through_parents(tid, &name) {
                            Some(m) => {
                                self.ensure_def(m, line);
                                if let DefKind::Method { mutates: true, .. } = self.defs[m].kind {
                                    self.error(line, format!("the method .{}() modifies its receiver, so the receiver must be a variable of known type; annotate the parameter", name));
                                    Ok(Solution::Method(m, vec![], vec![]))
                                } else {
                                    let (owner, user) = (self.store.constraints[id].owner, self.store.constraints[id].user);
                                    let (mt, targs, dicts) = self.instantiate_def_type_for(m, owner, user, line);
                                    let want = self.store.fresh_fn(args.clone(), ret.clone());
                                    // the method's first parameter is self
                                    let mut full = vec![subject.clone()];
                                    if let Type::Fn(ps, _, _) = &want { full.extend(ps.iter().cloned()) }
                                    let want_full = self.store.fresh_fn(full, ret.clone());
                                    match self.store.unify(&mt, &want_full) {
                                        Ok(()) => {
                                            self.note_call(m, line);
                                            Ok(Solution::Method(m, targs, dicts))
                                        }
                                        Err(e) => {
                                            let l = self.show_type(&e.left);
                                            let r = self.show_type(&e.right);
                                            self.error(line, format!("type mismatch in .{}(): expected {}, found {}", name, l, r));
                                            Ok(Solution::Method(m, targs, dicts))
                                        }
                                    }
                                }
                            }
                            None => Err("method"),
                        }
                    }
                    _ => match method_sig(&mut self.store, &subject, &name, args.len()) {
                        Some((ps, r, eff)) => {
                            if ps.len() != args.len() {
                                self.error(line, format!(".{}() takes {} argument(s), found {}", name, ps.len(), args.len()));
                            } else {
                                for (a, p) in args.iter().zip(ps.iter()) {
                                    self.unify(a, p, line);
                                }
                            }
                            self.unify(&ret, &r, line);
                            self.note_effect(id, eff);
                            // what the method needs of the elements
                            let owner = c.owner;
                            let user = c.user;
                            let elem = match &subject {
                                Type::List(e) => Some((**e).clone()),
                                Type::Data(RANGE, _) => Some(Type::Int),
                                _ => None,
                            };
                            let mut subs = Vec::new();
                            if let Some(e) = elem {
                                let needs: Vec<Class> = match name.as_str() {
                                    "sum" => vec![Class::Arith(ArithOp::Add), Class::Zero],
                                    "min" | "max" => vec![Class::Ord],
                                    "contains" | "index_of" => vec![Class::Eq],
                                    "sort" | "sorted" if args.is_empty() => vec![Class::Ord],
                                    _ => vec![],
                                };
                                for cl in needs {
                                    subs.push(self.store.constrain(cl, e.clone(), owner, user, line));
                                }
                                if matches!(name.as_str(), "sort" | "sorted") && !args.is_empty() {
                                    // the key's type
                                    if let Type::Fn(_, k, _) = self.shallow(&args[0]) {
                                        subs.push(self.store.constrain(Class::Ord, (*k).clone(), owner, user, line));
                                    }
                                }
                            }
                            for sc in &subs {
                                self.solve_one(*sc);
                            }
                            Ok(Solution::Concrete(subs))
                        }
                        None => Err("method"),
                    },
                }
            }
            Class::Convert(name, ty) => {
                let ty = ty.clone();
                let ok = match (*name, &subject) {
                    ("str", _) => Some(Type::Str),
                    ("int", Type::Int) | ("int", Type::Float) => Some(Type::Int),
                    ("int", Type::Str) => {
                        self.note_effect(id, Effect::ABORT);
                        Some(Type::Int)
                    }
                    ("int", Type::Bool) => Some(Type::Int),
                    ("float", Type::Int) | ("float", Type::Float) => Some(Type::Float),
                    ("float", Type::Str) => {
                        self.note_effect(id, Effect::ABORT);
                        Some(Type::Float)
                    }
                    _ => None,
                };
                match ok {
                    Some(t) => {
                        self.unify(&ty, &t, line);
                        Ok(Solution::Concrete(vec![]))
                    }
                    None => Err("conversion"),
                }
            }
        };
        match ok {
            Ok(sol) => {
                self.store.constraints[id].solution = Some(sol);
            }
            Err(_) => {
                let what = describe_class(&c.class);
                let s = self.show_type(&subject);
                match &c.class {
                    Class::Method(n, _, _) => self.error(line, format!("no method .{}() on a value of type {}", n, s)),
                    Class::Field(n, _) | Class::SetField(n, _) => self.error(line, format!("no field .{} on a value of type {}", n, s)),
                    _ => self.error(line, format!("{} is not defined on {}", what, s)),
                }
                self.store.constraints[id].solution = Some(Solution::Concrete(vec![]));
            }
        }
        true
    }

    /// The method of a class named after an operator symbol.
    pub(crate) fn class_operator(&self, tid: TypeId, sym: &str) -> Option<DefId> {
        self.types[tid].method(sym)
    }

    /// A field's type in a data type instantiated at `args`, looking
    /// through adopted parents.
    pub(crate) fn field_type_at(&mut self, tid: TypeId, name: &str, args: &[Type]) -> Option<Type> {
        let dt = self.types[tid].clone();
        if let Some(idx) = dt.field_index(name) {
            let tys = self.ctor_field_types(tid, 0, args);
            return Some(tys[idx].clone());
        }
        if let Some(pidx) = dt.parent_field() {
            let tys = self.ctor_field_types(tid, 0, args);
            if let Type::Data(ptid, pargs) = self.shallow(&tys[pidx]) {
                return self.field_type_at(ptid, name, &pargs);
            }
        }
        None
    }

    /// The path of field indices to a field, through adopted parents.
    /// A field path as (type, field) steps from `tid`.
    pub(crate) fn field_path(&self, tid: TypeId, path: &[usize]) -> Vec<(TypeId, usize)> {
        let mut out = Vec::new();
        let mut t = tid;
        for &idx in path {
            out.push((t, idx));
            if let Type::Data(n, _) = self.shallow(&self.types[t].ctors[0].fields[idx].ty) {
                t = n;
            }
        }
        out
    }

    pub(crate) fn field_through_parents(&self, tid: TypeId, name: &str) -> Option<(Vec<usize>, Type)> {
        let dt = &self.types[tid];
        if let Some(idx) = dt.field_index(name) {
            return Some((vec![idx], dt.ctors[0].fields[idx].ty.clone()));
        }
        if let Some(pidx) = dt.parent_field()
            && let Type::Data(ptid, _) = self.shallow(&dt.ctors[0].fields[pidx].ty)
                && let Some((mut path, t)) = self.field_through_parents(ptid, name) {
                    path.insert(0, pidx);
                    return Some((path, t));
                }
        None
    }

    /// A method by name, through adopted parents.
    pub(crate) fn method_through_parents(&self, tid: TypeId, name: &str) -> Option<DefId> {
        let dt = &self.types[tid];
        if let Some(m) = dt.method(name) {
            return Some(m);
        }
        if let Some(pidx) = dt.parent_field()
            && let Type::Data(ptid, _) = self.shallow(&dt.ctors[0].fields[pidx].ty) {
                return self.method_through_parents(ptid, name);
            }
        None
    }

    /// Instantiate a def's type for a call: its scheme when done, its
    /// monomorphic type while in progress. Returns the type, the type
    /// arguments (one per scheme variable) and the dictionary constraints.
    pub(crate) fn instantiate_def_type(&mut self, d: DefId, line: usize) -> (Type, Vec<Type>, Vec<ConstraintId>) {
        let unit = self.unit();
        let user = self.current_def();
        self.instantiate_def_type_for(d, unit, user, line)
    }

    /// The same, raising the dictionaries in a given unit for a given user
    /// (a constraint solved to a method instantiates it where the
    /// constraint was raised).
    pub(crate) fn instantiate_def_type_for(&mut self, d: DefId, unit: DefId, user: DefId, line: usize) -> (Type, Vec<Type>, Vec<ConstraintId>) {
        match self.defs[d].scheme.clone() {
            Some(s) if self.defs[d].state == State::Done => {
                let (t, subst, dicts) = self.store.instantiate(&s, unit, user, line);
                for (new, old) in dicts.iter().zip(s.dicts.iter()) {
                    self.instance_of.insert(*new, *old);
                }
                for id in &dicts {
                    self.solve_one(*id);
                }
                let targs = subst.iter().map(|(_, t)| t.clone()).collect();
                (t, targs, dicts)
            }
            _ => (self.defs[d].mono.clone(), vec![], vec![]),
        }
    }
}
