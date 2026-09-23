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
                "entries" => (vec![], Type::list(Type::entry(v)), pure),
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

/// What a builtin that is gone became, said beside the error that it
/// does not exist.
pub(crate) fn replaced_by(name: &str) -> &'static str {
    match name {
        "zip" => ": a loop over several lists goes through them in lockstep, `for x, y in xs, ys`",
        "enumerate" => ": count alongside the items with an open range, `for i, x in 0.., xs`",
        _ => "",
    }
}

/// The builtin types that have a method of this name taking `nargs`
/// arguments, as `method_sig` defines them.
pub(crate) fn builtin_receivers(store: &mut TypeStore, name: &str, nargs: usize) -> Vec<Type> {
    let candidates = [
        Type::Str,
        Type::Int,
        Type::Float,
        Type::Bool,
        Type::list(store.fresh()),
        Type::range(),
        Type::map(store.fresh()),
    ];
    candidates
        .into_iter()
        .filter(|t| method_sig(store, t, name, nargs).is_some_and(|(params, _, _)| params.len() == nargs))
        .collect()
}

/// The builtin type that a method of this name fixes a receiver of unknown
/// type to: the one type that has it. A method that takes a function (a
/// list's `map`, which a range also has) is lowered with its function as
/// code, which a generic receiver cannot pass on, so it fixes a list.
pub(crate) fn unique_receiver(store: &mut TypeStore, name: &str, nargs: usize) -> Option<Type> {
    let mut found = builtin_receivers(store, name, nargs);
    if found.len() == 1 {
        return found.pop();
    }
    let list = found.into_iter().find(|t| matches!(t, Type::List(_)))?;
    let (params, _, _) = method_sig(store, &list, name, nargs)?;
    params.iter().any(|p| matches!(store.shallow(p), Type::Fn(..))).then_some(list)
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
    /// A dictionary key: dictionaries are keyed by strings.
    fn unify_key(&mut self, idx: &Type, line: usize) {
        match self.shallow(idx) {
            Type::Str | Type::Var(_) => {
                self.unify(idx, &Type::Str, line);
            }
            _ => {
                let t = self.show_type(idx);
                self.error(line, format!("dictionary keys are strings, found {}; convert the key with str(k)", t));
            }
        }
    }

    /// Note an effect of what a constraint provides, on the def that
    /// performs it.
    fn note_effect(&mut self, id: ConstraintId, eff: Effect) {
        if !eff.is_pure() {
            let owner = self.store.constraints[id].user;
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
            if let Class::Method(name, args, _) = &c.class {
                let has_class_method = self.types.iter().any(|t| t.method(name).is_some());
                if !has_class_method
                    && let Some(t) = unique_receiver(&mut self.store, name, args.len())
                        && self.store.unify(&subject, &t).is_ok() {
                            return self.solve_one(id);
                        }
            }
            return false;
        }
        let line = c.line;
        match self.solution(id, &c, &subject) {
            Some(sol) => self.store.constraints[id].solution = Some(sol),
            None => {
                let s = self.show_type(&subject);
                match &c.class {
                    Class::Method(n, _, _) => self.error(line, format!("no method .{}() on a value of type {}{}", n, s, replaced_by(n))),
                    Class::Field(n, _) | Class::SetField(n, _) => self.error(line, format!("no field .{} on a value of type {}", n, s)),
                    Class::Index(..) if matches!(subject, Type::Data(PAIR, _)) => self.error(line, format!("indexing is not defined on {}: read its fields, `.key` and `.value`", s)),
                    _ => self.error(line, format!("{} is not defined on {}", describe_class(&c.class), s)),
                }
                self.store.constraints[id].solution = Some(Solution::Concrete(vec![]));
            }
        }
        true
    }

    /// How a constraint `c` (number `id`) is met on its known subject, or
    /// None when the subject's type does not support it.
    fn solution(&mut self, id: ConstraintId, c: &Constraint, subject: &Type) -> Option<Solution> {
        let line = c.line;
        let none = Some(Solution::Concrete(vec![]));
        match &c.class {
            Class::Eq | Class::Ord | Class::Show => {
                // the parts: a list's elements, a data type's arguments
                let parts: Vec<Type> = match subject {
                    Type::Fn(..) => return None,
                    Type::List(e) | Type::Map(e) => vec![(**e).clone()],
                    Type::Data(_, args) => args.clone(),
                    _ => vec![],
                };
                let subs: Vec<ConstraintId> = parts.into_iter().map(|p| self.store.constrain(c.class.clone(), p, c.owner, c.user, line)).collect();
                for s in &subs {
                    self.solve_one(*s);
                }
                Some(Solution::Concrete(subs))
            }
            Class::Arith(op) => match subject {
                Type::Int | Type::Float => none,
                Type::Str | Type::List(_) if *op == ArithOp::Add => none,
                Type::Data(tid, _) => {
                    let m = self.types[*tid].method(op.symbol())?;
                    self.ensure_def(m);
                    let (mt, targs, dicts) = self.instantiate_def_type_for(m, c.owner, c.user, line);
                    // self, other -> result (unary minus: self -> result)
                    let params = if *op == ArithOp::Neg { vec![subject.clone()] } else { vec![subject.clone(), subject.clone()] };
                    let want = self.store.fresh_fn(params, subject.clone());
                    self.store.unify(&mt, &want).ok()?;
                    self.note_call(m, line);
                    Some(Solution::Method(m, targs, dicts))
                }
                _ => None,
            },
            Class::OrElse(rhs, ret) => {
                let t = match subject {
                    Type::Bool => Type::Bool,
                    Type::Data(MAYBE, args) => args[0].clone(),
                    _ => return None,
                };
                self.unify(rhs, &t, line);
                self.unify(ret, &t, line);
                none
            }
            Class::Zero => matches!(subject, Type::Int | Type::Float | Type::Str | Type::List(_)).then_some(Solution::Concrete(vec![])),
            Class::Len => matches!(subject, Type::List(_) | Type::Str | Type::Map(_) | Type::Data(RANGE, _)).then_some(Solution::Concrete(vec![])),
            Class::Iter(elem) => {
                let item = match subject {
                    Type::List(e) => (**e).clone(),
                    Type::Data(RANGE, _) => Type::Int,
                    Type::Str => Type::Str,
                    Type::Map(v) => Type::entry((**v).clone()),
                    _ => return None,
                };
                self.unify(elem, &item, line);
                none
            }
            Class::Index(idx, elem) => {
                let item = match subject {
                    Type::List(e) => (**e).clone(),
                    Type::Str => Type::Str,
                    Type::Data(RANGE, _) => Type::Int,
                    Type::Map(v) => {
                        self.unify_key(idx, line);
                        self.unify(elem, &Type::maybe((**v).clone()), line);
                        return none;
                    }
                    _ => return None,
                };
                self.unify(idx, &Type::Int, line);
                self.unify(elem, &item, line);
                self.note_effect(id, Effect::ABORT);
                none
            }
            Class::IndexSet(idx, val) => match subject {
                Type::List(e) => {
                    self.unify(idx, &Type::Int, line);
                    self.unify(val, e, line);
                    self.note_effect(id, Effect::ABORT);
                    none
                }
                Type::Map(v) => {
                    self.unify_key(idx, line);
                    self.unify(val, v, line);
                    none
                }
                _ => None,
            },
            Class::Field(name, ty) | Class::SetField(name, ty) => {
                let Type::Data(tid, args) = subject else { return None };
                let (path, fty_template) = self.field_through_parents(*tid, name)?;
                let fty = self.field_type_at(*tid, name, args).unwrap_or(fty_template);
                self.unify(ty, &fty, line);
                Some(Solution::Field(self.field_path(*tid, &path)))
            }
            Class::Method(name, args, ret) => match subject {
                Type::Data(tid, _) if !matches!(self.types[*tid].kind, DataKind::Builtin) => {
                    let m = self.method_through_parents(*tid, name)?;
                    self.ensure_def(m);
                    if let DefKind::Method { mutates: true, .. } = self.defs[m].kind {
                        self.error(line, format!("the method .{}() modifies its receiver, so the receiver must be a variable of known type; annotate the parameter", name));
                        return Some(Solution::Method(m, vec![], vec![]));
                    }
                    let (mt, targs, dicts) = self.instantiate_def_type_for(m, c.owner, c.user, line);
                    // the method's first parameter is self
                    let full = std::iter::once(subject.clone()).chain(args.iter().cloned()).collect();
                    let want = self.store.fresh_fn(full, ret.clone());
                    match self.store.unify(&mt, &want) {
                        Ok(()) => self.note_call(m, line),
                        Err(e) => {
                            let l = self.show_type(&e.left);
                            let r = self.show_type(&e.right);
                            self.error(line, format!("type mismatch in .{}(): expected {}, found {}", name, l, r));
                        }
                    }
                    Some(Solution::Method(m, targs, dicts))
                }
                _ => {
                    let (ps, r, eff) = method_sig(&mut self.store, subject, name, args.len())?;
                    if ps.len() != args.len() {
                        self.error(line, format!(".{}() takes {} argument(s), found {}", name, ps.len(), args.len()));
                    } else {
                        for (a, p) in args.iter().zip(ps.iter()) {
                            self.unify(a, p, line);
                        }
                    }
                    self.unify(ret, &r, line);
                    self.note_effect(id, eff);
                    // what the method needs of the elements
                    let elem = match subject {
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
                            subs.push(self.store.constrain(cl, e.clone(), c.owner, c.user, line));
                        }
                        if matches!(name.as_str(), "sort" | "sorted") && !args.is_empty() {
                            // the key's type
                            if let Type::Fn(_, k, _) = self.shallow(&args[0]) {
                                subs.push(self.store.constrain(Class::Ord, (*k).clone(), c.owner, c.user, line));
                            }
                        }
                    }
                    for sc in &subs {
                        self.solve_one(*sc);
                    }
                    Some(Solution::Concrete(subs))
                }
            },
            Class::Convert(name, ty) => {
                let t = match (*name, subject) {
                    ("str", _) => Type::Str,
                    ("int", Type::Int | Type::Float | Type::Bool) => Type::Int,
                    ("float", Type::Int | Type::Float) => Type::Float,
                    ("int", Type::Str) => {
                        self.note_effect(id, Effect::ABORT);
                        Type::Int
                    }
                    ("float", Type::Str) => {
                        self.note_effect(id, Effect::ABORT);
                        Type::Float
                    }
                    _ => return None,
                };
                self.unify(ty, &t, line);
                none
            }
        }
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

    /// A path of field indices from `tid` as (type, field) steps.
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

    /// A field's index path and declared type, through adopted parents.
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
