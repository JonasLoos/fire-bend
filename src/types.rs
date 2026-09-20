// src/bend/types.rs
// The static type language of the compiler and its unifier.
//
// Types are Hindley-Milner with a few Fire-specific constructors. Type
// variables live in a store with union-find style binding and levels for
// let-generalization. Function types additionally carry a "closure set"
// variable that accumulates every lambda or def that can flow into a value
// of that type; the lowering uses it to pick a representation for function
// values (see docs/compiler.md).

use std::collections::BTreeSet;
use std::fmt;

pub type TVar = u32;
pub type RecId = usize;
/// A lambda site or a def used as a value.
pub type ClosId = usize;
pub type ClosVar = u32;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Var(TVar),
    Int,
    Float,
    Str,
    Bool,
    /// The type of `nothing` on its own.
    Unit,
    List(Box<Type>),
    /// A string-keyed dictionary (`{}` used with `[]`).
    Map(Box<Type>),
    /// `T | nothing`
    Maybe(Box<Type>),
    /// `{err: E}` / `{ok: A}`
    Result(Box<Type>, Box<Type>),
    /// Parameters, return type, closure set.
    Fn(Vec<Type>, Box<Type>, ClosVar),
    /// A nominal record (constructor-built object or literal shape) applied
    /// to its type arguments.
    Record(RecId, Vec<Type>),
    /// A closed integer range `a..b`.
    Range,
    /// An open range or a lazy pipeline over one, yielding elements of the
    /// given type.
    Stream(Box<Type>),
}

impl Type {
    pub fn list(t: Type) -> Type {
        Type::List(Box::new(t))
    }
    pub fn maybe(t: Type) -> Type {
        Type::Maybe(Box::new(t))
    }
    pub fn map(t: Type) -> Type {
        Type::Map(Box::new(t))
    }
    pub fn result(e: Type, a: Type) -> Type {
        Type::Result(Box::new(e), Box::new(a))
    }
    pub fn stream(t: Type) -> Type {
        Type::Stream(Box::new(t))
    }
}

/// A type scheme: quantified variables and a body.
#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<TVar>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
enum Binding {
    Unbound { level: u32 },
    Bound(Type),
}

#[derive(Debug, Clone)]
enum ClosNode {
    Root(BTreeSet<ClosId>),
    Link(ClosVar),
}

/// Storage for type variables and closure-set variables.
#[derive(Debug, Default, Clone)]
pub struct TypeStore {
    vars: Vec<Binding>,
    clos: Vec<ClosNode>,
    pub level: u32,
}

#[derive(Debug, Clone)]
pub struct UnifyError {
    pub left: Type,
    pub right: Type,
}

impl TypeStore {
    pub fn new() -> Self {
        TypeStore { vars: Vec::new(), clos: Vec::new(), level: 1 }
    }

    pub fn fresh(&mut self) -> Type {
        self.vars.push(Binding::Unbound { level: self.level });
        Type::Var((self.vars.len() - 1) as TVar)
    }

    pub fn fresh_var(&mut self) -> TVar {
        match self.fresh() {
            Type::Var(v) => v,
            _ => unreachable!(),
        }
    }

    pub fn fresh_clos(&mut self) -> ClosVar {
        self.clos.push(ClosNode::Root(BTreeSet::new()));
        (self.clos.len() - 1) as ClosVar
    }

    pub fn clos_singleton(&mut self, id: ClosId) -> ClosVar {
        let mut set = BTreeSet::new();
        set.insert(id);
        self.clos.push(ClosNode::Root(set));
        (self.clos.len() - 1) as ClosVar
    }

    pub fn fresh_fn(&mut self, params: Vec<Type>, ret: Type) -> Type {
        let c = self.fresh_clos();
        Type::Fn(params, Box::new(ret), c)
    }

    pub fn enter_level(&mut self) {
        self.level += 1;
    }
    pub fn leave_level(&mut self) {
        self.level -= 1;
    }

    fn clos_root(&mut self, mut c: ClosVar) -> ClosVar {
        loop {
            match &self.clos[c as usize] {
                ClosNode::Link(n) => c = *n,
                ClosNode::Root(_) => return c,
            }
        }
    }

    pub fn clos_set(&mut self, c: ClosVar) -> BTreeSet<ClosId> {
        let r = self.clos_root(c);
        match &self.clos[r as usize] {
            ClosNode::Root(s) => s.clone(),
            _ => unreachable!(),
        }
    }

    pub fn clos_add(&mut self, c: ClosVar, id: ClosId) {
        let r = self.clos_root(c);
        if let ClosNode::Root(s) = &mut self.clos[r as usize] {
            s.insert(id);
        }
    }

    fn clos_union(&mut self, a: ClosVar, b: ClosVar) {
        let ra = self.clos_root(a);
        let rb = self.clos_root(b);
        if ra == rb {
            return;
        }
        let sb = match &self.clos[rb as usize] {
            ClosNode::Root(s) => s.clone(),
            _ => unreachable!(),
        };
        if let ClosNode::Root(sa) = &mut self.clos[ra as usize] {
            sa.extend(sb);
        }
        self.clos[rb as usize] = ClosNode::Link(ra);
    }

    /// Follow variable bindings one level.
    pub fn shallow(&self, t: &Type) -> Type {
        let mut t = t.clone();
        loop {
            match t {
                Type::Var(v) => match &self.vars[v as usize] {
                    Binding::Bound(b) => t = b.clone(),
                    Binding::Unbound { .. } => return Type::Var(v),
                },
                other => return other,
            }
        }
    }

    /// Fully resolve a type (replace bound variables everywhere).
    pub fn resolve(&self, t: &Type) -> Type {
        match self.shallow(t) {
            Type::Var(v) => Type::Var(v),
            Type::List(e) => Type::List(Box::new(self.resolve(&e))),
            Type::Map(e) => Type::Map(Box::new(self.resolve(&e))),
            Type::Maybe(e) => Type::Maybe(Box::new(self.resolve(&e))),
            Type::Stream(e) => Type::Stream(Box::new(self.resolve(&e))),
            Type::Result(e, a) => Type::Result(Box::new(self.resolve(&e)), Box::new(self.resolve(&a))),
            Type::Fn(ps, r, c) => Type::Fn(ps.iter().map(|p| self.resolve(p)).collect(), Box::new(self.resolve(&r)), c),
            Type::Record(id, args) => Type::Record(id, args.iter().map(|a| self.resolve(a)).collect()),
            other => other,
        }
    }

    fn occurs(&self, v: TVar, t: &Type) -> bool {
        match self.shallow(t) {
            Type::Var(w) => w == v,
            Type::List(e) | Type::Map(e) | Type::Maybe(e) | Type::Stream(e) => self.occurs(v, &e),
            Type::Result(e, a) => self.occurs(v, &e) || self.occurs(v, &a),
            Type::Fn(ps, r, _) => ps.iter().any(|p| self.occurs(v, p)) || self.occurs(v, &r),
            Type::Record(_, args) => args.iter().any(|a| self.occurs(v, a)),
            _ => false,
        }
    }

    fn var_level(&self, v: TVar) -> u32 {
        match &self.vars[v as usize] {
            Binding::Unbound { level } => *level,
            Binding::Bound(_) => 0,
        }
    }

    /// Lower the level of every unbound variable in `t` to at most `level`.
    fn adjust_levels(&mut self, t: &Type, level: u32) {
        match self.shallow(t) {
            Type::Var(w) => {
                if let Binding::Unbound { level: l } = &mut self.vars[w as usize] {
                    if *l > level {
                        *l = level;
                    }
                }
            }
            Type::List(e) | Type::Map(e) | Type::Maybe(e) | Type::Stream(e) => self.adjust_levels(&e, level),
            Type::Result(e, a) => {
                self.adjust_levels(&e, level);
                self.adjust_levels(&a, level);
            }
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.adjust_levels(p, level);
                }
                self.adjust_levels(&r, level);
            }
            Type::Record(_, args) => {
                for a in &args {
                    self.adjust_levels(a, level);
                }
            }
            _ => {}
        }
    }

    /// Keep every variable in `t` monomorphic: lower its level to the
    /// current one so `generalize` will not quantify it.
    pub fn pin(&mut self, t: &Type) {
        let level = self.level;
        self.adjust_levels(t, level);
    }

    fn bind(&mut self, v: TVar, t: Type) -> Result<(), UnifyError> {
        if let Type::Var(w) = self.shallow(&t) {
            if w == v {
                return Ok(());
            }
        }
        if self.occurs(v, &t) {
            return Err(UnifyError { left: Type::Var(v), right: t });
        }
        let level = self.var_level(v);
        self.adjust_levels(&t, level);
        self.vars[v as usize] = Binding::Bound(t);
        Ok(())
    }

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), UnifyError> {
        let a = self.shallow(a);
        let b = self.shallow(b);
        match (&a, &b) {
            (Type::Var(v), _) => self.bind(*v, b.clone()),
            (_, Type::Var(w)) => self.bind(*w, a.clone()),
            (Type::Int, Type::Int)
            | (Type::Float, Type::Float)
            | (Type::Str, Type::Str)
            | (Type::Bool, Type::Bool)
            | (Type::Unit, Type::Unit)
            | (Type::Range, Type::Range) => Ok(()),
            (Type::List(x), Type::List(y))
            | (Type::Map(x), Type::Map(y))
            | (Type::Maybe(x), Type::Maybe(y))
            | (Type::Stream(x), Type::Stream(y)) => self.unify(x, y),
            (Type::Result(e1, a1), Type::Result(e2, a2)) => {
                self.unify(e1, e2)?;
                self.unify(a1, a2)
            }
            (Type::Fn(p1, r1, c1), Type::Fn(p2, r2, c2)) => {
                if p1.len() != p2.len() {
                    return Err(UnifyError { left: a.clone(), right: b.clone() });
                }
                for (x, y) in p1.iter().zip(p2.iter()) {
                    self.unify(x, y)?;
                }
                self.unify(r1, r2)?;
                self.clos_union(*c1, *c2);
                Ok(())
            }
            (Type::Record(i, x), Type::Record(j, y)) if i == j && x.len() == y.len() => {
                for (p, q) in x.iter().zip(y.iter()) {
                    self.unify(p, q)?;
                }
                Ok(())
            }
            _ => Err(UnifyError { left: a.clone(), right: b.clone() }),
        }
    }

    /// Generalize a type over the variables above the current level.
    pub fn generalize(&self, t: &Type) -> Scheme {
        let mut vars = Vec::new();
        self.collect_generic(t, &mut vars);
        Scheme { vars, ty: self.resolve(t) }
    }

    fn collect_generic(&self, t: &Type, out: &mut Vec<TVar>) {
        match self.shallow(t) {
            Type::Var(v) => {
                if self.var_level(v) > self.level && !out.contains(&v) {
                    out.push(v);
                }
            }
            Type::List(e) | Type::Map(e) | Type::Maybe(e) | Type::Stream(e) => self.collect_generic(&e, out),
            Type::Result(e, a) => {
                self.collect_generic(&e, out);
                self.collect_generic(&a, out);
            }
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.collect_generic(p, out);
                }
                self.collect_generic(&r, out);
            }
            Type::Record(_, args) => {
                for a in &args {
                    self.collect_generic(a, out);
                }
            }
            _ => {}
        }
    }

    /// Instantiate a scheme with fresh variables. Returns the type and the
    /// substitution (quantified var -> fresh var), which the lowering uses
    /// to monomorphize.
    pub fn instantiate(&mut self, s: &Scheme) -> (Type, Vec<(TVar, Type)>) {
        let subst: Vec<(TVar, Type)> = s.vars.iter().map(|v| (*v, self.fresh())).collect();
        let t = self.substitute(&s.ty, &subst);
        (t, subst)
    }

    /// Replace quantified variables. Function closure variables are kept:
    /// every instance of a polymorphic function shares the closure set of
    /// its definition, which is what monomorphization wants.
    pub fn substitute(&mut self, t: &Type, subst: &[(TVar, Type)]) -> Type {
        match self.shallow(t) {
            Type::Var(v) => {
                for (w, r) in subst {
                    if *w == v {
                        return r.clone();
                    }
                }
                Type::Var(v)
            }
            Type::List(e) => Type::List(Box::new(self.substitute(&e, subst))),
            Type::Map(e) => Type::Map(Box::new(self.substitute(&e, subst))),
            Type::Maybe(e) => Type::Maybe(Box::new(self.substitute(&e, subst))),
            Type::Stream(e) => Type::Stream(Box::new(self.substitute(&e, subst))),
            Type::Result(e, a) => {
                let e = self.substitute(&e, subst);
                let a = self.substitute(&a, subst);
                Type::Result(Box::new(e), Box::new(a))
            }
            Type::Fn(ps, r, c) => {
                let ps = ps.iter().map(|p| self.substitute(p, subst)).collect();
                let r = self.substitute(&r, subst);
                Type::Fn(ps, Box::new(r), c)
            }
            Type::Record(id, args) => Type::Record(id, args.iter().map(|a| self.substitute(a, subst)).collect()),
            other => other,
        }
    }

    /// Free (unbound) variables of a resolved type.
    pub fn free_vars(&self, t: &Type, out: &mut Vec<TVar>) {
        match self.shallow(t) {
            Type::Var(v) => {
                if !out.contains(&v) {
                    out.push(v);
                }
            }
            Type::List(e) | Type::Map(e) | Type::Maybe(e) | Type::Stream(e) => self.free_vars(&e, out),
            Type::Result(e, a) => {
                self.free_vars(&e, out);
                self.free_vars(&a, out);
            }
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.free_vars(p, out);
                }
                self.free_vars(&r, out);
            }
            Type::Record(_, args) => {
                for a in &args {
                    self.free_vars(a, out);
                }
            }
            _ => {}
        }
    }
}

/// Human-readable type names for diagnostics. Record names are supplied by
/// the caller through `names`.
pub struct TypeDisplay<'a> {
    pub store: &'a TypeStore,
    pub ty: &'a Type,
    pub names: &'a dyn Fn(RecId) -> String,
}

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(store: &TypeStore, t: &Type, names: &dyn Fn(RecId) -> String, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match store.shallow(t) {
                Type::Var(v) => write!(f, "?{}", v),
                Type::Int => write!(f, "int"),
                Type::Float => write!(f, "float"),
                Type::Str => write!(f, "str"),
                Type::Bool => write!(f, "bool"),
                Type::Unit => write!(f, "nothing"),
                Type::Range => write!(f, "range"),
                Type::List(e) => {
                    write!(f, "list of ")?;
                    go(store, &e, names, f)
                }
                Type::Stream(e) => {
                    write!(f, "stream of ")?;
                    go(store, &e, names, f)
                }
                Type::Map(e) => {
                    write!(f, "dict of ")?;
                    go(store, &e, names, f)
                }
                Type::Maybe(e) => {
                    go(store, &e, names, f)?;
                    write!(f, " | nothing")
                }
                Type::Result(e, a) => {
                    write!(f, "result(ok: ")?;
                    go(store, &a, names, f)?;
                    write!(f, ", err: ")?;
                    go(store, &e, names, f)?;
                    write!(f, ")")
                }
                Type::Fn(ps, r, _) => {
                    write!(f, "fn(")?;
                    for (i, p) in ps.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        go(store, p, names, f)?;
                    }
                    write!(f, ") -> ")?;
                    go(store, &r, names, f)
                }
                Type::Record(id, args) => {
                    write!(f, "{}", names(id))?;
                    if !args.is_empty() {
                        write!(f, "<")?;
                        for (i, a) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            go(store, a, names, f)?;
                        }
                        write!(f, ">")?;
                    }
                    Ok(())
                }
            }
        }
        go(self.store, self.ty, self.names, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unifies_and_generalizes() {
        let mut s = TypeStore::new();
        s.enter_level();
        let a = s.fresh();
        let f = s.fresh_fn(vec![a.clone()], a.clone());
        s.leave_level();
        let scheme = s.generalize(&f);
        assert_eq!(scheme.vars.len(), 1);
        let (inst, _) = s.instantiate(&scheme);
        if let Type::Fn(ps, _, _) = &inst {
            s.unify(&ps[0], &Type::Int).unwrap();
        }
        match s.resolve(&inst) {
            Type::Fn(ps, r, _) => {
                assert_eq!(ps[0], Type::Int);
                assert_eq!(*r, Type::Int);
            }
            _ => panic!(),
        }
        // the scheme itself is untouched
        let (inst2, _) = s.instantiate(&scheme);
        assert!(matches!(s.resolve(&inst2), Type::Fn(_, _, _)));
        assert!(s.unify(&Type::Int, &Type::Str).is_err());
    }

    #[test]
    fn closure_sets_union() {
        let mut s = TypeStore::new();
        let c1 = s.clos_singleton(1);
        let c2 = s.clos_singleton(2);
        let f1 = Type::Fn(vec![Type::Int], Box::new(Type::Int), c1);
        let f2 = Type::Fn(vec![Type::Int], Box::new(Type::Int), c2);
        s.unify(&f1, &f2).unwrap();
        assert_eq!(s.clos_set(c1).len(), 2);
        assert_eq!(s.clos_set(c2).len(), 2);
    }
}
