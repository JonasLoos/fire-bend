// src/types.rs
// The static type language of the compiler: Hindley-Milner types with
// constraints on type variables (qualified types) and closure sets.
//
// A constraint records one thing a def's body needs from a type it does not
// know yet: an ordering, a way to show it, a field, a method. While the
// checker runs, constraints wait on their subject type; once it is known
// they are solved against it, and a constraint whose subject stays generic
// when its def is generalized becomes a *dictionary parameter* of that def,
// which the lowering emits as a Bend template parameter (`~lt: A -> A -> Bool`).
// The Core IR refers to every such need by constraint id (`Dict`), so the
// lowering can resolve each one either to a concrete def or to a forwarded
// template parameter. See docs/compiler.md.

use std::collections::BTreeSet;
use std::fmt;

pub type TVar = u32;
/// Index of a data type in the program's type table (core::Program::types).
pub type TypeId = usize;
/// A lambda site or a def used as a value.
pub type ClosId = usize;
pub type ClosVar = u32;
pub type ConstraintId = usize;

/// Fixed positions of the builtin data types in every program's type table.
pub const MAYBE: TypeId = 0;
pub const RESULT: TypeId = 1;
pub const PAIR: TypeId = 2;
pub const RANGE: TypeId = 3;
pub const BUILTIN_TYPES: usize = 4;

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
    /// A string-keyed dictionary.
    Map(Box<Type>),
    /// Parameters, return type, closure set.
    Fn(Vec<Type>, Box<Type>, ClosVar),
    /// A data type (declared, class, record shape, or builtin such as
    /// `Maybe`) applied to its type arguments.
    Data(TypeId, Vec<Type>),
}

impl Type {
    pub fn list(t: Type) -> Type {
        Type::List(Box::new(t))
    }
    pub fn map(t: Type) -> Type {
        Type::Map(Box::new(t))
    }
    pub fn maybe(t: Type) -> Type {
        Type::Data(MAYBE, vec![t])
    }
    pub fn result(e: Type, a: Type) -> Type {
        Type::Data(RESULT, vec![e, a])
    }
    pub fn pair(a: Type, b: Type) -> Type {
        Type::Data(PAIR, vec![a, b])
    }
    pub fn range() -> Type {
        Type::Data(RANGE, vec![])
    }
    pub fn is_maybe(&self) -> bool {
        matches!(self, Type::Data(MAYBE, _))
    }
    pub fn is_result(&self) -> bool {
        matches!(self, Type::Data(RESULT, _))
    }
}

/// An arithmetic operator, each its own constraint (and template parameter).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Neg,
}

impl ArithOp {
    pub fn symbol(self) -> &'static str {
        match self {
            ArithOp::Add => "+",
            ArithOp::Sub => "-",
            ArithOp::Mul => "*",
            ArithOp::Div => "/",
            ArithOp::Mod => "%",
            ArithOp::Pow => "**",
            ArithOp::Neg => "-",
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            ArithOp::Add => "add",
            ArithOp::Sub => "sub",
            ArithOp::Mul => "mul",
            ArithOp::Div => "div",
            ArithOp::Mod => "mod",
            ArithOp::Pow => "pow",
            ArithOp::Neg => "neg",
        }
    }
}

/// What a body needs from a type: the class of a constraint.
#[derive(Debug, Clone, PartialEq)]
pub enum Class {
    /// Structural equality (`==`), derived for every type.
    Eq,
    /// Ordering (`<`, `sorted`, `min`), derived for every type.
    Ord,
    /// Rendering to text (`print`, f-strings, `str`), derived for every type.
    Show,
    /// One arithmetic operator: `+` on int, float, str and list; the others
    /// on int and float; a class may define any of them as a method.
    Arith(ArithOp),
    /// `a or b`: logical on bools, the default on `T | nothing`.
    OrElse(Type, Type),
    /// `len(x)`: list, str, dict, range.
    Len,
    /// The zero a sum starts from: int, float, str, list.
    Zero,
    /// `for x in subject` yields `elem`: list, range, str, dict entries.
    Iter(Type),
    /// `subject[idx] : elem`: list or str (int index), dict (str index,
    /// elem is then `T | nothing`), a pair (a literal 0 or 1, which the
    /// option records).
    Index(Type, Type, Option<i64>),
    /// `subject[idx] = value`, answering the updated subject.
    IndexSet(Type, Type),
    /// `subject.name : ty`
    Field(String, Type),
    /// `subject.name = value`, answering the updated subject.
    SetField(String, Type),
    /// `subject.name(args) : ret`: a builtin method or a class method that
    /// does not mutate its receiver.
    Method(String, Vec<Type>, Type),
    /// `str(x)`, `int(x)`, `float(x)`: conversions, overloaded on the
    /// argument.
    Convert(&'static str, Type),
}

/// How a solved constraint is implemented (the lowering reads this).
impl Class {
    /// Classes whose operation may abort for some subjects (indexing,
    /// methods, conversions): their dictionary form answers a result, and
    /// a def that takes such a dictionary may abort.
    pub fn fallible(&self) -> bool {
        matches!(self, Class::Index(..) | Class::IndexSet(..) | Class::Method(..) | Class::Convert(..))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Solution {
    /// Implemented from the class and the resolved subject type alone
    /// (builtin methods, derived show/eq/lt, arithmetic), with the
    /// constraints on the subject's parts it needs in turn (showing a
    /// list needs showing its elements; summing needs adding them).
    Concrete(Vec<ConstraintId>),
    /// A class method: the def, its type arguments and dictionaries at this
    /// use (an instantiation of its scheme).
    Method(usize, Vec<Type>, Vec<ConstraintId>),
    /// A field of a data type (constructor 0), as the (type, field) steps
    /// from the subject to it: several steps read through adopted parents.
    Field(Vec<(TypeId, usize)>),
    /// Forwarded from a dictionary parameter of the enclosing def (its
    /// index in that def's `dicts`), because the subject stayed generic.
    Param(usize),
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub class: Class,
    pub subject: Type,
    pub line: usize,
    pub solution: Option<Solution>,
    /// The unit the constraint belongs to (whose scheme may quantify it).
    pub owner: usize,
    /// The def whose body performs the operation (a lambda inside the
    /// unit, or the unit itself): where its effect lands.
    pub user: usize,
}

/// A type scheme: quantified variables, the constraints on them (by id),
/// and the body.
#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<TVar>,
    pub dicts: Vec<ConstraintId>,
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

/// Storage for type variables, closure-set variables and constraints.
#[derive(Debug, Default, Clone)]
pub struct TypeStore {
    vars: Vec<Binding>,
    clos: Vec<ClosNode>,
    pub constraints: Vec<Constraint>,
    pub level: u32,
}

#[derive(Debug, Clone)]
pub struct UnifyError {
    pub left: Type,
    pub right: Type,
}

impl TypeStore {
    pub fn new() -> Self {
        TypeStore { vars: Vec::new(), clos: Vec::new(), constraints: Vec::new(), level: 1 }
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

    fn clos_root(&self, mut c: ClosVar) -> ClosVar {
        loop {
            match &self.clos[c as usize] {
                ClosNode::Link(n) => c = *n,
                ClosNode::Root(_) => return c,
            }
        }
    }

    pub fn clos_set(&self, c: ClosVar) -> BTreeSet<ClosId> {
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
            Type::Fn(ps, r, c) => Type::Fn(ps.iter().map(|p| self.resolve(p)).collect(), Box::new(self.resolve(&r)), c),
            Type::Data(id, args) => Type::Data(id, args.iter().map(|a| self.resolve(a)).collect()),
            other => other,
        }
    }

    fn occurs(&self, v: TVar, t: &Type) -> bool {
        match self.shallow(t) {
            Type::Var(w) => w == v,
            Type::List(e) | Type::Map(e) => self.occurs(v, &e),
            Type::Fn(ps, r, _) => ps.iter().any(|p| self.occurs(v, p)) || self.occurs(v, &r),
            Type::Data(_, args) => args.iter().any(|a| self.occurs(v, a)),
            _ => false,
        }
    }

    pub fn var_level(&self, v: TVar) -> u32 {
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
            Type::List(e) | Type::Map(e) => self.adjust_levels(&e, level),
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.adjust_levels(p, level);
                }
                self.adjust_levels(&r, level);
            }
            Type::Data(_, args) => {
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
            | (Type::Unit, Type::Unit) => Ok(()),
            (Type::List(x), Type::List(y)) | (Type::Map(x), Type::Map(y)) => self.unify(x, y),
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
            (Type::Data(i, x), Type::Data(j, y)) if i == j && x.len() == y.len() => {
                for (p, q) in x.iter().zip(y.iter()) {
                    self.unify(p, q)?;
                }
                Ok(())
            }
            _ => Err(UnifyError { left: a.clone(), right: b.clone() }),
        }
    }

    /// Generalize a type over the variables above the current level. The
    /// constraints whose subject mentions a quantified variable become the
    /// scheme's dictionaries; `owner` limits them to the def being closed.
    pub fn generalize(&self, t: &Type, owner: usize) -> Scheme {
        let mut vars = Vec::new();
        self.collect_generic(t, &mut vars);
        // constraints on quantified variables come along, and the variables
        // their classes mention (a field's type, an element type) are
        // quantified too, with their own constraints, until nothing changes
        let mut dicts: Vec<ConstraintId> = Vec::new();
        loop {
            let before = (vars.len(), dicts.len());
            for (id, c) in self.constraints.iter().enumerate() {
                if c.owner != owner || c.solution.is_some() || dicts.contains(&id) {
                    continue;
                }
                let mut fv = Vec::new();
                self.free_vars(&c.subject, &mut fv);
                if fv.iter().any(|v| vars.contains(v)) {
                    dicts.push(id);
                    for ct in TypeStore::class_types(&c.class) {
                        let mut cv = Vec::new();
                        self.collect_generic(&ct, &mut cv);
                        for v in cv {
                            if !vars.contains(&v) {
                                vars.push(v);
                            }
                        }
                    }
                }
            }
            if (vars.len(), dicts.len()) == before {
                break;
            }
        }
        Scheme { vars, dicts, ty: self.resolve(t) }
    }

    fn collect_generic(&self, t: &Type, out: &mut Vec<TVar>) {
        match self.shallow(t) {
            Type::Var(v) => {
                if self.var_level(v) > self.level && !out.contains(&v) {
                    out.push(v);
                }
            }
            Type::List(e) | Type::Map(e) => self.collect_generic(&e, out),
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.collect_generic(p, out);
                }
                self.collect_generic(&r, out);
            }
            Type::Data(_, args) => {
                for a in &args {
                    self.collect_generic(a, out);
                }
            }
            _ => {}
        }
    }

    /// Instantiate a scheme with fresh variables. Returns the type, the
    /// substitution, and one new constraint per dictionary of the scheme
    /// (raised in `owner`), which the call site passes along.
    pub fn instantiate(&mut self, s: &Scheme, owner: usize, user: usize, line: usize) -> (Type, Vec<(TVar, Type)>, Vec<ConstraintId>) {
        let subst: Vec<(TVar, Type)> = s.vars.iter().map(|v| (*v, self.fresh())).collect();
        let t = self.substitute(&s.ty, &subst);
        let mut dicts = Vec::new();
        for &d in &s.dicts {
            let c = self.constraints[d].clone();
            let class = self.substitute_class(&c.class, &subst);
            let subject = self.substitute(&c.subject, &subst);
            dicts.push(self.constrain(class, subject, owner, user, line));
        }
        (t, subst, dicts)
    }

    /// Record a new constraint and return its id.
    pub fn constrain(&mut self, class: Class, subject: Type, owner: usize, user: usize, line: usize) -> ConstraintId {
        self.constraints.push(Constraint { class, subject, line, solution: None, owner, user });
        self.constraints.len() - 1
    }

    /// Whether a type (resolved) mentions a variable.
    pub fn mentions(&self, t: &Type, v: TVar) -> bool {
        match self.shallow(t) {
            Type::Var(w) => w == v,
            Type::List(e) | Type::Map(e) => self.mentions(&e, v),
            Type::Fn(ps, r, _) => ps.iter().any(|p| self.mentions(p, v)) || self.mentions(&r, v),
            Type::Data(_, args) => args.iter().any(|a| self.mentions(a, v)),
            _ => false,
        }
    }

    pub fn substitute_class(&mut self, c: &Class, subst: &[(TVar, Type)]) -> Class {
        match c {
            Class::Iter(e) => Class::Iter(self.substitute(e, subst)),
            Class::OrElse(r, t) => Class::OrElse(self.substitute(r, subst), self.substitute(t, subst)),
            Class::Index(i, e, l) => Class::Index(self.substitute(i, subst), self.substitute(e, subst), *l),
            Class::IndexSet(i, v) => Class::IndexSet(self.substitute(i, subst), self.substitute(v, subst)),
            Class::Field(n, t) => Class::Field(n.clone(), self.substitute(t, subst)),
            Class::SetField(n, t) => Class::SetField(n.clone(), self.substitute(t, subst)),
            Class::Method(n, args, ret) => {
                let args = args.iter().map(|a| self.substitute(a, subst)).collect();
                Class::Method(n.clone(), args, self.substitute(ret, subst))
            }
            Class::Convert(n, t) => Class::Convert(n, self.substitute(t, subst)),
            other => other.clone(),
        }
    }

    /// Replace quantified variables. Function closure variables are kept:
    /// every instance of a polymorphic function shares the closure set of
    /// its definition.
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
            Type::Fn(ps, r, c) => {
                let ps = ps.iter().map(|p| self.substitute(p, subst)).collect();
                let r = self.substitute(&r, subst);
                Type::Fn(ps, Box::new(r), c)
            }
            Type::Data(id, args) => Type::Data(id, args.iter().map(|a| self.substitute(a, subst)).collect()),
            other => other,
        }
    }

    /// Free (unbound) variables of a type.
    pub fn free_vars(&self, t: &Type, out: &mut Vec<TVar>) {
        match self.shallow(t) {
            Type::Var(v) => {
                if !out.contains(&v) {
                    out.push(v);
                }
            }
            Type::List(e) | Type::Map(e) => self.free_vars(&e, out),
            Type::Fn(ps, r, _) => {
                for p in &ps {
                    self.free_vars(p, out);
                }
                self.free_vars(&r, out);
            }
            Type::Data(_, args) => {
                for a in &args {
                    self.free_vars(a, out);
                }
            }
            _ => {}
        }
    }

    /// The types a constraint's class mentions besides its subject.
    pub fn class_types(c: &Class) -> Vec<Type> {
        match c {
            Class::Iter(e) => vec![e.clone()],
            Class::Index(i, e, _) | Class::IndexSet(i, e) | Class::OrElse(i, e) => vec![i.clone(), e.clone()],
            Class::Field(_, t) | Class::SetField(_, t) | Class::Convert(_, t) => vec![t.clone()],
            Class::Method(_, args, ret) => {
                let mut v = args.clone();
                v.push(ret.clone());
                v
            }
            _ => vec![],
        }
    }
}

/// Human-readable type names for diagnostics. Data type names are supplied
/// by the caller through `names`.
pub struct TypeDisplay<'a> {
    pub store: &'a TypeStore,
    pub ty: &'a Type,
    pub names: &'a dyn Fn(TypeId) -> String,
}

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(store: &TypeStore, t: &Type, names: &dyn Fn(TypeId) -> String, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match store.shallow(t) {
                Type::Var(v) => write!(f, "?{}", v),
                Type::Int => write!(f, "int"),
                Type::Float => write!(f, "float"),
                Type::Str => write!(f, "str"),
                Type::Bool => write!(f, "bool"),
                Type::Unit => write!(f, "nothing"),
                Type::List(e) => {
                    write!(f, "[")?;
                    go(store, &e, names, f)?;
                    write!(f, "]")
                }
                Type::Map(e) => {
                    write!(f, "{{str: ")?;
                    go(store, &e, names, f)?;
                    write!(f, "}}")
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
                Type::Data(MAYBE, args) => {
                    go(store, &args[0], names, f)?;
                    write!(f, " | nothing")
                }
                Type::Data(RESULT, args) => {
                    write!(f, "result(ok: ")?;
                    go(store, &args[1], names, f)?;
                    write!(f, ", err: ")?;
                    go(store, &args[0], names, f)?;
                    write!(f, ")")
                }
                Type::Data(RANGE, _) => write!(f, "range"),
                Type::Data(id, args) => {
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
        let scheme = s.generalize(&f, 0);
        assert_eq!(scheme.vars.len(), 1);
        let (inst, _, _) = s.instantiate(&scheme, 0, 0, 0);
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
        let (inst2, _, _) = s.instantiate(&scheme, 0, 0, 0);
        assert!(matches!(s.resolve(&inst2), Type::Fn(_, _, _)));
        assert!(s.unify(&Type::Int, &Type::Str).is_err());
    }

    #[test]
    fn constraints_become_dictionaries() {
        let mut s = TypeStore::new();
        s.enter_level();
        let a = s.fresh();
        let c = s.constrain(Class::Ord, a.clone(), 7, 7, 1);
        let f = s.fresh_fn(vec![a.clone(), a.clone()], Type::Bool);
        s.leave_level();
        let scheme = s.generalize(&f, 7);
        assert_eq!(scheme.dicts, vec![c]);
        let (_, _, dicts) = s.instantiate(&scheme, 8, 8, 2);
        assert_eq!(dicts.len(), 1);
        assert_eq!(s.constraints[dicts[0]].owner, 8);
    }
}
