// src/bend/ir.rs
// A small AST for the subset of Bend 2 the backend emits, and its printer.
//
// The IR mirrors Bend's surface forms one to one (types, defs, match trees,
// do-blocks, template arguments), so the printer is a straightforward
// pretty-printer and every rule Bend enforces (see docs/compiler.md) is
// the lowering's responsibility, not the printer's.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    U32,
    F32,
    Str,
    Bool,
    Unit,
    Nat,
    Char,
    /// `List<&2, T>`
    List(Box<Ty>),
    /// `Maybe<&2, T>`
    Maybe(Box<Ty>),
    /// `Result<&2, &2, E, A>`
    Result(Box<Ty>, Box<Ty>),
    /// `Map<&2, V>` — Bend's string-keyed map
    Map(Box<Ty>),
    /// A user or prelude type applied to type arguments.
    Named(String, Vec<Ty>),
    /// Curried function type `A -> B -> R`. Empty params means `Unit -> R`
    /// is NOT used; nullary functions are just defs.
    Fn(Vec<Ty>, Box<Ty>),
    /// `IO(T)`
    Io(Box<Ty>),
    /// `A & B`
    Tuple(Box<Ty>, Box<Ty>),
    /// A type parameter of a polymorphic prelude def, or the kind `Data`
    /// itself when used as an erased-argument kind.
    Param(String),
}

impl Ty {
    /// Replace type parameters by name.
    pub fn subst_params(&self, m: &[(String, Ty)]) -> Ty {
        match self {
            Ty::Param(p) => m.iter().find(|(n, _)| n == p).map(|(_, t)| t.clone()).unwrap_or_else(|| self.clone()),
            Ty::List(t) => Ty::List(Box::new(t.subst_params(m))),
            Ty::Maybe(t) => Ty::Maybe(Box::new(t.subst_params(m))),
            Ty::Result(e, a) => Ty::Result(Box::new(e.subst_params(m)), Box::new(a.subst_params(m))),
            Ty::Map(t) => Ty::Map(Box::new(t.subst_params(m))),
            Ty::Named(n, args) => Ty::Named(n.clone(), args.iter().map(|a| a.subst_params(m)).collect()),
            Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|a| a.subst_params(m)).collect(), Box::new(r.subst_params(m))),
            Ty::Io(t) => Ty::Io(Box::new(t.subst_params(m))),
            Ty::Tuple(a, b) => Ty::Tuple(Box::new(a.subst_params(m)), Box::new(b.subst_params(m))),
            _ => self.clone(),
        }
    }

    pub fn list(t: Ty) -> Ty {
        Ty::List(Box::new(t))
    }
    pub fn maybe(t: Ty) -> Ty {
        Ty::Maybe(Box::new(t))
    }
    pub fn result(e: Ty, a: Ty) -> Ty {
        Ty::Result(Box::new(e), Box::new(a))
    }
    pub fn io(t: Ty) -> Ty {
        Ty::Io(Box::new(t))
    }
    pub fn func(params: Vec<Ty>, ret: Ty) -> Ty {
        Ty::Fn(params, Box::new(ret))
    }
    pub fn tuple(a: Ty, b: Ty) -> Ty {
        Ty::Tuple(Box::new(a), Box::new(b))
    }

    /// Names of user types (`Named`) this type mentions, for ordering.
    pub fn named_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Ty::List(t) | Ty::Maybe(t) | Ty::Map(t) | Ty::Io(t) => t.named_refs(out),
            Ty::Result(a, b) | Ty::Tuple(a, b) => {
                a.named_refs(out);
                b.named_refs(out);
            }
            Ty::Named(n, args) => {
                out.insert(n.clone());
                for a in args {
                    a.named_refs(out);
                }
            }
            Ty::Fn(ps, r) => {
                for p in ps {
                    p.named_refs(out);
                }
                r.named_refs(out);
            }
            _ => {}
        }
    }

    fn write(&self, out: &mut String, in_arrow: bool) {
        match self {
            Ty::U32 => out.push_str("U32"),
            Ty::F32 => out.push_str("F32"),
            Ty::Str => out.push_str("String"),
            Ty::Bool => out.push_str("Bool"),
            Ty::Unit => out.push_str("Unit"),
            Ty::Nat => out.push_str("Nat"),
            Ty::Char => out.push_str("Char"),
            Ty::List(t) => {
                out.push_str("List<&2, ");
                t.write(out, false);
                out.push('>');
            }
            Ty::Maybe(t) => {
                out.push_str("Maybe<&2, ");
                t.write(out, false);
                out.push('>');
            }
            Ty::Result(e, a) => {
                out.push_str("Result<&2, &2, ");
                e.write(out, false);
                out.push_str(", ");
                a.write(out, false);
                out.push('>');
            }
            Ty::Map(t) => {
                out.push_str("Map<&2, ");
                t.write(out, false);
                out.push('>');
            }
            Ty::Named(n, args) => {
                out.push_str(n);
                if !args.is_empty() {
                    out.push('<');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        a.write(out, false);
                    }
                    out.push('>');
                }
            }
            Ty::Fn(ps, r) => {
                if in_arrow {
                    out.push('(');
                }
                for p in ps {
                    p.write(out, true);
                    out.push_str(" -> ");
                }
                r.write(out, true);
                if in_arrow {
                    out.push(')');
                }
            }
            Ty::Io(t) => {
                out.push_str("IO(");
                t.write(out, false);
                out.push(')');
            }
            Ty::Tuple(a, b) => {
                out.push('(');
                a.write(out, true);
                out.push_str(" & ");
                b.write(out, true);
                out.push(')');
            }
            Ty::Param(p) => out.push_str(p),
        }
    }

    pub fn render(&self) -> String {
        let mut s = String::new();
        self.write(&mut s, false);
        s
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Var(String),
    U32(u32),
    F32(f32),
    Nat(u64),
    Str(String),
    Chr(char),
    /// `Name{a, b}`
    Ctor(String, Vec<Term>),
    /// `f(args)` — a call of a def (possibly with template / erased args).
    Call(String, Vec<Term>),
    /// `f(args)` where `f` is a local closure variable.
    CallVar(String, Vec<Term>),
    /// `x => body` (curried for several params).
    Lam(Vec<String>, Box<Term>),
    /// `(a op b : T)` — arithmetic in the namespace of `T`.
    Op(Box<Term>, &'static str, Box<Term>, Ty),
    /// `a ++ b`
    Cat(Box<Term>, Box<Term>),
    /// `a && b`, `a || b`
    And(Box<Term>, Box<Term>),
    Or(Box<Term>, Box<Term>),
    /// `h <> t`
    Cons(Box<Term>, Box<Term>),
    /// `[a, b, c]`
    List(Vec<Term>),
    /// `(a, b)`
    Tuple(Box<Term>, Box<Term>),
    /// `~name` — a template reference to a def.
    TmplRef(String),
    /// `~T` — a template type argument.
    TmplTy(Ty),
    /// A type passed as an erased argument.
    TyArg(Ty),
    /// `{t : T}`
    Ann(Box<Term>, Ty),
}

impl Term {
    pub fn var(s: &str) -> Term {
        Term::Var(s.to_string())
    }
    pub fn call(f: &str, args: Vec<Term>) -> Term {
        Term::Call(f.to_string(), args)
    }
    pub fn ctor(c: &str, args: Vec<Term>) -> Term {
        Term::Ctor(c.to_string(), args)
    }
    pub fn op(a: Term, op: &'static str, b: Term, ty: Ty) -> Term {
        Term::Op(Box::new(a), op, Box::new(b), ty)
    }
    pub fn cat(a: Term, b: Term) -> Term {
        Term::Cat(Box::new(a), Box::new(b))
    }
    pub fn unit() -> Term {
        Term::ctor("Unit", vec![])
    }
    pub fn boolean(b: bool) -> Term {
        Term::ctor(if b { "True" } else { "False" }, vec![])
    }

    fn write(&self, out: &mut String) {
        match self {
            Term::Var(v) => out.push_str(v),
            Term::U32(n) => write!(out, "{}", n).unwrap(),
            Term::F32(x) => {
                let s = format!("{:?}", x);
                out.push_str(&s);
                if !s.contains('.') && !s.contains('e') && !s.contains("inf") && !s.contains("NaN") {
                    out.push_str(".0");
                }
            }
            Term::Nat(n) => write!(out, "{}n", n).unwrap(),
            Term::Str(s) => {
                out.push('"');
                for c in s.chars() {
                    match c {
                        '"' => out.push_str("\\\""),
                        '\\' => out.push_str("\\\\"),
                        '\n' => out.push_str("\\n"),
                        '\t' => out.push_str("\\t"),
                        '\r' => out.push_str("\\r"),
                        c => out.push(c),
                    }
                }
                out.push('"');
            }
            Term::Chr(c) => {
                out.push('\'');
                match c {
                    '\'' => out.push_str("\\'"),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\t' => out.push_str("\\t"),
                    c => out.push(*c),
                }
                out.push('\'');
            }
            Term::Ctor(name, args) => {
                out.push_str(name);
                out.push('{');
                write_args(out, args);
                out.push('}');
            }
            Term::Call(f, args) | Term::CallVar(f, args) => {
                out.push_str(f);
                out.push('(');
                write_args(out, args);
                out.push(')');
            }
            Term::Lam(params, body) => {
                for p in params {
                    out.push_str(p);
                    out.push_str(" => ");
                }
                body.write(out);
            }
            Term::Op(a, op, b, ty) => {
                out.push('(');
                a.write(out);
                out.push(' ');
                out.push_str(op);
                out.push(' ');
                b.write(out);
                out.push_str(" : ");
                ty.write(out, false);
                out.push(')');
            }
            Term::Cat(a, b) => {
                out.push('(');
                a.write(out);
                out.push_str(" ++ ");
                b.write(out);
                out.push(')');
            }
            Term::And(a, b) => {
                out.push('(');
                a.write(out);
                out.push_str(" && ");
                b.write(out);
                out.push(')');
            }
            Term::Or(a, b) => {
                out.push('(');
                a.write(out);
                out.push_str(" || ");
                b.write(out);
                out.push(')');
            }
            Term::Cons(h, t) => {
                out.push('(');
                h.write(out);
                out.push_str(" <> ");
                t.write(out);
                out.push(')');
            }
            Term::List(items) => {
                out.push('[');
                write_args(out, items);
                out.push(']');
            }
            Term::Tuple(a, b) => {
                out.push('(');
                a.write(out);
                out.push_str(", ");
                b.write(out);
                out.push(')');
            }
            Term::TmplRef(name) => {
                out.push('~');
                out.push_str(name);
            }
            Term::TmplTy(ty) => {
                out.push('~');
                ty.write(out, false);
            }
            Term::TyArg(ty) => ty.write(out, false),
            Term::Ann(t, ty) => {
                out.push('{');
                t.write(out);
                out.push_str(" : ");
                ty.write(out, false);
                out.push('}');
            }
        }
    }

    /// Def names this term calls or references as templates.
    pub fn def_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Term::Call(f, args) => {
                out.insert(f.clone());
                for a in args {
                    a.def_refs(out);
                }
            }
            Term::TmplRef(f) => {
                out.insert(f.clone());
            }
            Term::CallVar(_, args) | Term::Ctor(_, args) | Term::List(args) => {
                for a in args {
                    a.def_refs(out);
                }
            }
            Term::Lam(_, b) | Term::Ann(b, _) => b.def_refs(out),
            Term::Op(a, _, b, _)
            | Term::Cat(a, b)
            | Term::And(a, b)
            | Term::Or(a, b)
            | Term::Cons(a, b)
            | Term::Tuple(a, b) => {
                a.def_refs(out);
                b.def_refs(out);
            }
            _ => {}
        }
    }

    /// Count of syntactic occurrences of each variable name.
    pub fn count_vars(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Term::Var(v) => *counts.entry(v.clone()).or_insert(0) += 1,
            Term::CallVar(f, args) => {
                *counts.entry(f.clone()).or_insert(0) += 1;
                for a in args {
                    a.count_vars(counts);
                }
            }
            Term::Call(_, args) | Term::Ctor(_, args) | Term::List(args) => {
                for a in args {
                    a.count_vars(counts);
                }
            }
            Term::Lam(params, b) => {
                let mut inner = HashMap::new();
                b.count_vars(&mut inner);
                for p in params {
                    inner.remove(p);
                }
                for (k, v) in inner {
                    *counts.entry(k).or_insert(0) += v;
                }
            }
            Term::Ann(b, _) => b.count_vars(counts),
            Term::Op(a, _, b, _)
            | Term::Cat(a, b)
            | Term::And(a, b)
            | Term::Or(a, b)
            | Term::Cons(a, b)
            | Term::Tuple(a, b) => {
                a.count_vars(counts);
                b.count_vars(counts);
            }
            _ => {}
        }
    }
}

fn write_args(out: &mut String, args: &[Term]) {
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        a.write(out);
    }
}

// ---------------------------------------------------------------------------
// Statements and bodies
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// Pure let: `x = v` / `+x = v` (outside do-blocks) or `x : T = v`
    /// (inside do-blocks, where `reusable` must be false).
    Let { name: String, reusable: bool, ty: Option<Ty>, value: Term },
    /// `x : T <- m` inside a do-block.
    Bind { name: String, ty: Ty, value: Term },
    /// `K{a, b} = v` — only legal when `v` is a parameter or field.
    Destructure { ctor: String, fields: Vec<String>, value: Term },
    /// `(a, b) = v` — only legal when `v` is a parameter or field.
    TupleLet { a: String, b: String, value: Term },
    /// A unit step inside a do-block.
    Step(Term),
    /// `a b = f(x) g(y)` — a parallel let.
    ParLet { names: Vec<String>, calls: Vec<Term> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    /// `K{a, b}` — field binders, each optionally `+`.
    Ctor(String, Vec<(String, bool)>),
    /// `_`
    Wild,
    /// `0n`
    Zero,
    /// `1n+p`
    Succ(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Body {
    /// `match x:` with one body per case. `x` must be a parameter or a
    /// field bound by an enclosing pattern.
    Match { scrutinee: String, arms: Vec<(Pat, Body)> },
    /// Pure block: lets, then a tail term.
    Block { stmts: Vec<Stmt>, tail: Term },
    /// `do M<..>:` block. `monad` is the full monadic type (`IO(T)` or
    /// `Result<...>`); `tail` is either `return v` or a final monadic term.
    Do { monad: Ty, stmts: Vec<Stmt>, tail: DoTail },
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoTail {
    Return(Term),
    Step(Term),
}

impl Body {
    pub fn term(t: Term) -> Body {
        Body::Block { stmts: vec![], tail: t }
    }

    pub fn def_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Body::Match { arms, .. } => {
                for (_, b) in arms {
                    b.def_refs(out);
                }
            }
            Body::Block { stmts, tail } => {
                for s in stmts {
                    s.def_refs(out);
                }
                tail.def_refs(out);
            }
            Body::Do { stmts, tail, .. } => {
                for s in stmts {
                    s.def_refs(out);
                }
                match tail {
                    DoTail::Return(t) | DoTail::Step(t) => t.def_refs(out),
                }
            }
        }
    }

    /// Variable use counts, taking the maximum across match arms.
    pub fn count_vars(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Body::Match { scrutinee, arms } => {
                *counts.entry(scrutinee.clone()).or_insert(0) += 1;
                let mut best: HashMap<String, usize> = HashMap::new();
                for (_, b) in arms {
                    let mut c = HashMap::new();
                    b.count_vars(&mut c);
                    for (k, v) in c {
                        let e = best.entry(k).or_insert(0);
                        if v > *e {
                            *e = v;
                        }
                    }
                }
                for (k, v) in best {
                    *counts.entry(k).or_insert(0) += v;
                }
            }
            Body::Block { stmts, tail } => {
                for s in stmts {
                    s.count_vars(counts);
                }
                tail.count_vars(counts);
            }
            Body::Do { stmts, tail, .. } => {
                for s in stmts {
                    s.count_vars(counts);
                }
                match tail {
                    DoTail::Return(t) | DoTail::Step(t) => t.count_vars(counts),
                }
            }
        }
    }

    fn write(&self, out: &mut String, indent: usize) {
        let pad = "  ".repeat(indent);
        match self {
            Body::Match { scrutinee, arms } => {
                writeln!(out, "{}match {}:", pad, scrutinee).unwrap();
                for (pat, body) in arms {
                    write!(out, "{}  case ", pad).unwrap();
                    match pat {
                        Pat::Ctor(name, fields) => {
                            out.push_str(name);
                            out.push('{');
                            for (i, (f, reusable)) in fields.iter().enumerate() {
                                if i > 0 {
                                    out.push_str(", ");
                                }
                                if *reusable {
                                    out.push('+');
                                }
                                out.push_str(f);
                            }
                            out.push('}');
                        }
                        Pat::Wild => out.push('_'),
                        Pat::Zero => out.push_str("0n"),
                        Pat::Succ(p) => {
                            out.push_str("1n+");
                            out.push_str(p);
                        }
                    }
                    out.push_str(":\n");
                    body.write(out, indent + 2);
                }
            }
            Body::Block { stmts, tail } => {
                for s in stmts {
                    s.write(out, indent);
                }
                out.push_str(&pad);
                tail.write(out);
                out.push('\n');
            }
            Body::Do { monad, stmts, tail } => {
                write!(out, "{}do ", pad).unwrap();
                match monad {
                    Ty::Io(t) => {
                        out.push_str("IO<");
                        t.write(out, false);
                        out.push('>');
                    }
                    Ty::Result(e, a) => {
                        out.push_str("Result<&2, &2, ");
                        e.write(out, false);
                        out.push_str(", ");
                        a.write(out, false);
                        out.push('>');
                    }
                    other => other.write(out, false),
                }
                out.push_str(":\n");
                for s in stmts {
                    s.write(out, indent + 1);
                }
                out.push_str(&pad);
                out.push_str("  ");
                match tail {
                    DoTail::Return(t) => {
                        out.push_str("return ");
                        t.write(out);
                    }
                    DoTail::Step(t) => t.write(out),
                }
                out.push('\n');
            }
        }
    }
}

impl Stmt {
    pub fn def_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Stmt::Let { value, .. }
            | Stmt::Bind { value, .. }
            | Stmt::Destructure { value, .. }
            | Stmt::TupleLet { value, .. }
            | Stmt::Step(value) => value.def_refs(out),
            Stmt::ParLet { calls, .. } => {
                for c in calls {
                    c.def_refs(out);
                }
            }
        }
    }

    pub fn count_vars(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Stmt::Let { value, .. }
            | Stmt::Bind { value, .. }
            | Stmt::Destructure { value, .. }
            | Stmt::TupleLet { value, .. }
            | Stmt::Step(value) => value.count_vars(counts),
            Stmt::ParLet { calls, .. } => {
                for c in calls {
                    c.count_vars(counts);
                }
            }
        }
    }

    fn write(&self, out: &mut String, indent: usize) {
        let pad = "  ".repeat(indent);
        out.push_str(&pad);
        match self {
            Stmt::Let { name, reusable, ty, value } => {
                if *reusable {
                    out.push('+');
                }
                out.push_str(name);
                if let Some(t) = ty {
                    out.push_str(" : ");
                    t.write(out, false);
                }
                out.push_str(" = ");
                value.write(out);
            }
            Stmt::Bind { name, ty, value } => {
                out.push_str(name);
                out.push_str(" : ");
                ty.write(out, false);
                out.push_str(" <- ");
                value.write(out);
            }
            Stmt::Destructure { ctor, fields, value } => {
                out.push_str(ctor);
                out.push('{');
                out.push_str(&fields.join(", "));
                out.push_str("} = ");
                value.write(out);
            }
            Stmt::TupleLet { a, b, value } => {
                write!(out, "({}, {}) = ", a, b).unwrap();
                value.write(out);
            }
            Stmt::Step(t) => t.write(out),
            Stmt::ParLet { names, calls } => {
                out.push_str(&names.join(" "));
                out.push_str(" = ");
                for (i, c) in calls.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    c.write(out);
                }
            }
        }
        out.push('\n');
    }
}

// ---------------------------------------------------------------------------
// Definitions and programs
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub reusable: bool,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Def {
    pub name: String,
    pub is_unsafe: bool,
    /// `~A: Data` template type parameters (first in the list).
    pub tmpl_types: Vec<String>,
    /// `~f: T` template function parameters (after the types).
    pub tmpl_funcs: Vec<(String, Ty)>,
    /// `-A: Data` erased type parameters.
    pub erased: Vec<String>,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Body,
}

impl Def {
    pub fn def_refs(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.body.def_refs(&mut out);
        out.remove(&self.name);
        out
    }

    fn write(&self, out: &mut String) {
        if self.is_unsafe {
            out.push_str("@unsafe\n");
        }
        out.push_str("def ");
        out.push_str(&self.name);
        out.push('(');
        let mut first = true;
        let mut sep = |out: &mut String| {
            if !first {
                out.push_str(", ");
            }
            first = false;
        };
        for t in &self.tmpl_types {
            sep(out);
            write!(out, "~{}: Data", t).unwrap();
        }
        for (f, ty) in &self.tmpl_funcs {
            sep(out);
            write!(out, "~{}: ", f).unwrap();
            ty.write(out, false);
        }
        for e in &self.erased {
            sep(out);
            write!(out, "-{}: Data", e).unwrap();
        }
        for p in &self.params {
            sep(out);
            if p.reusable {
                out.push('+');
            }
            out.push_str(&p.name);
            out.push_str(": ");
            p.ty.write(out, false);
        }
        out.push_str(") -> ");
        self.ret.write(out, false);
        out.push_str(":\n");
        self.body.write(out, 1);
        out.push('\n');
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub name: String,
    /// `-A: Data` parameters.
    pub params: Vec<String>,
    pub ctors: Vec<(String, Vec<(String, Ty)>)>,
}

impl TypeDef {
    fn write(&self, out: &mut String) {
        out.push_str("type ");
        out.push_str(&self.name);
        if !self.params.is_empty() {
            out.push('<');
            for (i, p) in self.params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write!(out, "-{}: Data", p).unwrap();
            }
            out.push('>');
        }
        out.push_str(" is Data:\n");
        for (c, fields) in &self.ctors {
            out.push_str("  ");
            out.push_str(c);
            out.push('{');
            for (i, (f, ty)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(f);
                out.push_str(": ");
                ty.write(out, false);
            }
            out.push_str("}\n");
        }
        out.push('\n');
    }

    fn type_refs(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for (_, fields) in &self.ctors {
            for (_, ty) in fields {
                ty.named_refs(&mut out);
            }
        }
        out.remove(&self.name);
        out
    }
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub types: Vec<TypeDef>,
    pub defs: Vec<Def>,
    /// Verbatim Bend source placed after `import Base` and before the
    /// generated declarations (the prelude).
    pub raw_prelude: String,
}

impl Program {
    /// Render the program with types and defs in dependency order, after
    /// the part of the prelude it uses.
    pub fn render(&self) -> String {
        let mut body = String::new();
        for t in order_types(&self.types) {
            t.write(&mut body);
        }
        for d in order_defs(&self.defs) {
            d.write(&mut body);
        }
        let prelude = crate::prune::prune_prelude(&self.raw_prelude, &body);
        let mut out = String::new();
        out.push_str("import Base\n\n");
        out.push_str(&prelude);
        if !prelude.ends_with('\n') {
            out.push('\n');
        }
        out.push('\n');
        out.push_str(&body);
        out
    }
}

/// Topological order of type declarations (a type after the types its
/// fields mention). Self-references are fine; cycles keep source order.
fn order_types(types: &[TypeDef]) -> Vec<&TypeDef> {
    let index: HashMap<&str, usize> = types.iter().enumerate().map(|(i, t)| (t.name.as_str(), i)).collect();
    let mut done = vec![false; types.len()];
    let mut out = Vec::new();
    fn visit<'a>(i: usize, types: &'a [TypeDef], index: &HashMap<&str, usize>, done: &mut [bool], visiting: &mut Vec<usize>, out: &mut Vec<&'a TypeDef>) {
        if done[i] || visiting.contains(&i) {
            return;
        }
        visiting.push(i);
        for r in types[i].type_refs() {
            if let Some(&j) = index.get(r.as_str()) {
                visit(j, types, index, done, visiting, out);
            }
        }
        visiting.pop();
        done[i] = true;
        out.push(&types[i]);
    }
    for i in 0..types.len() {
        visit(i, types, &index, &mut done, &mut Vec::new(), &mut out);
    }
    out
}

/// Topological order of defs (callees before callers). Self-recursion is
/// ignored; a genuine cycle (which Bend would reject anyway) keeps source
/// order so the error surfaces in Bend's checker.
pub fn order_defs(defs: &[Def]) -> Vec<&Def> {
    let index: HashMap<&str, usize> = defs.iter().enumerate().map(|(i, d)| (d.name.as_str(), i)).collect();
    let mut done = vec![false; defs.len()];
    let mut out = Vec::new();
    fn visit<'a>(i: usize, defs: &'a [Def], index: &HashMap<&str, usize>, done: &mut [bool], visiting: &mut Vec<usize>, out: &mut Vec<&'a Def>) {
        if done[i] || visiting.contains(&i) {
            return;
        }
        visiting.push(i);
        for r in defs[i].def_refs() {
            if let Some(&j) = index.get(r.as_str()) {
                visit(j, defs, index, done, visiting, out);
            }
        }
        visiting.pop();
        done[i] = true;
        out.push(&defs[i]);
    }
    for i in 0..defs.len() {
        visit(i, defs, &index, &mut done, &mut Vec::new(), &mut out);
    }
    out
}

/// Detect genuine call cycles between distinct defs (mutual recursion),
/// which Bend rejects. Returns one cycle as a list of names, if any.
pub fn find_mutual_recursion(defs: &[Def]) -> Option<Vec<String>> {
    let index: HashMap<&str, usize> = defs.iter().enumerate().map(|(i, d)| (d.name.as_str(), i)).collect();
    let mut state = vec![0u8; defs.len()]; // 0 new, 1 visiting, 2 done
    let mut stack: Vec<usize> = Vec::new();
    fn visit(i: usize, defs: &[Def], index: &HashMap<&str, usize>, state: &mut [u8], stack: &mut Vec<usize>) -> Option<Vec<String>> {
        state[i] = 1;
        stack.push(i);
        for r in defs[i].def_refs() {
            if let Some(&j) = index.get(r.as_str()) {
                if state[j] == 1 {
                    let pos = stack.iter().position(|&k| k == j).unwrap();
                    return Some(stack[pos..].iter().map(|&k| defs[k].name.clone()).collect());
                }
                if state[j] == 0 {
                    if let Some(c) = visit(j, defs, index, state, stack) {
                        return Some(c);
                    }
                }
            }
        }
        stack.pop();
        state[i] = 2;
        None
    }
    for i in 0..defs.len() {
        if state[i] == 0 {
            if let Some(c) = visit(i, defs, &index, &mut state, &mut stack) {
                return Some(c);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_a_small_def() {
        let d = Def {
            name: "f.sq".into(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: vec![Param { name: "x".into(), reusable: false, ty: Ty::U32 }],
            ret: Ty::U32,
            body: Body::Block {
                stmts: vec![Stmt::Let { name: "y".into(), reusable: true, ty: None, value: Term::var("x") }],
                tail: Term::op(Term::var("y"), "*", Term::var("y"), Ty::U32),
            },
        };
        let mut s = String::new();
        d.write(&mut s);
        assert_eq!(s, "def f.sq(x: U32) -> U32:\n  +y = x\n  (y * y : U32)\n\n");
    }

    #[test]
    fn orders_helpers_before_callers() {
        let mk = |name: &str, calls: &[&str]| Def {
            name: name.into(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: vec![],
            ret: Ty::U32,
            body: Body::term(Term::List(calls.iter().map(|c| Term::call(c, vec![])).collect())),
        };
        let defs = vec![mk("a", &["b", "a"]), mk("b", &["c"]), mk("c", &[])];
        let names: Vec<&str> = order_defs(&defs).iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["c", "b", "a"]);
        assert!(find_mutual_recursion(&defs).is_none());
        let cyc = vec![mk("a", &["b"]), mk("b", &["a"])];
        assert!(find_mutual_recursion(&cyc).is_some());
    }
}
