// src/ir.rs
// A small AST for the subset of Bend 2 the backend emits, and its printer.
//
// The IR mirrors Bend's surface forms one to one (types, defs, match trees,
// do-blocks, template arguments), so the printer is a straightforward
// pretty-printer and every rule Bend enforces (see docs/compiler.md) is
// the lowering's responsibility, not the printer's.

use std::collections::{BTreeSet, HashMap, HashSet};
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
    /// Curried function type `A -> B -> R`.
    Fn(Vec<Ty>, Box<Ty>),
    /// `IO(T)`
    Io(Box<Ty>),
    /// A type parameter of a polymorphic prelude def, or the kind `Data`
    /// itself when used as an erased-argument kind.
    Param(String),
}

impl Ty {
    /// The type parameters it mentions.
    pub fn params(&self, out: &mut BTreeSet<String>) {
        match self {
            Ty::Param(p) => {
                out.insert(p.clone());
            }
            Ty::List(t) | Ty::Maybe(t) | Ty::Map(t) | Ty::Io(t) => t.params(out),
            Ty::Result(a, b) => {
                a.params(out);
                b.params(out);
            }
            Ty::Named(_, args) => {
                for a in args {
                    a.params(out);
                }
            }
            Ty::Fn(ps, r) => {
                for a in ps {
                    a.params(out);
                }
                r.params(out);
            }
            _ => {}
        }
    }

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
            _ => self.clone(),
        }
    }

    pub fn list(t: Ty) -> Ty {
        Ty::List(Box::new(t))
    }
    pub fn maybe(t: Ty) -> Ty {
        Ty::Maybe(Box::new(t))
    }
    pub fn map(t: Ty) -> Ty {
        Ty::Map(Box::new(t))
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

    /// Names of user types (`Named`) this type mentions, for ordering.
    pub fn named_refs(&self, out: &mut BTreeSet<String>) {
        match self {
            Ty::List(t) | Ty::Maybe(t) | Ty::Map(t) | Ty::Io(t) => t.named_refs(out),
            Ty::Result(a, b) => {
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
    /// `[a, b, c]`
    List(Vec<Term>),
    /// `~name` — a template reference to a def.
    TmplRef(String),
    /// `~T` — a template type argument.
    TmplTy(Ty),
    /// `~(t)` — a closed term as a template argument.
    TmplTerm(Box<Term>),
    /// `(f)(args)` — a term (a lambda) applied to arguments.
    App(Box<Term>, Vec<Term>),
    /// A type passed as an erased argument.
    TyArg(Ty),
    /// `(a b = f(x) g(y); body)` — calls evaluated in parallel, their
    /// answers bound for the body.
    Par(Vec<String>, Vec<Term>, Box<Term>),
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

    pub fn render(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }

    fn write(&self, out: &mut String) {
        match self {
            Term::Var(v) => out.push_str(v),
            Term::U32(n) => write!(out, "{}", n).unwrap(),
            Term::F32(x) => {
                // Bend has no negative, infinite or NaN float literals
                if x.is_nan() {
                    out.push_str("(0.0 / 0.0 : F32)");
                } else if x.is_infinite() {
                    out.push_str(if *x > 0.0 { "(1.0 / 0.0 : F32)" } else { "F32.neg((1.0 / 0.0 : F32))" });
                } else if x.is_sign_negative() && *x != 0.0 {
                    out.push_str("F32.neg(");
                    Term::F32(-x).write(out);
                    out.push(')');
                } else {
                    let s = format!("{:?}", x.abs());
                    out.push_str(&s);
                    if !s.contains('.') && !s.contains('e') {
                        out.push_str(".0");
                    }
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
            Term::List(items) => {
                out.push('[');
                write_args(out, items);
                out.push(']');
            }
            Term::TmplRef(name) => {
                out.push('~');
                out.push_str(name);
            }
            Term::TmplTy(ty) => {
                out.push('~');
                ty.write(out, false);
            }
            Term::TmplTerm(t) => {
                out.push_str("~(");
                t.write(out);
                out.push(')');
            }
            Term::App(f, args) => {
                out.push('(');
                f.write(out);
                out.push_str(")(");
                write_args(out, args);
                out.push(')');
            }
            Term::TyArg(ty) => ty.write(out, false),
            Term::Par(names, calls, body) => {
                out.push('(');
                out.push_str(&names.join(" "));
                out.push_str(" =");
                for c in calls {
                    out.push(' ');
                    c.write(out);
                }
                out.push_str("; ");
                body.write(out);
                out.push(')');
            }
        }
    }

    /// The direct subterms.
    fn children(&self) -> Vec<&Term> {
        match self {
            Term::Ctor(_, args) | Term::Call(_, args) | Term::CallVar(_, args) | Term::List(args) => args.iter().collect(),
            Term::App(f, args) => std::iter::once(&**f).chain(args).collect(),
            Term::Lam(_, b) | Term::TmplTerm(b) => vec![&**b],
            Term::Op(a, _, b, _) | Term::Cat(a, b) | Term::And(a, b) | Term::Or(a, b) => vec![&**a, &**b],
            Term::Par(_, calls, body) => calls.iter().chain([&**body]).collect(),
            _ => vec![],
        }
    }

    fn children_mut(&mut self) -> Vec<&mut Term> {
        match self {
            Term::Ctor(_, args) | Term::Call(_, args) | Term::CallVar(_, args) | Term::List(args) => args.iter_mut().collect(),
            Term::App(f, args) => std::iter::once(&mut **f).chain(args).collect(),
            Term::Lam(_, b) | Term::TmplTerm(b) => vec![&mut **b],
            Term::Op(a, _, b, _) | Term::Cat(a, b) | Term::And(a, b) | Term::Or(a, b) => vec![&mut **a, &mut **b],
            Term::Par(_, calls, body) => calls.iter_mut().chain([&mut **body]).collect(),
            _ => vec![],
        }
    }

    /// The type parameters a template argument inside the term mentions:
    /// a template argument must be closed, so each must be a template
    /// parameter of the def.
    pub fn template_params(&self, inside: bool, out: &mut BTreeSet<String>) {
        match self {
            Term::TmplTy(t) => t.params(out),
            Term::TyArg(t) if inside => t.params(out),
            Term::TmplTerm(b) => b.template_params(true, out),
            _ => {
                for c in self.children() {
                    c.template_params(inside, out);
                }
            }
        }
    }

    /// Def names this term calls or references as templates.
    pub fn def_refs(&self, out: &mut BTreeSet<String>) {
        if let Term::Call(f, _) | Term::TmplRef(f) = self {
            out.insert(f.clone());
        }
        for c in self.children() {
            c.def_refs(out);
        }
    }

    /// Mark lambda parameters used more than once in their body as
    /// reusable (`+x`): Bend counts a variable once per use, and a variable
    /// used in two thunks of a pick is used twice.
    pub fn mark_reusable_lambdas(&mut self) {
        if let Term::Lam(params, body) = self {
            body.mark_reusable_lambdas();
            let mut counts = HashMap::new();
            body.count_vars(&mut counts);
            for p in params.iter_mut() {
                if p != "_" && !p.starts_with('+') && counts.get(p.as_str()).cloned().unwrap_or(0) > 1 {
                    *p = format!("+{}", p);
                }
            }
            return;
        }
        for c in self.children_mut() {
            c.mark_reusable_lambdas();
        }
    }

    /// The term with free variables replaced (a lambda's parameters
    /// shadow; a template argument is closed).
    pub fn subst(&self, m: &HashMap<String, Term>) -> Term {
        match self {
            Term::Var(v) => m.get(v).cloned().unwrap_or_else(|| self.clone()),
            Term::TmplTerm(_) => self.clone(),
            Term::Par(names, calls, b) => {
                let mut inner = m.clone();
                for n in names {
                    inner.remove(n.trim_start_matches('+'));
                }
                Term::Par(names.clone(), calls.iter().map(|c| c.subst(m)).collect(), Box::new(b.subst(&inner)))
            }
            Term::Lam(params, b) => {
                let mut inner = m.clone();
                for p in params {
                    inner.remove(p.trim_start_matches('+'));
                }
                Term::Lam(params.clone(), Box::new(b.subst(&inner)))
            }
            _ => {
                let mut t = self.clone();
                for c in t.children_mut() {
                    *c = c.subst(m);
                }
                t
            }
        }
    }

    /// Variables the term reads (a lambda's or parallel let's binders
    /// are its own).
    pub fn free_vars(&self, out: &mut HashSet<String>) {
        match self {
            Term::Var(v) => {
                out.insert(v.clone());
            }
            Term::Lam(params, b) => {
                let mut inner = HashSet::new();
                b.free_vars(&mut inner);
                for p in params {
                    inner.remove(p.trim_start_matches('+'));
                }
                out.extend(inner);
            }
            Term::Par(names, calls, b) => {
                for c in calls {
                    c.free_vars(out);
                }
                let mut inner = HashSet::new();
                b.free_vars(&mut inner);
                for n in names {
                    inner.remove(n.trim_start_matches('+'));
                }
                out.extend(inner);
            }
            _ => {
                if let Term::CallVar(f, _) = self {
                    out.insert(f.clone());
                }
                for c in self.children() {
                    c.free_vars(out);
                }
            }
        }
    }

    /// Count of syntactic occurrences of each variable name.
    pub fn count_vars(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Term::Var(v) => *counts.entry(v.clone()).or_insert(0) += 1,
            Term::App(f, args) => {
                f.count_vars(counts);
                let params: &[String] = match &**f {
                    Term::Lam(ps, _) => ps,
                    _ => &[],
                };
                for (i, a) in args.iter().enumerate() {
                    a.count_vars(counts);
                    // a reusable binder duplicates its argument term: every
                    // variable in it is used again
                    if params.get(i).is_some_and(|p| p.starts_with('+')) {
                        a.count_vars(counts);
                    }
                }
            }
            Term::Par(names, calls, b) => {
                for c in calls {
                    c.count_vars(counts);
                }
                let mut inner = HashMap::new();
                b.count_vars(&mut inner);
                for n in names {
                    inner.remove(n.trim_start_matches('+'));
                }
                for (k, v) in inner {
                    *counts.entry(k).or_insert(0) += v;
                }
            }
            Term::Lam(params, b) => {
                let mut inner = HashMap::new();
                b.count_vars(&mut inner);
                for p in params {
                    inner.remove(p.trim_start_matches('+'));
                }
                for (k, v) in inner {
                    *counts.entry(k).or_insert(0) += v;
                }
            }
            _ => {
                if let Term::CallVar(f, _) = self {
                    *counts.entry(f.clone()).or_insert(0) += 1;
                }
                for c in self.children() {
                    c.count_vars(counts);
                }
            }
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
    /// `x : T <- m` (or `+x : T <- m`) inside a do-block.
    Bind { name: String, reusable: bool, ty: Ty, value: Term },
    /// A unit step inside a do-block.
    Step(Term),
    /// `a b = f(x) g(y)`: calls evaluated in parallel (pure blocks only).
    Par { names: Vec<String>, calls: Vec<Term> },
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

impl DoTail {
    fn term(&self) -> &Term {
        match self {
            DoTail::Return(t) | DoTail::Step(t) => t,
        }
    }

    fn term_mut(&mut self) -> &mut Term {
        match self {
            DoTail::Return(t) | DoTail::Step(t) => t,
        }
    }
}

impl Body {
    pub fn term(t: Term) -> Body {
        Body::Block { stmts: vec![], tail: t }
    }

    /// The terms of a straight body (a block or a do-block): each
    /// statement's value, then the tail. A match has none of its own.
    fn terms(&self) -> Vec<&Term> {
        match self {
            Body::Match { .. } => vec![],
            Body::Block { stmts, tail } => stmts.iter().flat_map(Stmt::values).chain([tail]).collect(),
            Body::Do { stmts, tail, .. } => stmts.iter().flat_map(Stmt::values).chain([tail.term()]).collect(),
        }
    }

    fn terms_mut(&mut self) -> Vec<&mut Term> {
        match self {
            Body::Match { .. } => vec![],
            Body::Block { stmts, tail } => stmts.iter_mut().flat_map(Stmt::values_mut).chain([tail]).collect(),
            Body::Do { stmts, tail, .. } => stmts.iter_mut().flat_map(Stmt::values_mut).chain([tail.term_mut()]).collect(),
        }
    }

    /// See `Term::template_params`.
    pub fn template_params(&self, out: &mut BTreeSet<String>) {
        if let Body::Match { arms, .. } = self {
            for (_, b) in arms {
                b.template_params(out);
            }
        }
        for t in self.terms() {
            t.template_params(false, out);
        }
    }

    pub fn def_refs(&self, out: &mut BTreeSet<String>) {
        if let Body::Match { arms, .. } = self {
            for (_, b) in arms {
                b.def_refs(out);
            }
        }
        for t in self.terms() {
            t.def_refs(out);
        }
    }

    /// Mark the lambdas of every term in the body (see
    /// `Term::mark_reusable_lambdas`).
    pub fn mark_reusable_lambdas(&mut self) {
        if let Body::Match { arms, .. } = self {
            for (_, b) in arms {
                b.mark_reusable_lambdas();
            }
        }
        for t in self.terms_mut() {
            t.mark_reusable_lambdas();
        }
    }

    /// Variable use counts, taking the maximum across match arms.
    pub fn count_vars(&self, counts: &mut HashMap<String, usize>) {
        if let Body::Match { scrutinee, arms } = self {
            *counts.entry(scrutinee.clone()).or_insert(0) += 1;
            let mut best: HashMap<String, usize> = HashMap::new();
            for (_, b) in arms {
                let mut c = HashMap::new();
                b.count_vars(&mut c);
                for (k, v) in c {
                    let e = best.entry(k).or_insert(0);
                    *e = (*e).max(v);
                }
            }
            for (k, v) in best {
                *counts.entry(k).or_insert(0) += v;
            }
        }
        for t in self.terms() {
            t.count_vars(counts);
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
                    s.write(out, indent, None);
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
                    other => other.write(out, false),
                }
                out.push_str(":\n");
                for s in stmts {
                    s.write(out, indent + 1, Some(monad));
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
    /// The terms a statement evaluates.
    fn values(&self) -> Vec<&Term> {
        match self {
            Stmt::Let { value, .. } | Stmt::Bind { value, .. } | Stmt::Step(value) => vec![value],
            Stmt::Par { calls, .. } => calls.iter().collect(),
        }
    }

    fn values_mut(&mut self) -> Vec<&mut Term> {
        match self {
            Stmt::Let { value, .. } | Stmt::Bind { value, .. } | Stmt::Step(value) => vec![value],
            Stmt::Par { calls, .. } => calls.iter_mut().collect(),
        }
    }

    /// Inside a do-block (`monad` given) a reusable let has no syntax of
    /// its own: it binds the value through the monad's `pure`.
    fn write(&self, out: &mut String, indent: usize, monad: Option<&Ty>) {
        let pad = "  ".repeat(indent);
        out.push_str(&pad);
        match self {
            Stmt::Let { name, reusable: true, ty: Some(t), value } if monad.is_some() => {
                write!(out, "+{} : ", name).unwrap();
                t.write(out, false);
                out.push_str(" <- ");
                match monad {
                    Some(Ty::Result(e, _)) => {
                        out.push_str("Result.pure(&2, &2, ");
                        e.write(out, false);
                        out.push_str(", ");
                        t.write(out, false);
                        out.push_str(", ");
                    }
                    _ => {
                        out.push_str("IO.pure(");
                        t.write(out, false);
                        out.push_str(", ");
                    }
                }
                value.write(out);
                out.push(')');
            }
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
            Stmt::Bind { name, reusable, ty, value } => {
                if *reusable {
                    out.push('+');
                }
                out.push_str(name);
                out.push_str(" : ");
                ty.write(out, false);
                out.push_str(" <- ");
                value.write(out);
            }
            Stmt::Step(t) => t.write(out),
            Stmt::Par { names, calls } => {
                out.push_str(&names.join(" "));
                out.push_str(" =");
                for c in calls {
                    out.push(' ');
                    c.write(out);
                }
            }
        }
        out.push('\n');
    }
}

// ---------------------------------------------------------------------------
// Parallel self-calls
// ---------------------------------------------------------------------------
//
// In a pure def every call a term reaches is evaluated (Bend is strict;
// only a lambda's body waits), so two self-calls that one term, or one
// block, evaluates can run at once: `size(l) + size(r)` becomes
// `(a b = size(l) size(r); a + b)`. A call is taken out of the term only
// where it reads no variable the term binds on the way (an applied lambda
// is a let), and never from under a lambda or the right of `&&`/`||`,
// which may not run. A lambda's body is a region of its own.

/// Visit the outermost self-calls a term evaluates, with whether each can
/// move ahead of the term (it reads no variable the term binds).
fn visit_calls(t: &mut Term, me: &str, bound: &mut Vec<String>, f: &mut dyn FnMut(&mut Term, bool)) {
    match t {
        Term::Call(g, _) if g == me => {
            let mut fv = HashSet::new();
            t.free_vars(&mut fv);
            let ok = !bound.iter().any(|b| fv.contains(b));
            f(t, ok);
        }
        Term::Lam(..) | Term::TmplTerm(_) | Term::And(..) | Term::Or(..) => {}
        Term::App(g, args) if matches!(**g, Term::Lam(..)) => {
            for a in args.iter_mut() {
                visit_calls(a, me, bound, f);
            }
            if let Term::Lam(ps, b) = &mut **g {
                let n = bound.len();
                bound.extend(ps.iter().map(|p| p.trim_start_matches('+').to_string()));
                visit_calls(b, me, bound, f);
                bound.truncate(n);
            }
        }
        Term::Par(names, _, b) => {
            let n = bound.len();
            bound.extend(names.iter().map(|n| n.trim_start_matches('+').to_string()));
            visit_calls(b, me, bound, f);
            bound.truncate(n);
        }
        _ => {
            for c in t.children_mut() {
                visit_calls(c, me, bound, f);
            }
        }
    }
}

/// Replace the movable calls `pick` selects (by their order among the
/// term's movable calls) with fresh variables; answers the names and calls.
fn take_calls(t: &mut Term, me: &str, counter: &mut usize, pick: &dyn Fn(usize) -> bool, names: &mut Vec<String>, calls: &mut Vec<Term>) {
    let mut i = 0;
    visit_calls(t, me, &mut Vec::new(), &mut |c, ok| {
        if ok {
            if pick(i) {
                *counter += 1;
                let n = format!("__par{}", counter);
                calls.push(std::mem::replace(c, Term::Var(n.clone())));
                names.push(n);
            }
            i += 1;
        }
    });
}

/// A parallel let's binders, `+` where what follows uses one twice.
fn reusable(names: Vec<String>, counts: &HashMap<String, usize>) -> Vec<String> {
    names.into_iter().map(|n| if counts.get(&n).copied().unwrap_or(0) > 1 { format!("+{}", n) } else { n }).collect()
}

/// A term as a region: its movable self-calls, if two or more, run in
/// parallel ahead of it; then the regions inside it.
fn par_term(t: &mut Term, me: &str, counter: &mut usize) {
    let mut n = 0;
    visit_calls(t, me, &mut Vec::new(), &mut |_, ok| n += ok as usize);
    if n >= 2 {
        let (mut names, mut calls) = (Vec::new(), Vec::new());
        take_calls(t, me, counter, &|_| true, &mut names, &mut calls);
        let mut counts = HashMap::new();
        t.count_vars(&mut counts);
        let body = std::mem::replace(t, Term::unit());
        *t = Term::Par(reusable(names, &counts), calls, Box::new(body));
    }
    par_inside(t, me, counter);
}

/// The regions nested in a term: lambda bodies, the bodies of applied
/// lambdas (for calls that read their binders), the operands of `&&`/`||`,
/// and the arguments of self-calls.
fn par_inside(t: &mut Term, me: &str, counter: &mut usize) {
    match t {
        Term::Lam(_, b) => par_term(b, me, counter),
        Term::TmplTerm(_) => {}
        Term::And(a, b) | Term::Or(a, b) => {
            par_term(a, me, counter);
            par_term(b, me, counter);
        }
        Term::Call(g, args) if g == me => {
            for a in args.iter_mut() {
                par_term(a, me, counter);
            }
        }
        Term::App(g, args) if matches!(**g, Term::Lam(..)) => {
            for a in args.iter_mut() {
                par_inside(a, me, counter);
            }
            if let Term::Lam(_, b) = &mut **g {
                par_term(b, me, counter);
            }
        }
        _ => {
            for c in t.children_mut() {
                par_inside(c, me, counter);
            }
        }
    }
}

/// The terms of a pure block a parallel let may take calls from: each
/// let's value and the result, with its position (the result's is the
/// number of statements).
fn block_terms<'a>(stmts: &'a mut [Stmt], tail: &'a mut Term) -> Vec<(usize, &'a mut Term)> {
    let len = stmts.len();
    let mut out: Vec<(usize, &mut Term)> = stmts.iter_mut().enumerate().filter_map(|(j, s)| match s {
        Stmt::Let { value, .. } => Some((j, value)),
        _ => None,
    }).collect();
    out.push((len, tail));
    out
}

/// A body: in a block, the self-calls of its lets and tail run in
/// parallel at the point where the most of them have what they read
/// (after the last let each reads, before the first term that uses one);
/// then each term as a region.
fn par_body(b: &mut Body, me: &str, counter: &mut usize) {
    match b {
        Body::Match { arms, .. } => {
            for (_, a) in arms {
                par_body(a, me, counter);
            }
        }
        Body::Do { .. } => {}
        Body::Block { stmts, tail } => {
            // per movable call: the term it is in, and the last let it reads
            let len = stmts.len();
            let lets: Vec<Option<String>> = stmts.iter().map(|s| match s {
                Stmt::Let { name, .. } => Some(name.clone()),
                _ => None,
            }).collect();
            let mut found: Vec<(usize, usize)> = Vec::new();
            for (j, t) in block_terms(stmts, tail) {
                visit_calls(t, me, &mut Vec::new(), &mut |c, ok| {
                    if ok {
                        let mut fv = HashSet::new();
                        c.free_vars(&mut fv);
                        let after = lets[..j].iter().rposition(|n| n.as_ref().is_some_and(|n| fv.contains(n))).map_or(0, |i| i + 1);
                        found.push((j, after));
                    }
                });
            }
            let best = (0..=len).map(|p| (found.iter().filter(|&&(j, a)| a <= p && p <= j).count(), p)).max_by_key(|&(n, p)| (n, p));
            if let Some((n, p)) = best
                && n >= 2 {
                    let (mut names, mut calls) = (Vec::new(), Vec::new());
                    let mut k = 0;
                    for (j, t) in block_terms(stmts, tail) {
                        let mine: Vec<bool> = found[k..].iter().take_while(|&&(jj, _)| jj == j).map(|&(_, a)| a <= p && p <= j).collect();
                        k += mine.len();
                        take_calls(t, me, counter, &|i| mine[i], &mut names, &mut calls);
                    }
                    let mut counts = HashMap::new();
                    for t in stmts[p..].iter().flat_map(Stmt::values).chain([&*tail]) {
                        t.count_vars(&mut counts);
                    }
                    stmts.insert(p, Stmt::Par { names: reusable(names, &counts), calls });
                }
            for s in stmts.iter_mut() {
                for t in s.values_mut() {
                    par_term(t, me, counter);
                }
            }
            par_term(tail, me, counter);
        }
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

impl Param {
    /// A parameter, reusable once `mark_reusable` finds it used twice.
    pub fn new(name: impl Into<String>, ty: Ty) -> Param {
        Param { name: name.into(), reusable: false, ty }
    }
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
    /// `-A: Type` erased parameters, after those: types that need not be
    /// data (an eliminator's answer may be an `IO(..)`).
    pub erased_types: Vec<String>,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Body,
}

impl Def {
    /// A def with value parameters only.
    pub fn new(name: impl Into<String>, params: Vec<Param>, ret: Ty, body: Body) -> Def {
        Def { name: name.into(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], erased_types: vec![], params, ret, body }
    }

    /// Evaluate a pure def's independent self-calls in parallel (tree
    /// recursion: `size(l) + size(r)`); see `par_body`.
    pub fn parallelize(&mut self) {
        if self.name.starts_with("law:") || matches!(self.ret, Ty::Io(_) | Ty::Result(..)) {
            return;
        }
        let me = self.name.clone();
        let mut counter = 0;
        par_body(&mut self.body, &me, &mut counter);
    }

    fn write(&self, out: &mut String) {
        // a law: its Bend text is carried verbatim in the body
        if self.name.starts_with("law:") {
            if let Body::Block { tail: Term::Var(text), .. } = &self.body {
                out.push_str(text);
                out.push('\n');
            }
            return;
        }
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
        for e in &self.erased_types {
            sep(out);
            write!(out, "-{}: Type", e).unwrap();
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
}

/// An item placed after the items it refers to.
trait Node {
    fn key(&self) -> &str;
    /// The names it refers to, other than its own.
    fn refs(&self) -> BTreeSet<String>;
}

impl Node for TypeDef {
    fn key(&self) -> &str {
        &self.name
    }

    fn refs(&self) -> BTreeSet<String> {
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

impl Node for Def {
    fn key(&self) -> &str {
        &self.name
    }

    fn refs(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.body.def_refs(&mut out);
        out.remove(&self.name);
        out
    }
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub types: Vec<TypeDef>,
    pub defs: Vec<Def>,
}

impl Program {
    /// Render the program with types and defs in dependency order, after
    /// the part of the prelude it uses.
    pub fn render(&self) -> String {
        let mut body = String::new();
        for t in topo_order(&self.types) {
            t.write(&mut body);
        }
        for d in topo_order(&self.defs) {
            d.write(&mut body);
        }
        let prelude = crate::prune::prune_prelude(crate::lower::PRELUDE, &body);
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

/// Topological order (an item after the items it refers to). A cycle
/// keeps source order: between types it is a recursive type, between
/// defs Bend's checker reports it.
fn topo_order<T: Node>(items: &[T]) -> Vec<&T> {
    let index: HashMap<&str, usize> = items.iter().enumerate().map(|(i, t)| (t.key(), i)).collect();
    let mut done = vec![false; items.len()];
    let mut visiting = Vec::new();
    let mut out = Vec::new();
    fn visit<'a, T: Node>(i: usize, items: &'a [T], index: &HashMap<&str, usize>, done: &mut [bool], visiting: &mut Vec<usize>, out: &mut Vec<&'a T>) {
        if done[i] || visiting.contains(&i) {
            return;
        }
        visiting.push(i);
        for r in items[i].refs() {
            if let Some(&j) = index.get(r.as_str()) {
                visit(j, items, index, done, visiting, out);
            }
        }
        visiting.pop();
        done[i] = true;
        out.push(&items[i]);
    }
    for i in 0..items.len() {
        visit(i, items, &index, &mut done, &mut visiting, &mut out);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_a_small_def() {
        let body = Body::Block {
            stmts: vec![Stmt::Let { name: "y".into(), reusable: true, ty: None, value: Term::var("x") }],
            tail: Term::op(Term::var("y"), "*", Term::var("y"), Ty::U32),
        };
        let d = Def::new("f.sq", vec![Param::new("x", Ty::U32)], Ty::U32, body);
        let mut s = String::new();
        d.write(&mut s);
        assert_eq!(s, "def f.sq(x: U32) -> U32:\n  +y = x\n  (y * y : U32)\n\n");
    }

    #[test]
    fn orders_helpers_before_callers() {
        let mk = |name: &str, calls: &[&str]| Def::new(name, vec![], Ty::U32, Body::term(Term::List(calls.iter().map(|c| Term::call(c, vec![])).collect())));
        let defs = vec![mk("a", &["b", "a"]), mk("b", &["c"]), mk("c", &[])];
        let names: Vec<&str> = topo_order(&defs).iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["c", "b", "a"]);
    }
}
