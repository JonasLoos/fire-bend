// src/core.rs
// Core: the explicitly typed, fully resolved intermediate representation
// between the checker and the lowering.
//
// The checker (check/) produces it from the AST: every expression carries a
// type (possibly with variables that the store resolves), every name is
// resolved to a local, a def, a constructor or a builtin, and Fire's sugar
// is gone: pipelines, `$`, implicit self, keyword arguments, defaults,
// compound assignment, destructuring, mutating methods (functional updates
// of the receiver). What a body needs from a type it does not know is a
// constraint (types::Constraint), referred to here by id (`Dict`).
//
// The lowering (lower/) reads only this. It never re-infers anything.

use crate::types::{ClosId, ConstraintId, Scheme, TVar, Type, TypeId, TypeStore};

pub type DefId = usize;

/// The effects a def may perform. Divergence is not an effect: a def that
/// may not terminate must be declared `unsafe`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Effect {
    /// May abort with a message: `error`, `assert`, `xs[i]`, a failing
    /// `{ok} = ...`, a non-exhaustive match.
    pub abort: bool,
    /// Prints or uses `$io`.
    pub io: bool,
}

impl Effect {
    pub const PURE: Effect = Effect { abort: false, io: false };
    pub const ABORT: Effect = Effect { abort: true, io: false };
    pub const IO: Effect = Effect { abort: false, io: true };
    pub fn join(self, other: Effect) -> Effect {
        Effect { abort: self.abort || other.abort, io: self.io || other.io }
    }
    pub fn is_pure(self) -> bool {
        !self.abort && !self.io
    }
}

impl std::fmt::Display for Effect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.abort, self.io) {
            (false, false) => write!(f, "pure"),
            (true, false) => write!(f, "abort"),
            (false, true) => write!(f, "io"),
            (true, true) => write!(f, "io, abort"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Nothing,
}

#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: String,
    pub ty: Type,
    /// Shown by `print` and compared by `==` (data members of a class; every
    /// field of a declared type or record).
    pub public: bool,
}

#[derive(Debug, Clone)]
pub struct Ctor {
    pub name: String,
    pub fields: Vec<FieldDef>,
}

#[derive(Debug, Clone)]
pub enum DataKind {
    /// `Maybe`, `Result`, `Pair`, `Range`.
    Builtin,
    /// A `type` declaration.
    Declared,
    /// A class: `def` with `public` members. One constructor.
    Class {
        ctor: DefId,
        methods: Vec<(String, DefId)>,
        /// The hidden field holding the adopted parent object.
        parent: Option<usize>,
        /// Field indices in the order `print` shows them.
        show_order: Vec<usize>,
    },
    /// The shape of a record literal, nominal by its (sorted) field names;
    /// it shows its fields in the order the first literal wrote them.
    Record { show_order: Vec<usize> },
}

#[derive(Debug, Clone)]
pub struct DataType {
    pub name: String,
    /// Type parameters, in order; the type's arguments instantiate them.
    pub params: Vec<TVar>,
    pub ctors: Vec<Ctor>,
    pub kind: DataKind,
    pub line: usize,
}

impl DataType {
    pub fn ctor_index(&self, name: &str) -> Option<usize> {
        self.ctors.iter().position(|c| c.name == name)
    }
    /// The field index of a name in constructor 0 (records and classes).
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.ctors.first().and_then(|c| c.fields.iter().position(|f| f.name == name))
    }
    pub fn method(&self, name: &str) -> Option<DefId> {
        match &self.kind {
            DataKind::Class { methods, .. } => methods.iter().find(|(n, _)| n == name).map(|(_, d)| *d),
            _ => None,
        }
    }
    pub fn parent_field(&self) -> Option<usize> {
        match &self.kind {
            DataKind::Class { parent, .. } => *parent,
            _ => None,
        }
    }
    pub fn show_order(&self) -> Vec<usize> {
        match &self.kind {
            DataKind::Class { show_order, .. } | DataKind::Record { show_order } if !show_order.is_empty() => show_order.clone(),
            _ => (0..self.ctors.first().map(|c| c.fields.len()).unwrap_or(0)).collect(),
        }
    }
    /// A type whose constructors all carry no fields (bools of user types):
    /// laws over it are proven by case split.
    pub fn is_finite(&self) -> bool {
        !self.ctors.is_empty() && self.ctors.iter().all(|c| c.fields.is_empty())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DefKind {
    /// A plain named function (top-level or nested).
    Plain,
    /// A lambda; `name` is synthetic.
    Lambda,
    /// The constructor of a class.
    Ctor(TypeId),
    /// A method of a class. A mutating method answers the rebuilt receiver;
    /// one that also answers a value answers `Pair<self, value>`.
    Method { rec: TypeId, mutates: bool, returns_value: bool },
    /// The program's top-level statements.
    Main,
    /// The frame a law is checked in; never emitted.
    Law,
}

/// How a def's self-calls get smaller, as the descent analysis found it and
/// the lowering emits it.
#[derive(Debug, Clone, PartialEq)]
pub enum Descent {
    /// No self-call.
    None,
    /// Lexicographic structural descent over these parameters: every
    /// self-call passes a prefix of them unchanged and the next one smaller
    /// (a piece bound by a match on it). Bend's rule, reading the
    /// parameters left to right.
    Structural(Vec<usize>),
    /// Recursion on an int parameter decreased by literals under a guard;
    /// the image counts a Nat fuel down.
    Fuel(usize),
    /// Declared `unsafe`: emitted `@unsafe`, not checked.
    Unsafe,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Def {
    pub id: DefId,
    /// The source name (or a synthetic one for lambdas and main).
    pub name: String,
    pub kind: DefKind,
    /// The top-level def this one belongs to (itself for top-level ones):
    /// the unit of generalization, whose type parameters it shares.
    pub unit: DefId,
    pub unsafe_: bool,
    pub params: Vec<Param>,
    /// Free variables of the body bound in enclosing functions, with their
    /// types: the closure environment.
    pub captures: Vec<(String, Type)>,
    /// The function's type (params -> ret), generalized, with its
    /// dictionaries.
    pub scheme: Scheme,
    pub ret: Type,
    pub body: Block,
    pub effect: Effect,
    /// The def itself or something it calls is `unsafe` (Bend's report).
    pub relies_on_unsafe: bool,
    pub descent: Descent,
    /// The lambda-site id of this def when used as a value.
    pub closure_id: ClosId,
    pub line: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Let { name: String, value: Expr },
    /// Reassignment of a `var` (or the rebinding a mutation causes).
    Assign { name: String, value: Expr },
    Expr(Expr),
    Return(Expr),
    Break,
    Continue,
    If { cond: Expr, then: Block, else_: Block },
    Match { subject: Expr, arms: Vec<Arm> },
    /// One pattern per iterable; several iterables run in lockstep.
    For { patterns: Vec<Pat>, iters: Vec<Iter>, body: Block },
    /// Only inside an `unsafe` def.
    While { cond: Expr, body: Block },
    /// Binds `name` to a function value of `def` with its environment
    /// captured at this point (a nested def or a named lambda).
    Bind { name: String, def: DefId },
}

/// What a `for` loop runs over. Every form is finite except a counter,
/// which only appears alongside a finite one.
#[derive(Debug, Clone)]
pub enum Iter {
    /// A list, range, string or dictionary; the constraint says which and
    /// what the items are.
    Items(Expr, ConstraintId),
    /// `a..`: counts from `a`.
    Counter(Expr),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Var(String),
    Lit(Lit),
    List(Vec<Expr>),
    EmptyMap,
    /// Build a constructor of a data type from field values in order.
    Con(TypeId, usize, Vec<Expr>),
    /// Read a field of constructor 0 (records, classes, pairs).
    Field(Box<Expr>, TypeId, usize),
    /// The record with one field replaced.
    SetField(Box<Expr>, TypeId, usize, Box<Expr>),
    /// Call of a known def: type arguments for its scheme's variables, the
    /// constraints standing in for its dictionaries, and the arguments
    /// (defaults already filled).
    Call { def: DefId, targs: Vec<Type>, dicts: Vec<ConstraintId>, args: Vec<Expr> },
    /// Call of a function value.
    CallClosure(Box<Expr>, Vec<Expr>),
    /// What a constraint provides, applied to arguments: a method, a
    /// field, an ordering, a rendering, ...
    Dict { id: ConstraintId, args: Vec<Expr> },
    /// A lambda site; the closure captures its environment here.
    Lambda(DefId),
    /// A named def used as a value, with its instantiation.
    DefRef { def: DefId, targs: Vec<Type>, dicts: Vec<ConstraintId> },
    /// A builtin with a fixed signature (`print`, `error`, `$math.sqrt`, ...).
    Builtin(String, Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Arm>),
    Block(Block),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    /// A runtime abort with a message.
    Abort(Box<Expr>),
    /// Formatted string: text or (expression, format spec); the
    /// expressions are already rendered to `str`.
    FString(Vec<FPart>),
    /// The receiver rebuilt from the member locals, inside a method.
    SelfValue(TypeId),
}

#[derive(Debug, Clone)]
pub enum FPart {
    Text(String),
    Expr(Expr, Option<String>),
}

#[derive(Debug, Clone)]
pub struct Arm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Bind(String),
    Wild,
    Lit(Lit),
    /// A constructor with one sub-pattern per field.
    Con(TypeId, usize, Vec<Pat>),
    /// Element patterns and an optional rest binder.
    List(Vec<Pat>, Option<Option<String>>),
}

impl Pat {
    pub fn binders(&self, out: &mut Vec<String>) {
        match self {
            Pat::Bind(n) => out.push(n.clone()),
            Pat::Wild | Pat::Lit(_) => {}
            Pat::Con(_, _, ps) => {
                for p in ps {
                    p.binders(out);
                }
            }
            Pat::List(items, rest) => {
                for i in items {
                    i.binders(out);
                }
                if let Some(Some(r)) = rest {
                    out.push(r.clone());
                }
            }
        }
    }
}

/// What a law claims.
#[derive(Debug, Clone)]
pub enum Claim {
    /// `lhs == rhs` at the type.
    Equation(Expr, Expr, Type),
    /// A boolean expression that holds.
    Holds(Expr),
}

/// How the compiler proves a law, if it can.
#[derive(Debug, Clone, PartialEq)]
pub enum Proof {
    /// No variables: both sides normalize to the same term.
    Closed,
    /// Every variable ranges over a finite type: case split.
    Finite,
    /// Left to a Bend proof.
    Open,
}

#[derive(Debug, Clone)]
pub struct Law {
    pub name: String,
    pub vars: Vec<(String, Type)>,
    pub hyps: Vec<Expr>,
    pub claim: Claim,
    pub proof: Proof,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub types: Vec<DataType>,
    pub defs: Vec<Def>,
    pub laws: Vec<Law>,
    pub main: DefId,
    pub store: TypeStore,
}

impl Program {
    pub fn type_name(&self, id: TypeId) -> String {
        self.types[id].name.clone()
    }
}

/// A pattern that matches every value of its type: a name, `_`, or the
/// only constructor of its type (a pair, a record, a class) over such
/// patterns.
pub fn pat_total(p: &Pat, types: &[DataType]) -> bool {
    match p {
        Pat::Bind(_) | Pat::Wild => true,
        Pat::Con(id, _, ps) => types[*id].ctors.len() == 1 && ps.iter().all(|q| pat_total(q, types)),
        Pat::List(items, Some(_)) => items.is_empty(),
        _ => false,
    }
}

/// Whether the arms cover every value of the subject's type.
pub fn arms_exhaustive(arms: &[Arm], types: &[DataType]) -> bool {
    let total: Vec<&Pat> = arms.iter().filter(|a| a.guard.is_none()).map(|a| &a.pat).collect();
    pats_exhaustive(&total, types)
}

/// Whether the patterns together cover every value of their type.
fn pats_exhaustive(total: &[&Pat], types: &[DataType]) -> bool {
    if total.iter().any(|p| pat_total(p, types)) {
        return true;
    }
    // every constructor of one data type: one with total fields, or, for a
    // constructor of one field, patterns that cover that field
    // (`nothing`, `Leaf`, `Node(..)` on a `Tree | nothing`)
    if let Some(Pat::Con(id, _, _)) = total.first() {
        let dt = &types[*id];
        return (0..dt.ctors.len()).all(|ci| {
            let rows: Vec<&Vec<Pat>> = total.iter().filter_map(|p| match p {
                Pat::Con(i, c, ps) if i == id && *c == ci => Some(ps),
                _ => None,
            }).collect();
            rows.iter().any(|ps| ps.iter().all(|q| pat_total(q, types)))
                || (dt.ctors[ci].fields.len() == 1 && !rows.is_empty() && {
                    let firsts: Vec<&Pat> = rows.iter().map(|ps| &ps[0]).collect();
                    pats_exhaustive(&firsts, types)
                })
        });
    }
    let t = total.iter().any(|p| matches!(p, Pat::Lit(Lit::Bool(true))));
    let f = total.iter().any(|p| matches!(p, Pat::Lit(Lit::Bool(false))));
    if t && f {
        return true;
    }
    // lists: a `[a, b, ...rest]` covers every length from its own up, and
    // exact shapes (`[]`, `[a]`) must cover each length below
    let items_total = |items: &Vec<Pat>| items.iter().all(|q| pat_total(q, types));
    let Some(open) = total.iter().filter_map(|p| match p {
        Pat::List(items, Some(_)) if items_total(items) => Some(items.len()),
        _ => None,
    }).min() else {
        return false;
    };
    (0..open).all(|n| total.iter().any(|p| matches!(p, Pat::List(items, None) if items.len() == n && items_total(items))))
}

/// Visit every expression in a block (statements first, then nested
/// expressions), calling `f` on each.
pub fn walk_block(b: &Block, f: &mut dyn FnMut(&Expr)) {
    for s in &b.stmts {
        walk_stmt(s, f);
    }
}

pub fn walk_stmt(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
    match &s.kind {
        StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) | StmtKind::Return(value) => walk_expr(value, f),
        StmtKind::Break | StmtKind::Continue | StmtKind::Bind { .. } => {}
        StmtKind::If { cond, then, else_ } => {
            walk_expr(cond, f);
            walk_block(then, f);
            walk_block(else_, f);
        }
        StmtKind::Match { subject, arms } => {
            walk_expr(subject, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    walk_expr(g, f);
                }
                walk_expr(&a.body, f);
            }
        }
        StmtKind::While { cond, body } => {
            walk_expr(cond, f);
            walk_block(body, f);
        }
        StmtKind::For { iters, body, .. } => {
            for it in iters {
                walk_iter(it, f);
            }
            walk_block(body, f);
        }
    }
}

pub fn walk_iter(it: &Iter, f: &mut dyn FnMut(&Expr)) {
    match it {
        Iter::Items(e, _) | Iter::Counter(e) => walk_expr(e, f),
    }
}

pub fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => {}
        ExprKind::List(items) | ExprKind::Con(_, _, items) | ExprKind::Builtin(_, items) => {
            for i in items {
                walk_expr(i, f);
            }
        }
        ExprKind::Call { args, .. } | ExprKind::Dict { args, .. } => {
            for i in args {
                walk_expr(i, f);
            }
        }
        ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => walk_expr(o, f),
        ExprKind::SetField(o, _, _, v) => {
            walk_expr(o, f);
            walk_expr(v, f);
        }
        ExprKind::CallClosure(g, args) => {
            walk_expr(g, f);
            for a in args {
                walk_expr(a, f);
            }
        }
        ExprKind::If(c, t, e) => {
            walk_expr(c, f);
            walk_expr(t, f);
            walk_expr(e, f);
        }
        ExprKind::Match(subject, arms) => {
            walk_expr(subject, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    walk_expr(g, f);
                }
                walk_expr(&a.body, f);
            }
        }
        ExprKind::Block(b) => walk_block(b, f),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            walk_expr(a, f);
            walk_expr(b, f);
        }
        ExprKind::FString(parts) => {
            for p in parts {
                if let FPart::Expr(x, _) = p {
                    walk_expr(x, f);
                }
            }
        }
    }
}
