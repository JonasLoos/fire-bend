// src/bend/tast.rs
// The typed, desugared AST the compiler lowers from.
//
// Inference (infer.rs) turns the Fire AST into this form: every expression
// carries a type (possibly containing type variables that resolve through
// the TypeStore), names are resolved to locals, defs, records, or builtins,
// and Fire's sugar (pipelines, `$`, implicit self, keyword arguments,
// compound assignment, destructuring) is expanded.

use crate::types::{ClosId, RecId, Scheme, Type};

pub type DefId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Effect {
    Pure,
    /// May abort with a message (`error`, failed assertion, bad index).
    Abort,
    /// Performs IO (`print`, `$io`).
    Io,
}

impl Effect {
    pub fn join(self, other: Effect) -> Effect {
        if other > self { other } else { self }
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
pub struct Field {
    pub name: String,
    pub public: bool,
    pub mutable: bool,
}

#[derive(Debug, Clone)]
pub enum RecordKind {
    /// A constructor-built object: its ctor def, its methods by name, the
    /// names the pre-scan classified as methods, and the hidden parent field.
    Class {
        ctor: DefId,
        methods: Vec<(String, DefId)>,
        method_names: Vec<String>,
        parent: Option<usize>,
        /// Field indices in the order the interpreter shows them: parameters,
        /// then body declarations in order, the parent (inherited members)
        /// where `self.{...} = parent` appears.
        show_order: Vec<usize>,
    },
    /// The shape of an object literal.
    Literal,
}

#[derive(Debug, Clone)]
pub struct RecordDef {
    pub name: String,
    pub kind: RecordKind,
    /// One type variable per field, in field order. The record's type
    /// arguments are the resolved values of these variables.
    pub field_vars: Vec<Type>,
    pub fields: Vec<Field>,
}

impl RecordDef {
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
    }
    pub fn method(&self, name: &str) -> Option<DefId> {
        match &self.kind {
            RecordKind::Class { methods, .. } => methods.iter().find(|(n, _)| n == name).map(|(_, d)| *d),
            RecordKind::Literal => None,
        }
    }
    pub fn parent_field(&self) -> Option<usize> {
        match &self.kind {
            RecordKind::Class { parent, .. } => *parent,
            RecordKind::Literal => None,
        }
    }

    /// Field indices in display order (declaration order for classes).
    pub fn show_order(&self) -> Vec<usize> {
        match &self.kind {
            RecordKind::Class { show_order, .. } if !show_order.is_empty() => show_order.clone(),
            _ => (0..self.fields.len()).collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum DefKind {
    /// A plain named function (top-level or nested).
    Plain,
    /// A lambda expression; `name` is synthetic.
    Lambda,
    /// The constructor of a class record.
    Ctor(RecId),
    /// A method of a class record. `mutates` is set after inference when
    /// the body assigns to a member.
    Method { rec: RecId, mutates: bool },
    /// The program's top-level statements.
    Main,
}

#[derive(Debug, Clone)]
pub struct TParam {
    pub name: String,
    pub ty: Type,
    pub default: Option<TExpr>,
}

#[derive(Debug, Clone)]
pub struct TemplateSrc {
    pub params: Vec<crate::ast::Param>,
    pub return_type: Option<crate::ast::Expression>,
    pub body: Vec<crate::ast::Stmt>,
    /// Frame and scope index of the declaration (the copy is inferred there).
    pub decl: (usize, usize),
}

#[derive(Debug, Clone)]
pub struct TDef {
    pub id: DefId,
    pub name: String,
    pub kind: DefKind,
    pub params: Vec<TParam>,
    /// Free variables of the body bound in enclosing function scopes, with
    /// their types: the closure environment.
    pub captures: Vec<(String, Type)>,
    /// The function's type (params -> ret), generalized.
    pub scheme: Scheme,
    pub ret: Type,
    pub body: TBlock,
    pub effect: Effect,
    /// Lambda sites reachable from this def's body (for effect analysis).
    pub closure_id: ClosId,
    /// Source line of the definition.
    pub line: usize,
    /// The source of a plain `def`, kept so that a call at other argument
    /// types can re-infer a copy (a def whose parameters are constrained
    /// is monomorphic; copies stand in for polymorphism).
    pub template: Option<Box<TemplateSrc>>,
    /// The def this one is a copy of.
    pub template_of: Option<DefId>,
}

#[derive(Debug, Clone, Default)]
pub struct TBlock {
    pub stmts: Vec<TStmt>,
}

#[derive(Debug, Clone)]
pub struct TStmt {
    pub kind: TStmtKind,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum TStmtKind {
    /// A new binding.
    Let { name: String, mutable: bool, value: TExpr },
    /// Reassignment of a `var` (compound ops already expanded).
    Assign { name: String, value: TExpr },
    Expr(TExpr),
    Return(Option<TExpr>),
    Break,
    Continue,
    If { cond: TExpr, then: TBlock, elifs: Vec<(TExpr, TBlock)>, else_: Option<TBlock> },
    Match { subject: TExpr, arms: Vec<TArm> },
    While { cond: TExpr, body: TBlock },
    For { pattern: TPattern, iterables: Vec<TExpr>, body: TBlock },
    /// Binds `name` to a function value of `def` with its environment
    /// captured at this point (a nested `def` or a named lambda).
    Bind { name: String, def: DefId },
}

#[derive(Debug, Clone)]
pub struct TExpr {
    pub kind: TExprKind,
    pub ty: Type,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum TExprKind {
    Local(String),
    Lit(Lit),
    List(Vec<TExpr>),
    EmptyMap,
    /// Build a record from field values in field order.
    MakeRecord(RecId, Vec<TExpr>),
    /// Read a field.
    Field(Box<TExpr>, RecId, usize),
    /// `obj.name` on a receiver whose record type is resolved later.
    Member(Box<TExpr>, String),
    /// Functional field update: the record with one field replaced.
    SetField(Box<TExpr>, RecId, usize, Box<TExpr>),
    /// Direct call of a known def (defaults already filled).
    Call(DefId, Vec<TExpr>),
    /// Call of a function value.
    CallValue(Box<TExpr>, Vec<TExpr>),
    /// `recv.name(args)`: a method on a class record, a builtin type, or a
    /// function-valued field. Resolved by the lowering from the receiver's
    /// type once inference has fixed it.
    MethodCall { recv: Box<TExpr>, name: String, args: Vec<TExpr> },
    /// A global builtin (`len`, `print`, `sum`, ...) or a module member,
    /// resolved by the lowering from the argument types.
    Builtin(String, Vec<TExpr>),
    /// A lambda site; the closure captures its environment here.
    Lambda(DefId),
    /// A named def used as a value.
    DefRef(DefId),
    If { cond: Box<TExpr>, then: Box<TExpr>, else_: Box<TExpr> },
    Match { subject: Box<TExpr>, arms: Vec<TArm> },
    Block(TBlock),
    /// Short-circuit `and` / `or`; both operands share the result type.
    And(Box<TExpr>, Box<TExpr>),
    Or(Box<TExpr>, Box<TExpr>),
    /// `not x`
    Not(Box<TExpr>),
    /// Arithmetic / comparison on two operands of the same type.
    BinOp(BinOp, Box<TExpr>, Box<TExpr>),
    Neg(Box<TExpr>),
    /// `{ok: v}` / `{err: e}` / a value lifted into `T | nothing`.
    MakeOk(Box<TExpr>),
    MakeErr(Box<TExpr>),
    MakeSome(Box<TExpr>),
    /// The pipeline family. `func` is a function-typed expression.
    Pipe { left: Box<TExpr>, func: Box<TExpr> },
    Stage { op: StageOp, input: Box<TExpr>, func: Box<TExpr> },
    /// `!> handler` (function) or `!> value`.
    Handle { left: Box<TExpr>, handler: Box<TExpr>, is_func: bool },
    /// `a..b` / `a..`
    Range { start: Box<TExpr>, end: Option<Box<TExpr>> },
    /// `for pattern in iterables do body` with an optional filter.
    Comprehension { pattern: TPattern, iterables: Vec<TExpr>, filter: Option<Box<TExpr>>, body: Box<TExpr> },
    /// Formatted string: parts are text or (expression, spec).
    FString(Vec<FPart>),
    /// The receiver itself inside a method (rebuilt from the member locals).
    SelfValue(RecId),
    /// A runtime abort with a message.
    Abort(Box<TExpr>),
    /// A closed range materialized as a list (`range(n)`, `a..b` in list
    /// position).
    RangeList(Box<TExpr>, Box<TExpr>),
}

#[derive(Debug, Clone)]
pub enum FPart {
    Text(String),
    Expr(TExpr, Option<String>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StageOp {
    Map,
    Filter,
}

impl BinOp {
    /// The Fire operator symbol of an arithmetic operator (a class may
    /// define a method of that name).
    pub fn symbol(&self) -> Option<&'static str> {
        Some(match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Pow => "**",
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    UShr,
}

impl BinOp {
    pub fn is_comparison(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
    /// `& | ^ << >>`: defined on ints only.
    pub fn is_bitwise(self) -> bool {
        matches!(self, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr | BinOp::UShr)
    }
}

#[derive(Debug, Clone)]
pub struct TArm {
    pub pattern: TPattern,
    pub guard: Option<TExpr>,
    pub body: TExpr,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum TPattern {
    Bind(String),
    Wild,
    Lit(Lit),
    /// Element patterns and an optional rest binder (`...rest` / `...`).
    List(Vec<TPattern>, Option<Option<String>>),
    /// Subset match on a record: (field index, pattern).
    Record(RecId, Vec<(usize, TPattern)>),
    Ok(Box<TPattern>),
    Err(Box<TPattern>),
    Some(Box<TPattern>),
    None,
}

impl TPattern {
    pub fn binders(&self, out: &mut Vec<String>) {
        match self {
            TPattern::Bind(n) => out.push(n.clone()),
            TPattern::List(items, rest) => {
                for i in items {
                    i.binders(out);
                }
                if let Some(Some(r)) = rest {
                    out.push(r.clone());
                }
            }
            TPattern::Record(_, fields) => {
                for (_, p) in fields {
                    p.binders(out);
                }
            }
            TPattern::Ok(p) | TPattern::Err(p) | TPattern::Some(p) => p.binders(out),
            _ => {}
        }
    }
}

#[derive(Debug, Clone)]
pub struct TProgram {
    pub records: Vec<RecordDef>,
    pub defs: Vec<TDef>,
    pub main: DefId,
    pub store: crate::types::TypeStore,
}

/// A pattern that matches every value of its type.
pub fn pattern_irrefutable(p: &TPattern) -> bool {
    match p {
        TPattern::Bind(_) | TPattern::Wild => true,
        TPattern::Record(_, fields) => fields.iter().all(|(_, p)| pattern_irrefutable(p)),
        _ => false,
    }
}

/// Whether the arms cover every value: a catch-all arm, both cases of a
/// maybe or a result, or both booleans (guards make an arm partial).
pub fn arms_exhaustive(arms: &[TArm]) -> bool {
    let total: Vec<&TPattern> = arms.iter().filter(|a| a.guard.is_none()).map(|a| &a.pattern).collect();
    if total.iter().any(|p| pattern_irrefutable(p)) {
        return true;
    }
    let none = total.iter().any(|p| matches!(p, TPattern::None));
    let some = total.iter().any(|p| matches!(p, TPattern::Some(inner) if pattern_irrefutable(inner)));
    if none && some {
        return true;
    }
    let ok = total.iter().any(|p| matches!(p, TPattern::Ok(inner) if pattern_irrefutable(inner)));
    let err = total.iter().any(|p| matches!(p, TPattern::Err(inner) if pattern_irrefutable(inner)));
    if ok && err {
        return true;
    }
    let t = total.iter().any(|p| matches!(p, TPattern::Lit(Lit::Bool(true))));
    let f = total.iter().any(|p| matches!(p, TPattern::Lit(Lit::Bool(false))));
    t && f
}

/// Visit every expression in a block (statements first, then nested
/// expressions), calling `f` on each.
pub fn walk_block(b: &TBlock, f: &mut dyn FnMut(&TExpr)) {
    for s in &b.stmts {
        walk_stmt(s, f);
    }
}

pub fn walk_stmt(s: &TStmt, f: &mut dyn FnMut(&TExpr)) {
    match &s.kind {
        TStmtKind::Let { value, .. } | TStmtKind::Assign { value, .. } | TStmtKind::Expr(value) => walk_expr(value, f),
        TStmtKind::Return(Some(v)) => walk_expr(v, f),
        TStmtKind::Return(None) | TStmtKind::Break | TStmtKind::Continue | TStmtKind::Bind { .. } => {}
        TStmtKind::If { cond, then, elifs, else_ } => {
            walk_expr(cond, f);
            walk_block(then, f);
            for (c, b) in elifs {
                walk_expr(c, f);
                walk_block(b, f);
            }
            if let Some(b) = else_ {
                walk_block(b, f);
            }
        }
        TStmtKind::Match { subject, arms } => {
            walk_expr(subject, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    walk_expr(g, f);
                }
                walk_expr(&a.body, f);
            }
        }
        TStmtKind::While { cond, body } => {
            walk_expr(cond, f);
            walk_block(body, f);
        }
        TStmtKind::For { iterables, body, .. } => {
            for it in iterables {
                walk_expr(it, f);
            }
            walk_block(body, f);
        }
    }
}

pub fn walk_expr(e: &TExpr, f: &mut dyn FnMut(&TExpr)) {
    f(e);
    match &e.kind {
        TExprKind::Local(_) | TExprKind::Lit(_) | TExprKind::EmptyMap | TExprKind::Lambda(_) | TExprKind::DefRef(_) | TExprKind::SelfValue(_) => {}
        TExprKind::List(items) | TExprKind::MakeRecord(_, items) | TExprKind::Builtin(_, items) | TExprKind::Call(_, items) => {
            for i in items {
                walk_expr(i, f);
            }
        }
        TExprKind::Field(o, _, _) | TExprKind::Member(o, _) | TExprKind::Not(o) | TExprKind::Neg(o) | TExprKind::MakeOk(o) | TExprKind::MakeErr(o) | TExprKind::MakeSome(o) | TExprKind::Abort(o) => walk_expr(o, f),
        TExprKind::SetField(o, _, _, v) => {
            walk_expr(o, f);
            walk_expr(v, f);
        }
        TExprKind::CallValue(g, args) => {
            walk_expr(g, f);
            for a in args {
                walk_expr(a, f);
            }
        }
        TExprKind::MethodCall { recv, args, .. } => {
            walk_expr(recv, f);
            for a in args {
                walk_expr(a, f);
            }
        }
        TExprKind::If { cond, then, else_ } => {
            walk_expr(cond, f);
            walk_expr(then, f);
            walk_expr(else_, f);
        }
        TExprKind::Match { subject, arms } => {
            walk_expr(subject, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    walk_expr(g, f);
                }
                walk_expr(&a.body, f);
            }
        }
        TExprKind::Block(b) => walk_block(b, f),
        TExprKind::And(a, b) | TExprKind::Or(a, b) | TExprKind::BinOp(_, a, b) | TExprKind::RangeList(a, b) => {
            walk_expr(a, f);
            walk_expr(b, f);
        }
        TExprKind::Pipe { left, func } => {
            walk_expr(left, f);
            walk_expr(func, f);
        }
        TExprKind::Stage { input, func, .. } => {
            walk_expr(input, f);
            walk_expr(func, f);
        }
        TExprKind::Handle { left, handler, .. } => {
            walk_expr(left, f);
            walk_expr(handler, f);
        }
        TExprKind::Range { start, end } => {
            walk_expr(start, f);
            if let Some(e) = end {
                walk_expr(e, f);
            }
        }
        TExprKind::Comprehension { iterables, filter, body, .. } => {
            for it in iterables {
                walk_expr(it, f);
            }
            if let Some(g) = filter {
                walk_expr(g, f);
            }
            walk_expr(body, f);
        }
        TExprKind::FString(parts) => {
            for p in parts {
                if let FPart::Expr(x, _) = p {
                    walk_expr(x, f);
                }
            }
        }
    }
}
