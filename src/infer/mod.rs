// src/bend/infer/mod.rs
// Type inference for the compiler: Fire AST -> typed AST (tast.rs).
//
// Split across files by concern: this one holds the inferencer state,
// scopes and name resolution, deferred constraints, and the program driver
// (including the effect fixpoint); `stmts.rs` handles statements, defs and
// classes; `exprs.rs` handles expressions and patterns.

mod exprs;
mod stmts;

use std::collections::{HashMap, HashSet};

use crate::sigs::{self, PAIR_REC};
use crate::tast::*;
use crate::types::*;
use crate::ast;

#[derive(Debug, Clone)]
pub struct Diag {
    pub line: usize,
    pub message: String,
}

impl std::fmt::Display for Diag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.line > 0 {
            write!(f, "line {}: {}", self.line, self.message)
        } else {
            write!(f, "{}", self.message)
        }
    }
}

/// What a name means in scope.
#[derive(Debug, Clone)]
pub(super) enum Binding {
    Local { ty: Type, mutable: bool },
    /// A named function (nested def, named lambda, or method).
    Func { def: DefId },
    /// A class: its constructor is callable and its name is a type.
    Class(RecId),
    /// A member of the record being built or the method receiver: the
    /// field path from `self` (through `__parent` fields).
    Member { path: Vec<(RecId, usize)>, ty: Type, mutable: bool },
    /// A member of a builtin module bound by destructuring (`{sqrt} = $math`).
    ModuleMember(String, String),
    /// A type alias (`Level = 'a' | 'b'`, `Maybe = int | nothing`).
    TypeAlias(Type),
}

#[derive(Debug, Default)]
pub(super) struct Scope {
    pub names: HashMap<String, Binding>,
    /// Defs declared in this block, by name, so a later def can be
    /// inferred on demand when an earlier statement references it.
    pub hoisted: HashMap<String, stmts::HoistEntry>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum HoistState {
    NotYet,
    InProgress,
    Done,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum FrameKind {
    Main,
    Plain,
    Ctor(RecId),
    Method(RecId),
}

/// One function being inferred.
#[derive(Debug)]
pub(super) struct Frame {
    pub def: DefId,
    pub kind: FrameKind,
    pub scopes: Vec<Scope>,
    pub captures: Vec<(String, Type)>,
    pub loop_depth: usize,
    /// Types of `return` expressions, joined into the return type.
    /// Types of the `return` values (and whether the value is an int
    /// literal, which may still become a float).
    pub returns: Vec<(Type, bool)>,
    pub ret: Type,
    pub mutates_member: bool,
}

/// A constraint waiting for a type variable to be resolved.
#[derive(Debug, Clone)]
pub(super) enum Pending {
    /// `recv.name(args) : ret`
    Method { recv: Type, name: String, args: Vec<Type>, ret: Type, line: usize },
    /// `recv.name : ty`
    Field { recv: Type, name: String, ty: Type, line: usize },
    /// An overloaded global: `name(args) : ret`
    Global { name: String, args: Vec<Type>, ret: Type, line: usize },
    /// `ty` must support the operator.
    Arith { ty: Type, op: BinOp, line: usize },
    /// `recv[idx] : ret`; `lit` is the index when it is an int literal
    /// (a pair record allows `[0]`/`[1]`).
    Index { recv: Type, idx: Type, ret: Type, lit: Option<i64>, line: usize },
    /// `for x in recv` yields `elem`.
    Iter { recv: Type, elem: Type, line: usize },
    /// `lhs or rhs : ret` where `lhs` is not yet known to be a maybe.
    Or { lhs: Type, rhs: Type, ret: Type, line: usize },
    /// `recv[idx] = value` on a receiver not yet known to be a list or map.
    IndexSet { recv: Type, idx: Type, value: Type, line: usize },
    /// `recv[idx]` read for a compound assignment: the element itself (a
    /// missing dictionary key aborts).
    IndexCur { recv: Type, idx: Type, ret: Type, line: usize },
    /// `ty` is used as a number (unary minus).
    Numeric { ty: Type, line: usize },
}

impl Pending {
    /// Every type a pending constraint mentions (for pinning).
    pub(super) fn types(&self) -> Vec<Type> {
        match self {
            Pending::Method { recv, args, ret, .. } => {
                let mut v = vec![recv.clone(), ret.clone()];
                v.extend(args.iter().cloned());
                v
            }
            Pending::Field { recv, ty, .. } => vec![recv.clone(), ty.clone()],
            Pending::Global { args, ret, .. } => {
                let mut v = args.clone();
                v.push(ret.clone());
                v
            }
            Pending::Arith { ty, .. } | Pending::Numeric { ty, .. } => vec![ty.clone()],
            Pending::Index { recv, idx, ret, .. } | Pending::IndexCur { recv, idx, ret, .. } => vec![recv.clone(), idx.clone(), ret.clone()],
            Pending::Iter { recv, elem, .. } => vec![recv.clone(), elem.clone()],
            Pending::Or { lhs, rhs, ret, .. } => vec![lhs.clone(), rhs.clone(), ret.clone()],
            Pending::IndexSet { recv, idx, value, .. } => vec![recv.clone(), idx.clone(), value.clone()],
        }
    }
}

pub struct Infer {
    pub store: TypeStore,
    pub records: Vec<RecordDef>,
    pub defs: Vec<Option<TDef>>,
    pub(super) frames: Vec<Frame>,
    pub(super) pending: Vec<Pending>,
    pub diags: Vec<Diag>,
    pub(super) literal_shapes: HashMap<Vec<String>, RecId>,
    pub(super) lambda_counter: usize,
    /// Def ids whose inference is in progress (self-recursion is fine,
    /// anything else through them is mutual recursion).
    pub(super) in_progress: Vec<DefId>,
    /// Bindings introduced by the last binding pattern inferred.
    pub(super) last_pattern_bindings: Vec<(String, Type)>,
    /// Template copies of defs by (def, argument types).
    pub(super) copies: HashMap<(DefId, String), DefId>,
    /// Copies whose argument types were not known when requested, per
    /// function being inferred (innermost last).
    pub(super) lazy_copies: Vec<Vec<crate::infer::stmts::LazyCopy>>,
    /// Function types of not yet inferred lazy copies.
    pub(super) placeholders: HashMap<DefId, Type>,
}

pub const BUILTIN_GLOBALS: &[&str] = &[
    "print", "debug", "len", "type", "range", "sum", "min", "max", "abs", "round", "sorted", "reversed",
    "error", "assert", "any", "int", "float", "number", "str", "bool", "list", "object", "fn", "nothing",
];

pub fn infer_program(program: &ast::Program) -> Result<TProgram, Vec<Diag>> {
    let mut inf = Infer {
        store: TypeStore::new(),
        records: Vec::new(),
        defs: Vec::new(),
        frames: Vec::new(),
        pending: Vec::new(),
        diags: Vec::new(),
        literal_shapes: HashMap::new(),
        lambda_counter: 0,
        in_progress: Vec::new(),
        last_pattern_bindings: Vec::new(),
        copies: HashMap::new(),
        lazy_copies: Vec::new(),
        placeholders: HashMap::new(),
    };
    // record 0: the builtin pair shape {key, value}
    let pair = inf.new_record("Pair", RecordKind::Literal, vec!["key".into(), "value".into()], vec![true, true], vec![false, false]);
    debug_assert_eq!(pair, PAIR_REC);
    inf.literal_shapes.insert(vec!["key".into(), "value".into()], PAIR_REC);

    let main = inf.infer_main(&program.statements);
    inf.resolve_pending(true);
    if !inf.diags.is_empty() {
        return Err(inf.diags);
    }
    let mut defs: Vec<TDef> = inf.defs.into_iter().map(|d| d.expect("every def inferred")).collect();
    compute_mutations(&mut defs, &inf.store, &inf.records);
    compute_effects(&mut defs, &inf.store, &inf.records);
    Ok(TProgram { records: inf.records, defs, main, store: inf.store })
}

impl Infer {
    // -- diagnostics ---------------------------------------------------------

    pub(super) fn error(&mut self, line: usize, message: impl Into<String>) {
        let message = message.into();
        if !self.diags.iter().any(|d| d.line == line && d.message == message) {
            self.diags.push(Diag { line, message });
        }
    }

    pub(super) fn type_name(&self, t: &Type) -> String {
        let names = |id: RecId| self.records[id].name.clone();
        format!("{}", TypeDisplay { store: &self.store, ty: t, names: &names })
    }

    /// Unify with a diagnostic on failure.
    pub(super) fn unify(&mut self, a: &Type, b: &Type, line: usize, what: &str) -> bool {
        match self.store.unify(a, b) {
            Ok(()) => true,
            Err(e) => {
                let msg = format!("{}: expected {}, found {}", what, self.type_name(&e.left), self.type_name(&e.right));
                self.error(line, msg);
                false
            }
        }
    }

    // -- records -------------------------------------------------------------

    pub(super) fn new_record(&mut self, name: &str, kind: RecordKind, fields: Vec<String>, public: Vec<bool>, mutable: Vec<bool>) -> RecId {
        let field_vars = fields.iter().map(|_| self.store.fresh()).collect();
        let fields = fields
            .into_iter()
            .zip(public)
            .zip(mutable)
            .map(|((name, public), mutable)| Field { name, public, mutable })
            .collect();
        self.records.push(RecordDef { name: name.to_string(), kind, field_vars, fields });
        self.records.len() - 1
    }

    /// The record shape for an object literal with these field names (in
    /// source order), and the type of one instance with fresh field types.
    pub(super) fn literal_shape(&mut self, names: &[String]) -> (RecId, Vec<Type>) {
        let key: Vec<String> = names.to_vec();
        let id = match self.literal_shapes.get(&key) {
            Some(id) => *id,
            None => {
                let name = format!("Rec_{}", names.join("_"));
                let n = names.len();
                let id = self.new_record(&name, RecordKind::Literal, key.clone(), vec![true; n], vec![false; n]);
                self.literal_shapes.insert(key, id);
                id
            }
        };
        let args = names.iter().map(|_| self.store.fresh()).collect();
        (id, args)
    }

    // -- scopes and frames ---------------------------------------------------

    pub(super) fn frame(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("inside a frame")
    }

    pub(super) fn push_scope(&mut self) {
        self.frame().scopes.push(Scope::default());
    }

    pub(super) fn pop_scope(&mut self) {
        self.frame().scopes.pop();
    }

    pub(super) fn declare(&mut self, name: &str, binding: Binding) {
        self.frame().scopes.last_mut().unwrap().names.insert(name.to_string(), binding);
    }

    /// Look a name up through the current frame's scopes, then the
    /// enclosing frames (recording captures), then the class members when
    /// inside a constructor or method, then builtins.
    pub(super) fn lookup(&mut self, name: &str, line: usize) -> Option<Binding> {
        // current frame
        let n = self.frames.len();
        if let Some(b) = self.lookup_in_frame(n - 1, name) {
            return Some(b);
        }
        // members of the class this frame belongs to
        if let Some(b) = self.lookup_member(name) {
            return Some(b);
        }
        // enclosing frames: capture
        let mut found: Option<(usize, Binding)> = None;
        for i in (0..n - 1).rev() {
            if let Some(b) = self.lookup_in_frame(i, name) {
                found = Some((i, b));
                break;
            }
        }
        if let Some((i, b)) = found {
            match &b {
                Binding::Local { ty, .. } => {
                    let ty = ty.clone();
                    for j in i + 1..n {
                        if !self.frames[j].captures.iter().any(|(c, _)| c == name) {
                            self.frames[j].captures.push((name.to_string(), ty.clone()));
                        }
                    }
                    return Some(Binding::Local { ty, mutable: false });
                }
                Binding::Func { def } => {
                    // a nested function with an environment is captured as a value
                    let def = *def;
                    if self.def_has_env(def) {
                        let ty = self.def_value_type(def, line);
                        for j in i + 1..n {
                            if !self.frames[j].captures.iter().any(|(c, _)| c == name) {
                                self.frames[j].captures.push((name.to_string(), ty.clone()));
                            }
                        }
                    }
                    return Some(b);
                }
                Binding::Member { .. } => {
                    // a method's lambda reading a member of the enclosing method's receiver
                    if let Binding::Member { ty, .. } = &b {
                        let ty = ty.clone();
                        for j in i + 1..n {
                            if !self.frames[j].captures.iter().any(|(c, _)| c == name) {
                                self.frames[j].captures.push((name.to_string(), ty.clone()));
                            }
                        }
                        return Some(Binding::Local { ty, mutable: false });
                    }
                    unreachable!()
                }
                _ => return Some(b),
            }
        }
        if let Some(b) = self.lookup_outer_member(name) {
            return Some(b);
        }
        None
    }

    pub(super) fn lookup_in_frame(&mut self, frame: usize, name: &str) -> Option<Binding> {
        let nscopes = self.frames[frame].scopes.len();
        for s in (0..nscopes).rev() {
            if let Some(b) = self.frames[frame].scopes[s].names.get(name) {
                return Some(b.clone());
            }
            // a def declared later in this block: infer it now
            let state = self.frames[frame].scopes[s].hoisted.get(name).map(|e| e.state);
            if let Some(HoistState::NotYet) = state {
                // infer it in its own frame: the frames of the functions
                // nested inside it are set aside meanwhile
                let inner: Vec<Frame> = self.frames.drain(frame + 1..).collect();
                self.frames[frame].scopes[s].hoisted.get_mut(name).unwrap().state = HoistState::InProgress;
                self.infer_hoisted(frame, s, name);
                self.frames[frame].scopes[s].hoisted.get_mut(name).unwrap().state = HoistState::Done;
                self.frames.extend(inner);
                if let Some(b) = self.frames[frame].scopes[s].names.get(name) {
                    return Some(b.clone());
                }
            }
        }
        None
    }

    /// Members of the class of the current frame (constructor or method).
    pub(super) fn lookup_member(&mut self, name: &str) -> Option<Binding> {
        let rec = match self.frames.last().unwrap().kind {
            FrameKind::Ctor(r) | FrameKind::Method(r) => r,
            _ => return None,
        };
        self.member_path(rec, name, Vec::new())
    }

    /// Members of the class of the nearest enclosing constructor/method
    /// frame (a lambda inside a method reading a member): captured by value.
    fn lookup_outer_member(&mut self, name: &str) -> Option<Binding> {
        let n = self.frames.len();
        for i in (0..n - 1).rev() {
            let rec = match self.frames[i].kind {
                FrameKind::Ctor(r) | FrameKind::Method(r) => r,
                _ => continue,
            };
            if let Some(Binding::Member { ty, .. }) = self.member_path(rec, name, Vec::new()) {
                for j in i + 1..n {
                    if !self.frames[j].captures.iter().any(|(c, _)| c == name) {
                        self.frames[j].captures.push((name.to_string(), ty.clone()));
                    }
                }
                return Some(Binding::Local { ty, mutable: false });
            }
            return None;
        }
        None
    }

    pub(super) fn member_path(&self, rec: RecId, name: &str, mut path: Vec<(RecId, usize)>) -> Option<Binding> {
        let r = &self.records[rec];
        if let Some(idx) = r.field_index(name) {
            path.push((rec, idx));
            return Some(Binding::Member { path, ty: r.field_vars[idx].clone(), mutable: r.fields[idx].mutable });
        }
        if let Some(pidx) = r.parent_field() {
            let parent_ty = self.store.shallow(&r.field_vars[pidx]);
            if let Type::Record(prec, _) = parent_ty {
                path.push((rec, pidx));
                return self.member_path(prec, name, path);
            }
        }
        None
    }

    pub(super) fn def_has_env(&self, def: DefId) -> bool {
        match &self.defs[def] {
            Some(d) => !d.captures.is_empty(),
            None => self.frames.iter().any(|f| f.def == def && !f.captures.is_empty()),
        }
    }

    /// The type of a def used as a value (instantiated).
    pub(super) fn def_value_type(&mut self, def: DefId, line: usize) -> Type {
        if let Some(d) = &self.defs[def] {
            let scheme = d.scheme.clone();
            let (t, _) = self.store.instantiate(&scheme);
            return t;
        }
        // a template copy not inferred yet: its call-site type
        if let Some(t) = self.placeholders.get(&def) {
            return t.clone();
        }
        // in progress: monomorphic placeholder stored in its frame
        for f in &self.frames {
            if f.def == def {
                if let Some(Binding::Local { ty, .. }) = f.scopes[0].names.get("__self_type") {
                    return ty.clone();
                }
            }
        }
        self.error(line, "internal: unknown def type");
        self.store.fresh()
    }

    // -- deferred constraints ------------------------------------------------

    pub(super) fn defer(&mut self, p: Pending) {
        self.pending.push(p);
    }

    /// Try to discharge deferred constraints; with `final_pass` the
    /// remaining ones are defaulted or reported.
    pub(super) fn resolve_pending(&mut self, final_pass: bool) {
        loop {
            let mut progress = false;
            let items = std::mem::take(&mut self.pending);
            let mut keep = Vec::new();
            for p in items {
                if self.try_resolve(&p, false) {
                    progress = true;
                } else {
                    keep.push(p);
                }
            }
            self.pending = keep;
            if !progress {
                break;
            }
        }
        if final_pass {
            let items = std::mem::take(&mut self.pending);
            for p in items {
                self.try_resolve(&p, true);
            }
        }
    }

    fn try_resolve(&mut self, p: &Pending, final_pass: bool) -> bool {
        match p {
            Pending::Method { recv, name, args, ret, line } => {
                let r = self.store.shallow(recv);
                if let Type::Var(_) = r {
                    // a method name that belongs to one builtin type only
                    if let Some(t) = sigs::unique_receiver(name) {
                        self.unify(&r, &t, *line, "receiver");
                        return self.try_resolve(p, false);
                    }
                    if final_pass {
                        // a unique record shape with a method of that name?
                        let cands: Vec<RecId> = (0..self.records.len()).filter(|&i| self.records[i].method(name).is_some()).collect();
                        if cands.len() == 1 {
                            let rec = cands[0];
                            let args_t: Vec<Type> = self.records[rec].field_vars.iter().map(|_| self.store.fresh()).collect();
                            self.unify(&r, &Type::Record(rec, args_t), *line, "receiver");
                            return self.try_resolve(p, false);
                        }
                        self.error(*line, format!("cannot infer the type of the receiver of .{}(); add a type annotation", name));
                    }
                    return false;
                }
                self.resolve_method(&r, name, args, ret, *line);
                true
            }
            Pending::Field { recv, name, ty, line } => {
                let r = self.store.shallow(recv);
                if let Type::Var(_) = r {
                    if final_pass {
                        let cands: Vec<RecId> = (0..self.records.len()).filter(|&i| self.records[i].field_index(name).is_some()).collect();
                        if cands.len() == 1 {
                            let rec = cands[0];
                            let args_t: Vec<Type> = self.records[rec].field_vars.iter().map(|_| self.store.fresh()).collect();
                            self.unify(&r, &Type::Record(rec, args_t), *line, "receiver");
                            return self.try_resolve(p, false);
                        }
                        self.error(*line, format!("cannot infer the type of the object whose member .{} is read; add a type annotation", name));
                    }
                    return false;
                }
                self.resolve_field(&r, name, ty, *line);
                true
            }
            Pending::Global { name, args, ret, line } => {
                let first = self.store.shallow(&args[0]);
                if let Type::Var(_) = first {
                    if final_pass {
                        match name.as_str() {
                            "sum" | "min" | "max" | "abs" | "round" => {
                                // numbers default to int
                                let t = if name == "sum" || name == "min" || name == "max" {
                                    if args.len() == 1 { Type::list(Type::Int) } else { Type::Int }
                                } else {
                                    Type::Int
                                };
                                self.unify(&first, &t, *line, name);
                                return self.try_resolve(p, false);
                            }
                            "print" | "debug" | "str" | "len" | "reversed" | "sorted" => {
                                self.error(*line, format!("cannot infer the type of the argument of {}(); add a type annotation", name));
                            }
                            _ => {}
                        }
                    }
                    return false;
                }
                self.resolve_global(name, args, ret, *line);
                true
            }
            Pending::Arith { ty, op, line } => {
                let t = self.store.shallow(ty);
                match t {
                    Type::Var(_) => {
                        if final_pass {
                            self.unify(&t, &Type::Int, *line, "arithmetic");
                        }
                        final_pass
                    }
                    Type::Int | Type::Float => true,
                    Type::Str if *op == BinOp::Add => true,
                    Type::List(_) if *op == BinOp::Add => true,
                    Type::Record(_, _) if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div) => true,
                    _ => {
                        let n = self.type_name(&t);
                        self.error(*line, format!("operator {:?} is not defined on {}", op, n));
                        true
                    }
                }
            }
            Pending::Numeric { ty, line } => {
                let t = self.store.shallow(ty);
                match t {
                    Type::Var(_) => {
                        if final_pass {
                            self.unify(&t, &Type::Int, *line, "number");
                        }
                        final_pass
                    }
                    Type::Int | Type::Float => true,
                    _ => {
                        let n = self.type_name(&t);
                        self.error(*line, format!("expected a number, found {}", n));
                        true
                    }
                }
            }
            Pending::Index { recv, idx, ret, lit, line } => {
                let r = self.store.shallow(recv);
                match r {
                    Type::Record(sigs::PAIR_REC, args) if matches!(lit, Some(0) | Some(1)) => {
                        let i = lit.unwrap() as usize;
                        self.unify(ret, &args[i], *line, "pair index");
                        true
                    }
                    Type::Var(_) => {
                        if final_pass {
                            self.error(*line, "cannot infer the type of the indexed value; add a type annotation");
                        }
                        false
                    }
                    Type::List(e) => {
                        let i = self.store.shallow(idx);
                        if matches!(i, Type::Range | Type::Stream(_)) {
                            self.unify(ret, &Type::list((*e).clone()), *line, "slice");
                        } else {
                            self.unify(idx, &Type::Int, *line, "index");
                            self.unify(ret, &e, *line, "index");
                        }
                        true
                    }
                    Type::Str => {
                        let i = self.store.shallow(idx);
                        if !matches!(i, Type::Range | Type::Stream(_)) {
                            self.unify(idx, &Type::Int, *line, "index");
                        }
                        self.unify(ret, &Type::Str, *line, "index");
                        true
                    }
                    Type::Map(v) => {
                        self.unify(idx, &Type::Str, *line, "key");
                        self.unify(ret, &Type::maybe((*v).clone()), *line, "lookup");
                        true
                    }
                    Type::Range => {
                        let i = self.store.shallow(idx);
                        if matches!(i, Type::Range | Type::Stream(_)) {
                            self.unify(ret, &Type::Range, *line, "slice");
                        } else {
                            self.unify(idx, &Type::Int, *line, "index");
                            self.unify(ret, &Type::Int, *line, "index");
                        }
                        true
                    }
                    Type::Stream(e) => {
                        let i = self.store.shallow(idx);
                        if let Type::Range = i {
                            self.unify(ret, &Type::list((*e).clone()), *line, "slice");
                        } else if let Type::Stream(_) = i {
                            self.unify(ret, &Type::stream((*e).clone()), *line, "slice");
                        } else {
                            self.unify(idx, &Type::Int, *line, "index");
                            self.unify(ret, &e, *line, "index");
                        }
                        true
                    }
                    Type::Record(rec, _) => {
                        // obj["key"] on a record: only string literal keys are static; treat as maybe
                        self.error(*line, format!("[] indexing on a record ({}) is not supported; use .member", self.records[rec].name));
                        true
                    }
                    other => {
                        let n = self.type_name(&other);
                        self.error(*line, format!("cannot index a value of type {}", n));
                        true
                    }
                }
            }
            Pending::Or { lhs, rhs, ret, line } => {
                let l = self.store.shallow(lhs);
                match l {
                    Type::Var(_) => {
                        if final_pass {
                            // plain: both sides have the same type
                            self.unify(lhs, rhs, *line, "or");
                            self.unify(ret, lhs, *line, "or");
                            return true;
                        }
                        false
                    }
                    Type::Maybe(inner) => {
                        let r = self.store.shallow(rhs);
                        if matches!(r, Type::Maybe(_) | Type::Unit) {
                            self.unify(ret, lhs, *line, "or");
                        } else {
                            // `x or default`: the present value
                            self.unify(&inner, rhs, *line, "or");
                            self.unify(ret, &inner, *line, "or");
                        }
                        true
                    }
                    _ => {
                        self.unify(lhs, rhs, *line, "or");
                        self.unify(ret, lhs, *line, "or");
                        true
                    }
                }
            }
            Pending::IndexSet { recv, idx, value, line } => {
                let r = self.store.shallow(recv);
                match r {
                    Type::Var(_) => {
                        if final_pass {
                            self.error(*line, "cannot infer the type of the assigned container; add a type annotation");
                        }
                        false
                    }
                    Type::List(e) => {
                        self.unify(idx, &Type::Int, *line, "index");
                        self.unify(&e, value, *line, "assignment");
                        true
                    }
                    Type::Map(v) => {
                        self.unify(idx, &Type::Str, *line, "key");
                        self.unify(&v, value, *line, "assignment");
                        true
                    }
                    other => {
                        let n = self.type_name(&other);
                        self.error(*line, format!("cannot assign into a value of type {}", n));
                        true
                    }
                }
            }
            Pending::IndexCur { recv, idx, ret, line } => {
                let r = self.store.shallow(recv);
                match r {
                    Type::Var(_) => {
                        if final_pass {
                            self.error(*line, "cannot infer the type of the indexed value; add a type annotation");
                        }
                        false
                    }
                    Type::List(e) => {
                        self.unify(idx, &Type::Int, *line, "index");
                        self.unify(ret, &e, *line, "index");
                        true
                    }
                    Type::Map(v) => {
                        self.unify(idx, &Type::Str, *line, "key");
                        self.unify(ret, &v, *line, "lookup");
                        true
                    }
                    other => {
                        let n = self.type_name(&other);
                        self.error(*line, format!("cannot index a value of type {}", n));
                        true
                    }
                }
            }
            Pending::Iter { recv, elem, line } => {
                let r = self.store.shallow(recv);
                match r {
                    Type::Var(_) => {
                        if final_pass {
                            self.error(*line, "cannot infer the type of the iterated value; add a type annotation");
                        }
                        false
                    }
                    Type::List(e) | Type::Stream(e) => {
                        self.unify(elem, &e, *line, "loop variable");
                        true
                    }
                    Type::Range => {
                        self.unify(elem, &Type::Int, *line, "loop variable");
                        true
                    }
                    Type::Str => {
                        self.unify(elem, &Type::Str, *line, "loop variable");
                        true
                    }
                    Type::Map(v) => {
                        self.unify(elem, &Type::Record(PAIR_REC, vec![Type::Str, (*v).clone()]), *line, "loop variable");
                        true
                    }
                    other => {
                        let n = self.type_name(&other);
                        self.error(*line, format!("cannot iterate over a value of type {}", n));
                        true
                    }
                }
            }
        }
    }

    fn resolve_method(&mut self, recv: &Type, name: &str, args: &[Type], ret: &Type, line: usize) {
        if let Type::Record(rec, rargs) = recv {
            let rec = *rec;
            // a class method?
            if let Some(def) = self.find_method(rec, name) {
                let ty = self.def_value_type(def, line);
                // method type: (self, params...) -> ret ; unify self with the receiver
                if let Type::Fn(params, r, _) = self.store.shallow(&ty) {
                    if params.is_empty() {
                        self.error(line, "internal: method without self");
                        return;
                    }
                    if params.len() - 1 != args.len() {
                        self.error(line, format!("{}() takes {} argument(s), {} given", name, params.len() - 1, args.len()));
                        return;
                    }
                    let self_ty = params[0].clone();
                    // the receiver may be a descendant: unify through its parent chain
                    let recv_for_self = self.receiver_as(rec, rargs, &self_ty);
                    self.unify(&self_ty, &recv_for_self, line, "receiver");
                    for (p, a) in params[1..].iter().zip(args.iter()) {
                        self.unify(p, a, line, &format!("argument of {}()", name));
                    }
                    self.unify(ret, &r, line, &format!("result of {}()", name));
                }
                return;
            }
            // a function-typed field called as a method
            if let Some(idx) = self.records[rec].field_index(name) {
                let fty = rargs[idx].clone();
                let f = self.store.fresh_fn(args.to_vec(), ret.clone());
                self.unify(&fty, &f, line, &format!("call of member {}", name));
                return;
            }
            let builtin = ["keys", "values", "entries", "has"];
            if builtin.contains(&name) {
                match name {
                    "keys" => {
                        self.unify(ret, &Type::list(Type::Str), line, name);
                    }
                    "has" => {
                        if let Some(a) = args.first() {
                            self.unify(a, &Type::Str, line, name);
                        }
                        self.unify(ret, &Type::Bool, line, name);
                    }
                    _ => {
                        // values/entries need one field type
                        let v = self.store.fresh();
                        let public: Vec<Type> = self.records[rec].fields.iter().zip(rargs.iter()).filter(|(f, _)| f.public).map(|(_, t)| t.clone()).collect();
                        for t in &public {
                            self.unify(&v, t, line, &format!(".{}() needs members of one type", name));
                        }
                        let r = if name == "values" { Type::list(v) } else { Type::list(Type::Record(PAIR_REC, vec![Type::Str, v])) };
                        self.unify(ret, &r, line, name);
                    }
                }
                return;
            }
            let rname = self.records[rec].name.clone();
            self.error(line, format!("{} has no method {}()", rname, name));
            return;
        }
        match sigs::method_sig(&mut self.store, recv, name, args.len()) {
            Some((params, r)) => {
                if params.len() != args.len() {
                    self.error(line, format!(".{}() takes {} argument(s), {} given", name, params.len(), args.len()));
                    return;
                }
                for (p, a) in params.iter().zip(args.iter()) {
                    self.unify(p, a, line, &format!("argument of .{}()", name));
                }
                self.unify(ret, &r, line, &format!("result of .{}()", name));
            }
            None => {
                let n = self.type_name(recv);
                self.error(line, format!("no method .{}() on {}", name, n));
            }
        }
    }

    /// Find a method on a record or through its parent chain.
    pub(super) fn find_method(&self, rec: RecId, name: &str) -> Option<DefId> {
        if let Some(d) = self.records[rec].method(name) {
            return Some(d);
        }
        if let Some(pidx) = self.records[rec].parent_field() {
            if let Type::Record(prec, _) = self.store.shallow(&self.records[rec].field_vars[pidx]) {
                return self.find_method(prec, name);
            }
        }
        None
    }

    /// The receiver value's type as seen by a method of `self_ty`'s record:
    /// the receiver itself, or the parent field it inherits the method from.
    fn receiver_as(&mut self, rec: RecId, rargs: &[Type], self_ty: &Type) -> Type {
        let target = match self.store.shallow(self_ty) {
            Type::Record(r, _) => r,
            _ => return Type::Record(rec, rargs.to_vec()),
        };
        let mut cur = Type::Record(rec, rargs.to_vec());
        let mut cur_rec = rec;
        let mut cur_args = rargs.to_vec();
        loop {
            if cur_rec == target {
                return cur;
            }
            match self.records[cur_rec].parent_field() {
                Some(pidx) => {
                    let pty = self.store.shallow(&cur_args[pidx]);
                    match pty {
                        Type::Record(pr, pa) => {
                            cur = Type::Record(pr, pa.clone());
                            cur_rec = pr;
                            cur_args = pa;
                        }
                        _ => return cur,
                    }
                }
                None => return cur,
            }
        }
    }

    fn resolve_field(&mut self, recv: &Type, name: &str, ty: &Type, line: usize) {
        match recv {
            Type::Record(rec, rargs) => {
                let rec = *rec;
                if let Some(Binding::Member { path, .. }) = self.member_path(rec, name, Vec::new()) {
                    // field type: walk the path through the receiver's args
                    let mut args = rargs.clone();
                    let mut fty = None;
                    for (i, (_, idx)) in path.iter().enumerate() {
                        let t = args[*idx].clone();
                        if i + 1 == path.len() {
                            fty = Some(t);
                        } else if let Type::Record(_, a) = self.store.shallow(&t) {
                            args = a;
                        } else {
                            break;
                        }
                    }
                    if let Some(t) = fty {
                        self.unify(ty, &t, line, &format!("member {}", name));
                        return;
                    }
                }
                if let Some(def) = self.find_method(rec, name) {
                    // a method referenced without a call: a bound function value
                    let t = self.def_value_type(def, line);
                    if let Type::Fn(params, r, _) = self.store.shallow(&t) {
                        let f = self.store.fresh_fn(params[1..].to_vec(), (*r).clone());
                        self.unify(ty, &f, line, &format!("member {}", name));
                        return;
                    }
                }
                let rname = self.records[rec].name.clone();
                self.error(line, format!("{} has no public member {}", rname, name));
            }
            Type::Result(e, a) => match name {
                "ok" => {
                    self.unify(ty, a, line, "ok");
                }
                "err" => {
                    self.unify(ty, e, line, "err");
                }
                _ => self.error(line, format!("a result has no member {}", name)),
            },
            other => {
                let n = self.type_name(other);
                self.error(line, format!("no member .{} on a value of type {}", name, n));
            }
        }
    }

    fn resolve_global(&mut self, name: &str, args: &[Type], ret: &Type, line: usize) {
        let first = self.store.shallow(&args[0]);
        match name {
            "len" => {
                match first {
                    Type::List(_) | Type::Str | Type::Range | Type::Map(_) => {}
                    other => {
                        let n = self.type_name(&other);
                        self.error(line, format!("len() takes a list, string, or range, not {}", n));
                    }
                }
                self.unify(ret, &Type::Int, line, "len");
            }
            "sum" | "min" | "max" => {
                if args.len() == 1 {
                    match first {
                        Type::List(e) => {
                            self.unify(ret, &e, line, name);
                        }
                        Type::Range => {
                            self.unify(ret, &Type::Int, line, name);
                        }
                        other => {
                            let n = self.type_name(&other);
                            self.error(line, format!("{}() takes a list, not {}", name, n));
                        }
                    }
                } else {
                    for a in args {
                        self.unify(a, &first, line, name);
                    }
                    self.unify(ret, &first, line, name);
                }
            }
            "abs" => {
                self.unify(ret, &first, line, name);
            }
            "round" => {
                if args.len() == 1 {
                    let r = if let Type::Float = first { Type::Int } else { first.clone() };
                    self.unify(ret, &r, line, name);
                } else {
                    self.unify(&args[1], &Type::Int, line, name);
                    self.unify(ret, &first, line, name);
                }
            }
            "sorted" | "reversed" => match first {
                Type::List(_) => {
                    if name == "sorted" && args.len() == 2 {
                        if let Type::List(e) = &first {
                            let k = self.store.fresh();
                            let f = self.store.fresh_fn(vec![(**e).clone()], k);
                            self.unify(&args[1], &f, line, "sort key");
                        }
                    }
                    self.unify(ret, &first, line, name);
                }
                Type::Range => {
                    self.unify(ret, &Type::list(Type::Int), line, name);
                }
                other => {
                    let n = self.type_name(&other);
                    self.error(line, format!("{}() takes a list, not {}", name, n));
                }
            },
            "print" | "debug" => {
                // returns its single argument, or nothing
                if args.len() == 1 {
                    self.unify(ret, &first, line, name);
                } else {
                    self.unify(ret, &Type::Unit, line, name);
                }
            }
            "str" => {
                self.unify(ret, &Type::Str, line, name);
            }
            "int" => {
                self.unify(ret, &Type::Int, line, name);
            }
            "float" => {
                self.unify(ret, &Type::Float, line, name);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

/// A method that calls a mutating method on one of its members (its
/// parent object, a member holding an object, or a sibling by bare name)
/// mutates its receiver too. Fixpoint over the methods.
fn compute_mutations(defs: &mut [TDef], store: &TypeStore, records: &[RecordDef]) {
    loop {
        let mut changed = false;
        for i in 0..defs.len() {
            let rec = match &defs[i].kind {
                DefKind::Method { rec, mutates: false } => *rec,
                _ => continue,
            };
            let member_names: Vec<String> = records[rec].fields.iter().map(|f| f.name.clone()).collect();
            let mut found = false;
            {
                let mut check = |e: &TExpr| {
                    if found {
                        return;
                    }
                    if let TExprKind::MethodCall { recv, name, .. } = &e.kind {
                        if !member_rooted(recv, &member_names) {
                            return;
                        }
                        if let Type::Record(r, _) = store.resolve(&recv.ty) {
                            if let Some(d) = find_method_static(records, store, r, name) {
                                if matches!(defs[d].kind, DefKind::Method { mutates: true, .. }) {
                                    found = true;
                                }
                            }
                        }
                    }
                };
                walk_block(&defs[i].body, &mut check);
            }
            if found {
                defs[i].kind = DefKind::Method { rec, mutates: true };
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Is the expression a path from the receiver's members?
fn member_rooted(e: &TExpr, members: &[String]) -> bool {
    match &e.kind {
        TExprKind::SelfValue(_) => true,
        TExprKind::Local(n) => members.iter().any(|m| m == n),
        TExprKind::Field(inner, _, _) | TExprKind::Member(inner, _) => member_rooted(inner, members),
        _ => false,
    }
}

/// Fixpoint over the call graph: each def's effect is the join of the
/// effects its body can perform.
fn compute_effects(defs: &mut [TDef], store: &TypeStore, records: &[RecordDef]) {
    let mut effects: Vec<Effect> = vec![Effect::Pure; defs.len()];
    loop {
        let mut changed = false;
        for i in 0..defs.len() {
            let e = block_effect(&defs[i].body, &effects, store, records);
            if e > effects[i] {
                effects[i] = e;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (d, e) in defs.iter_mut().zip(effects) {
        d.effect = e;
    }
}

fn block_effect(b: &TBlock, effects: &[Effect], store: &TypeStore, records: &[RecordDef]) -> Effect {
    let mut e = Effect::Pure;
    for s in &b.stmts {
        e = e.join(stmt_effect(s, effects, store, records));
    }
    e
}

fn stmt_effect(s: &TStmt, effects: &[Effect], store: &TypeStore, records: &[RecordDef]) -> Effect {
    let ex = |x: &TExpr| expr_effect(x, effects, store, records);
    let bl = |b: &TBlock| block_effect(b, effects, store, records);
    match &s.kind {
        TStmtKind::Let { value, .. } | TStmtKind::Assign { value, .. } | TStmtKind::Expr(value) => ex(value),
        TStmtKind::Return(Some(v)) => ex(v),
        TStmtKind::Return(None) | TStmtKind::Break | TStmtKind::Continue | TStmtKind::Bind { .. } => Effect::Pure,
        TStmtKind::If { cond, then, elifs, else_ } => {
            let mut e = ex(cond).join(bl(then));
            for (c, b) in elifs {
                e = e.join(ex(c)).join(bl(b));
            }
            if let Some(b) = else_ {
                e = e.join(bl(b));
            }
            e
        }
        TStmtKind::Match { subject, arms } => {
            let mut e = ex(subject);
            for a in arms {
                if let Some(g) = &a.guard {
                    e = e.join(ex(g));
                }
                e = e.join(ex(&a.body));
            }
            // a value no arm matches aborts
            if !crate::tast::arms_exhaustive(arms) {
                e = e.join(Effect::Abort);
            }
            e
        }
        TStmtKind::While { cond, body } => ex(cond).join(bl(body)),
        TStmtKind::For { iterables, body, .. } => {
            let mut e = bl(body);
            for i in iterables {
                e = e.join(ex(i));
            }
            e
        }
    }
}

/// The effect of calling a value of function type `t`: the join over the
/// defs in its closure set.
pub fn closure_effect(t: &Type, effects: &[Effect], store: &TypeStore) -> Effect {
    let mut s = store.clone();
    match s.shallow(t) {
        Type::Fn(_, _, c) => {
            let set = s.clos_set(c);
            let mut e = Effect::Pure;
            for id in set {
                if id < effects.len() {
                    e = e.join(effects[id]);
                }
            }
            e
        }
        _ => Effect::Pure,
    }
}

fn expr_effect(x: &TExpr, effects: &[Effect], store: &TypeStore, records: &[RecordDef]) -> Effect {
    let ex = |x: &TExpr| expr_effect(x, effects, store, records);
    let bl = |b: &TBlock| block_effect(b, effects, store, records);
    match &x.kind {
        TExprKind::Local(_) | TExprKind::Lit(_) | TExprKind::EmptyMap | TExprKind::Lambda(_) | TExprKind::DefRef(_) | TExprKind::SelfValue(_) => Effect::Pure,
        TExprKind::List(items) | TExprKind::MakeRecord(_, items) => items.iter().map(ex).fold(Effect::Pure, Effect::join),
        TExprKind::Field(o, _, _) | TExprKind::Member(o, _) => ex(o),
        TExprKind::SetField(o, _, _, v) => ex(o).join(ex(v)),
        TExprKind::Call(def, args) => args.iter().map(ex).fold(effects[*def], Effect::join),
        TExprKind::CallValue(f, args) => {
            let mut e = ex(f).join(closure_effect(&f.ty, effects, store));
            for a in args {
                e = e.join(ex(a));
            }
            e
        }
        TExprKind::MethodCall { recv, name, args } => {
            let mut e = ex(recv);
            for a in args {
                e = e.join(ex(a));
            }
            let rt = store.shallow(&recv.ty);
            match rt {
                Type::Record(rec, rargs) => {
                    if let Some(def) = find_method_static(records, store, rec, name) {
                        e = e.join(effects[def]);
                    } else if let Some(idx) = records[rec].field_index(name) {
                        e = e.join(closure_effect(&rargs[idx], effects, store));
                    }
                }
                _ => {
                    // builtin methods: function arguments contribute; some abort
                    for a in args {
                        if let Type::Fn(_, _, _) = store.shallow(&a.ty) {
                            e = e.join(closure_effect(&a.ty, effects, store));
                        }
                    }
                    if matches!(name.as_str(), "to_int" | "to_float" | "pop" | "sum" | "min" | "max") {
                        if !(matches!(rt, Type::List(_)) && name == "sum") {
                            e = e.join(Effect::Abort);
                        }
                    }
                }
            }
            e
        }
        TExprKind::Builtin(name, args) => {
            let mut e = args.iter().map(ex).fold(Effect::Pure, Effect::join);
            for a in args {
                if let Type::Fn(_, _, _) = store.shallow(&a.ty) {
                    e = e.join(closure_effect(&a.ty, effects, store));
                }
            }
            // `pair[0]` / `pair[1]` is a field read, which cannot fail
            let pair_field = name == "index"
                && args.len() == 2
                && matches!(store.shallow(&args[0].ty), Type::Record(sigs::PAIR_REC, _))
                && matches!(args[1].kind, TExprKind::Lit(Lit::Int(0 | 1)));
            let list_recv = args.first().is_some_and(|a| matches!(store.shallow(&a.ty), Type::List(_)));
            match name.as_str() {
                "print" | "debug" | "io.read_file" | "io.write_file" | "time.now" => e.join(Effect::Io),
                "index" if pair_field => e,
                "index_set" if !list_recv => e,
                "error" | "assert" | "index" | "index_cur" | "index_set" | "list_set" | "map_get_or" | "unwrap_ok" | "int" | "min" | "max" => e.join(Effect::Abort),
                _ => e,
            }
        }
        TExprKind::If { cond, then, else_ } => ex(cond).join(ex(then)).join(ex(else_)),
        TExprKind::Match { subject, arms } => {
            let mut e = ex(subject);
            for a in arms {
                if let Some(g) = &a.guard {
                    e = e.join(ex(g));
                }
                e = e.join(ex(&a.body));
            }
            if !crate::tast::arms_exhaustive(arms) {
                e = e.join(Effect::Abort);
            }
            e
        }
        TExprKind::Block(b) => bl(b),
        TExprKind::And(a, b) | TExprKind::Or(a, b) | TExprKind::BinOp(_, a, b) => ex(a).join(ex(b)),
        TExprKind::Not(a) | TExprKind::Neg(a) | TExprKind::MakeOk(a) | TExprKind::MakeErr(a) | TExprKind::MakeSome(a) => ex(a),
        TExprKind::Abort(a) => ex(a).join(Effect::Abort),
        TExprKind::Pipe { left, func } => ex(left).join(ex(func)).join(closure_effect(&func.ty, effects, store)),
        TExprKind::Stage { input, func, .. } => ex(input).join(ex(func)).join(closure_effect(&func.ty, effects, store)),
        TExprKind::Handle { left, handler, is_func } => {
            let mut e = ex(left).join(ex(handler));
            if *is_func {
                e = e.join(closure_effect(&handler.ty, effects, store));
            }
            e
        }
        TExprKind::Range { start, end } => {
            let mut e = ex(start);
            if let Some(en) = end {
                e = e.join(ex(en));
            }
            e
        }
        TExprKind::RangeList(a, b) => ex(a).join(ex(b)),
        TExprKind::Comprehension { iterables, filter, body, .. } => {
            let mut e = ex(body);
            for i in iterables {
                e = e.join(ex(i));
            }
            if let Some(f) = filter {
                e = e.join(ex(f));
            }
            e
        }
        TExprKind::FString(parts) => parts
            .iter()
            .map(|p| match p {
                FPart::Text(_) => Effect::Pure,
                FPart::Expr(x, _) => ex(x),
            })
            .fold(Effect::Pure, Effect::join),
    }
}

pub fn expr_effect_pub(x: &TExpr, effects: &[Effect], store: &TypeStore, records: &[RecordDef]) -> Effect {
    expr_effect(x, effects, store, records)
}

pub fn find_method_static(records: &[RecordDef], store: &TypeStore, rec: RecId, name: &str) -> Option<DefId> {
    if let Some(d) = records[rec].method(name) {
        return Some(d);
    }
    if let Some(pidx) = records[rec].parent_field() {
        if let Type::Record(prec, _) = store.shallow(&records[rec].field_vars[pidx]) {
            return find_method_static(records, store, prec, name);
        }
    }
    None
}

/// Free identifiers of a Fire expression / block (syntactic, before
/// resolution). Used to decide which constructor-scope bindings a method
/// references and to build the hoisting graph.
pub(super) fn free_names_block(stmts: &[ast::Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        free_names_stmt(&s.node, out);
    }
}

fn free_names_stmt(s: &ast::Statement, out: &mut HashSet<String>) {
    use ast::Statement::*;
    match s {
        Documentation(_) | Comment(_) | Break | Continue => {}
        Declaration { value, .. } => free_names_expr(value, out),
        Assignment { targets, value } => {
            for (p, _) in targets {
                free_names_pattern_targets(p, out);
            }
            free_names_expr(value, out);
        }
        Return(Some(e)) => free_names_expr(e, out),
        Return(None) => {}
        While { condition, body } => {
            free_names_expr(condition, out);
            free_names_block(body, out);
        }
        For { iterables, body, .. } => {
            for i in iterables {
                free_names_expr(i, out);
            }
            free_names_block(body, out);
        }
        If { condition, body, elif_branches, else_body } => {
            free_names_expr(condition, out);
            free_names_block(body, out);
            for (c, b) in elif_branches {
                free_names_expr(c, out);
                free_names_block(b, out);
            }
            if let Some(b) = else_body {
                free_names_block(b, out);
            }
        }
        Match { subject, arms } => {
            free_names_expr(subject, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    free_names_expr(g, out);
                }
                free_names_expr(&a.body, out);
            }
        }
        Def { params, body, .. } => {
            for p in params {
                if let Some(d) = &p.default {
                    free_names_expr(d, out);
                }
            }
            free_names_block(body, out);
        }
        Expression(e) => free_names_expr(e, out),
    }
}

fn free_names_pattern_targets(p: &ast::Pattern, out: &mut HashSet<String>) {
    match p {
        ast::Pattern::Identifier(n) => {
            out.insert(n.clone());
        }
        ast::Pattern::Member { object, .. } | ast::Pattern::Index { object, .. } | ast::Pattern::SpreadInto { object } => {
            free_names_expr(object, out)
        }
        ast::Pattern::List(items) => {
            for i in items {
                free_names_pattern_targets(i, out);
            }
        }
        ast::Pattern::Object(fields) => {
            for (_, p) in fields {
                free_names_pattern_targets(p, out);
            }
        }
        _ => {}
    }
}

pub(super) fn free_names_expr(e: &ast::Expression, out: &mut HashSet<String>) {
    use ast::Expression::*;
    match e {
        Identifier(n) => {
            out.insert(n.clone());
        }
        List(items) => {
            for i in items {
                free_names_expr(i, out);
            }
        }
        Object(entries) => {
            for en in entries {
                match en {
                    ast::ObjectEntry::KeyValue { value, .. } => free_names_expr(value, out),
                    ast::ObjectEntry::Shorthand(n) => {
                        out.insert(n.clone());
                    }
                    ast::ObjectEntry::Spread => {}
                }
            }
        }
        BinaryOp { left, right, .. } => {
            free_names_expr(left, out);
            free_names_expr(right, out);
        }
        UnaryOp { operand, .. } => free_names_expr(operand, out),
        Lambda { params, body } => {
            for p in params {
                if let Some(d) = &p.default {
                    free_names_expr(d, out);
                }
            }
            free_names_expr(body, out);
        }
        Block(stmts) => free_names_block(stmts, out),
        Call { function, args, named_args } => {
            free_names_expr(function, out);
            for a in args {
                free_names_expr(a, out);
            }
            for (_, a) in named_args {
                free_names_expr(a, out);
            }
        }
        MemberAccess { object, .. } | SpreadMember { object } => free_names_expr(object, out),
        Index { object, index } => {
            free_names_expr(object, out);
            free_names_expr(index, out);
        }
        IfExpr { condition, then_branch, elif_branches, else_branch } => {
            free_names_expr(condition, out);
            free_names_expr(then_branch, out);
            for (c, b) in elif_branches {
                free_names_expr(c, out);
                free_names_expr(b, out);
            }
            if let Some(b) = else_branch {
                free_names_expr(b, out);
            }
        }
        Comprehension { clauses, body } => {
            for c in clauses {
                match c {
                    ast::CompClause::For { iterables, .. } => {
                        for i in iterables {
                            free_names_expr(i, out);
                        }
                    }
                    ast::CompClause::While { condition } => free_names_expr(condition, out),
                }
            }
            free_names_expr(body, out);
        }
        TypeCheck { expression, type_expr } => {
            free_names_expr(expression, out);
            free_names_expr(type_expr, out);
        }
        Range { start, end } => {
            if let Some(s) = start {
                free_names_expr(s, out);
            }
            if let Some(e) = end {
                free_names_expr(e, out);
            }
        }
        Await(x) | Async(x) => free_names_expr(x, out),
        Pipeline { left, right, .. } => {
            free_names_expr(left, out);
            free_names_expr(right, out);
        }
        FString(parts) => {
            for p in parts {
                if let ast::FStringPart::Expression(x, _) = p {
                    free_names_expr(x, out);
                }
            }
        }
        _ => {}
    }
}
