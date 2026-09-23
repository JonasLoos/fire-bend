// src/check/mod.rs
// The checker: Fire AST -> Core. Name resolution, Hindley-Milner inference
// with constraints, effect inference, the descent (termination) analysis,
// and every desugaring, so that the lowering only has to give Core a Bend
// shape.
//
// Split by concern: this file holds the checker state, scopes, the program
// driver and def hoisting; `annot.rs` reads type annotations; `solve.rs`
// solves constraints against known types (and holds the builtin method
// table); `expr.rs` and `stmt.rs` infer expressions and statements;
// `pattern.rs` handles patterns; `classes.rs` builds class types; `effects.rs`
// runs the effect fixpoint; `descent.rs` checks termination; `laws.rs`
// checks laws.

mod annot;
mod classes;
mod descent;
mod effects;
mod expr;
mod laws;
mod lost;
mod pattern;
mod solve;
mod stmt;

use std::collections::{HashMap, HashSet};

use crate::ast;
use crate::core::*;
use crate::types::*;
use crate::Diag;

/// What a name means in scope.
#[derive(Debug, Clone)]
pub(crate) enum Binding {
    Local { ty: Type, mutable: bool },
    /// A named function: a top-level def, a nested def, a named lambda, or
    /// a method (callable by bare name inside its class).
    Func(DefId),
    /// A class: its constructor is callable and its name is a type.
    Class(TypeId),
    /// A declared type's constructor.
    Ctor(TypeId, usize),
    /// A member of the object being built or of the method receiver: the
    /// local that holds it (the member itself, or the adopted parent object
    /// it lives in, reached through a field path), its type, and whether
    /// the member is mutable.
    Member { root: String, root_ty: Type, path: Vec<(TypeId, usize)>, ty: Type, mutable: bool },
    /// A member of a builtin module bound by destructuring (`{sqrt} = $math`).
    ModuleMember(String, String),
}

#[derive(Debug, Default)]
pub(crate) struct Scope {
    pub names: HashMap<String, Binding>,
    /// Defs declared in this block, by name, inferred on demand when an
    /// earlier statement references them.
    pub hoisted: HashMap<String, DefId>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum State {
    NotYet,
    InProgress,
    Done,
}

/// The source of a hoisted def, inferred when first needed.
#[derive(Debug, Clone)]
pub(crate) struct Source {
    pub params: Vec<ast::Param>,
    pub return_type: Option<ast::Expression>,
    pub body: Vec<ast::Stmt>,
    /// The frame index and scope depth where the def was declared.
    pub frame: usize,
    pub depth: usize,
}

/// A def while it is being checked.
#[derive(Debug, Clone)]
pub(crate) struct DefInfo {
    pub name: String,
    pub kind: DefKind,
    pub unsafe_: bool,
    pub state: State,
    pub source: Option<Source>,
    /// Monomorphic function type while in progress (recursive calls use it).
    pub mono: Type,
    pub params: Vec<Param>,
    pub ret: Type,
    pub scheme: Option<Scheme>,
    pub body: Block,
    pub captures: Vec<(String, Type)>,
    /// The top-level def this one belongs to (itself for top-level ones):
    /// the unit of generalization and the owner of constraints.
    pub unit: DefId,
    /// Effects the body performs directly.
    pub own_effect: Effect,
    pub closure_id: ClosId,
    pub line: usize,
    /// For a method or constructor: the class.
    pub class: Option<TypeId>,
    /// Default values of the parameters, checked in the def's own frame and
    /// copied into calls that leave them out.
    pub defaults: Vec<Option<Expr>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum FrameKind {
    Main,
    Plain,
    Ctor(TypeId),
    Method(TypeId),
}

/// One function being checked.
#[derive(Debug)]
pub(crate) struct Frame {
    pub def: DefId,
    pub kind: FrameKind,
    pub scopes: Vec<Scope>,
    pub captures: Vec<(String, Type)>,
    pub loop_depth: usize,
    /// Types of `return` values, joined into the return type.
    pub returns: Vec<Type>,
    pub ret: Type,
    /// A method assigned to a member (it must answer the rebuilt receiver).
    pub mutates_member: bool,
    /// `$` inside a pipeline stage.
    pub piped: Vec<Type>,
    /// The def's `unsafe` flag, inherited by lambdas inside it.
    pub unsafe_: bool,
}

pub(crate) struct Checker {
    pub store: TypeStore,
    pub types: Vec<DataType>,
    pub defs: Vec<DefInfo>,
    pub laws: Vec<Law>,
    pub frames: Vec<Frame>,
    pub diags: Vec<Diag>,
    /// Record literal shapes by sorted field names.
    pub record_shapes: HashMap<Vec<String>, TypeId>,
    /// Declared types and classes by name.
    pub type_names: HashMap<String, TypeId>,
    /// Constructors of declared types by name.
    pub ctor_names: HashMap<String, (TypeId, usize)>,
    pub lambda_counter: usize,
    /// Which constraint each instantiated constraint came from (for the
    /// effect of a forwarded dictionary).
    pub instance_of: HashMap<ConstraintId, ConstraintId>,
    /// Calls from one def to another, for effects, descent and cycles:
    /// (caller, callee, line).
    pub calls: Vec<(DefId, DefId, usize)>,
    /// The source line of the statement being checked.
    pub line: usize,
    /// Statements a mutating call inside an expression hoists in front of
    /// the statement being checked.
    pub pending: Vec<Stmt>,
    pub effects_final: Vec<Effect>,
    pub unsafe_final: Vec<bool>,
    pub descent_final: Vec<Descent>,
    /// Guards against re-entering the solver from a solution's unification.
    pub solving: bool,
    /// Which classes declare a method of each name.
    pub class_method_names: HashMap<String, Vec<TypeId>>,
    /// Rebindings whose only effect is a change (`p.x = 1`, `xs.push(v)`):
    /// def, line and name. One nothing reads afterwards is an error.
    pub changes: HashSet<(DefId, usize, String)>,
    /// Whether the rebinding being made is such a change.
    pub noting_change: bool,
}

pub use solve::describe_class;

/// Check a whole program.
pub fn check_program(program: &ast::Program) -> Result<Program, Vec<Diag>> {
    let mut ck = Checker::new();
    ck.run(program);
    if !ck.diags.is_empty() {
        let mut d = ck.diags;
        d.sort_by_key(|d| d.line);
        d.dedup_by(|a, b| a.line == b.line && a.message == b.message);
        return Err(d);
    }
    Ok(ck.finish())
}

impl Checker {
    fn new() -> Checker {
        let mut ck = Checker {
            store: TypeStore::new(),
            types: Vec::new(),
            defs: Vec::new(),
            laws: Vec::new(),
            frames: Vec::new(),
            diags: Vec::new(),
            record_shapes: HashMap::new(),
            type_names: HashMap::new(),
            ctor_names: HashMap::new(),
            lambda_counter: 0,
            instance_of: HashMap::new(),
            calls: Vec::new(),
            line: 0,
            pending: Vec::new(),
            effects_final: Vec::new(),
            unsafe_final: Vec::new(),
            descent_final: Vec::new(),
            solving: false,
            class_method_names: HashMap::new(),
            changes: HashSet::new(),
            noting_change: false,
        };
        ck.builtin_types();
        ck
    }

    /// `Maybe`, `Result`, the record `{key, value}` and `Range`, at their
    /// fixed positions. `{key, value}` is an ordinary record shape that the
    /// runtime also knows (as `F.Pair`): dictionary entries are built from
    /// it, and the compiler packs two values into one with it.
    fn builtin_types(&mut self) {
        let a = self.store.fresh_var();
        self.types.push(DataType {
            name: "Maybe".into(),
            params: vec![a],
            ctors: vec![
                Ctor { name: "None".into(), fields: vec![] },
                Ctor { name: "Some".into(), fields: vec![FieldDef { name: "value".into(), ty: Type::Var(a), public: true }] },
            ],
            kind: DataKind::Builtin,
            line: 0,
        });
        let e = self.store.fresh_var();
        let a = self.store.fresh_var();
        self.types.push(DataType {
            name: "Result".into(),
            params: vec![e, a],
            ctors: vec![
                Ctor { name: "Fail".into(), fields: vec![FieldDef { name: "err".into(), ty: Type::Var(e), public: true }] },
                Ctor { name: "Done".into(), fields: vec![FieldDef { name: "ok".into(), ty: Type::Var(a), public: true }] },
            ],
            kind: DataKind::Builtin,
            line: 0,
        });
        let k = self.store.fresh_var();
        let v = self.store.fresh_var();
        self.types.push(DataType {
            name: "{key, value}".into(),
            params: vec![k, v],
            ctors: vec![Ctor {
                name: "F.Pair".into(),
                fields: vec![
                    FieldDef { name: "key".into(), ty: Type::Var(k), public: true },
                    FieldDef { name: "value".into(), ty: Type::Var(v), public: true },
                ],
            }],
            kind: DataKind::Record { show_order: vec![0, 1] },
            line: 0,
        });
        self.record_shapes.insert(vec!["key".into(), "value".into()], PAIR);
        self.types.push(DataType {
            name: "Range".into(),
            params: vec![],
            ctors: vec![Ctor {
                name: "F.Range".into(),
                fields: vec![
                    FieldDef { name: "start".into(), ty: Type::Int, public: true },
                    FieldDef { name: "end".into(), ty: Type::Int, public: true },
                ],
            }],
            kind: DataKind::Builtin,
            line: 0,
        });
        assert_eq!(self.types.len(), BUILTIN_TYPES);
    }

    pub(crate) fn error(&mut self, line: usize, message: impl Into<String>) {
        self.diags.push(Diag { line, message: message.into() });
    }

    // -- frames and scopes ---------------------------------------------------

    pub(crate) fn frame(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame")
    }

    pub(crate) fn frame_ref(&self) -> &Frame {
        self.frames.last().expect("a frame")
    }

    pub(crate) fn current_def(&self) -> DefId {
        self.frame_ref().def
    }

    /// The unit of generalization of the current def.
    pub(crate) fn unit(&self) -> DefId {
        self.defs[self.current_def()].unit
    }

    pub(crate) fn push_scope(&mut self) {
        self.frame().scopes.push(Scope::default());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.frame().scopes.pop();
    }

    pub(crate) fn declare(&mut self, name: &str, b: Binding) {
        self.frame().scopes.last_mut().unwrap().names.insert(name.to_string(), b);
    }

    /// Look a name up through the current frame's scopes; when it is a
    /// local of an enclosing frame, capture it.
    pub(crate) fn lookup(&mut self, name: &str) -> Option<Binding> {
        let nframes = self.frames.len();
        for fi in (0..nframes).rev() {
            let frame = &self.frames[fi];
            for scope in frame.scopes.iter().rev() {
                if let Some(b) = scope.names.get(name) {
                    let b = b.clone();
                    if fi == nframes - 1 {
                        return Some(b);
                    }
                    return Some(self.capture(fi, name, b));
                }
            }
        }
        None
    }

    /// A binding from an enclosing frame: locals and members are captured
    /// by value into every frame in between; functions and types are
    /// global.
    fn capture(&mut self, from: usize, name: &str, b: Binding) -> Binding {
        match b {
            Binding::Local { ty, .. } => {
                for fi in from + 1..self.frames.len() {
                    let f = &mut self.frames[fi];
                    if !f.captures.iter().any(|(n, _)| n == name) {
                        f.captures.push((name.to_string(), ty.clone()));
                    }
                    f.scopes[0].names.insert(name.to_string(), Binding::Local { ty: ty.clone(), mutable: false });
                }
                Binding::Local { ty, mutable: false }
            }
            // a member reached from a lambda inside a method: the root local
            // is captured by value, the member is read from it
            Binding::Member { root, root_ty, path, ty, .. } => {
                let ctor_frame = matches!(self.frames[from].kind, FrameKind::Ctor(_));
                let method_frame = matches!(self.frames[from + 1].kind, FrameKind::Method(_));
                if ctor_frame && method_frame {
                    // a method sees the members of its object through self
                    return Binding::Member { root, root_ty, path, ty, mutable: false };
                }
                for fi in from + 1..self.frames.len() {
                    let f = &mut self.frames[fi];
                    if !f.captures.iter().any(|(n, _)| n == &root) {
                        f.captures.push((root.clone(), root_ty.clone()));
                    }
                    f.scopes[0].names.insert(root.clone(), Binding::Local { ty: root_ty.clone(), mutable: false });
                    f.scopes[0].names.insert(name.to_string(), Binding::Member { root: root.clone(), root_ty: root_ty.clone(), path: path.clone(), ty: ty.clone(), mutable: false });
                }
                Binding::Member { root, root_ty, path, ty, mutable: false }
            }
            other => other,
        }
    }

    /// A def by name, from the hoisted declarations of every enclosing
    /// scope.
    pub(crate) fn lookup_hoisted(&self, name: &str) -> Option<DefId> {
        for frame in self.frames.iter().rev() {
            for scope in frame.scopes.iter().rev() {
                if let Some(d) = scope.hoisted.get(name) {
                    return Some(*d);
                }
            }
        }
        None
    }

    // -- types ---------------------------------------------------------------

    pub(crate) fn fresh(&mut self) -> Type {
        self.store.fresh()
    }

    pub(crate) fn unify(&mut self, a: &Type, b: &Type, line: usize) -> bool {
        match self.store.unify(a, b) {
            Ok(()) => true,
            Err(e) => {
                let l = self.show_type(&e.left);
                let r = self.show_type(&e.right);
                let hint = match (self.store.shallow(&e.left), self.store.shallow(&e.right)) {
                    (Type::Int, Type::Float) | (Type::Float, Type::Int) => ": ints and floats do not mix; convert with `float(x)` or `int(x)`".to_string(),
                    (Type::List(_), Type::Data(PAIR, _)) | (Type::Data(PAIR, _), Type::List(_)) => format!(": {}", pattern::ENTRY_NOT_A_LIST),
                    _ => String::new(),
                };
                self.error(line, format!("type mismatch: expected {}, found {}{}", l, r, hint));
                false
            }
        }
    }

    pub(crate) fn show_type(&self, t: &Type) -> String {
        let names = |id: TypeId| self.types[id].name.clone();
        let vars = var_names(&self.store, &[t]);
        format!("{}", TypeDisplay { store: &self.store, ty: t, names: &names, vars: &vars })
    }

    pub(crate) fn resolve(&self, t: &Type) -> Type {
        self.store.resolve(t)
    }

    pub(crate) fn shallow(&self, t: &Type) -> Type {
        self.store.shallow(t)
    }

    /// Raise a constraint in the current unit and try to solve it at once.
    pub(crate) fn constrain(&mut self, class: Class, subject: Type, line: usize) -> ConstraintId {
        let unit = self.unit();
        let user = self.current_def();
        let id = self.store.constrain(class, subject, unit, user, line);
        self.solve_one(id);
        id
    }

    /// The Core expression that applies a constraint to arguments.
    pub(crate) fn dict(&mut self, class: Class, subject: Type, args: Vec<Expr>, ret: Type, line: usize) -> Expr {
        let id = self.constrain(class, subject, line);
        Expr { kind: ExprKind::Dict { id, args }, ty: ret, line }
    }

    /// A record shape for a set of field names (sorted), with one type
    /// variable per field.
    pub(crate) fn record_shape(&mut self, written: Vec<String>, line: usize) -> TypeId {
        let mut names = written.clone();
        names.sort();
        if let Some(id) = self.record_shapes.get(&names) {
            return *id;
        }
        let show_order: Vec<usize> = written.iter().filter_map(|w| names.iter().position(|n| n == w)).collect();
        let params: Vec<TVar> = names.iter().map(|_| self.store.fresh_var()).collect();
        let fields = names.iter().zip(params.iter()).map(|(n, v)| FieldDef { name: n.clone(), ty: Type::Var(*v), public: true }).collect();
        let id = self.types.len();
        self.types.push(DataType {
            name: format!("{{{}}}", names.join(", ")),
            params,
            ctors: vec![Ctor { name: "Record".into(), fields }],
            kind: DataKind::Record { show_order },
            line,
        });
        self.record_shapes.insert(names, id);
        id
    }

    /// The type of a data type applied to fresh arguments, and the field
    /// types of its constructor under that instantiation.
    pub(crate) fn instantiate_type(&mut self, id: TypeId) -> (Type, Vec<(TVar, Type)>) {
        let params = self.types[id].params.clone();
        let subst: Vec<(TVar, Type)> = params.iter().map(|v| (*v, self.store.fresh())).collect();
        let args = subst.iter().map(|(_, t)| t.clone()).collect();
        (Type::Data(id, args), subst)
    }

    /// The field types of constructor `ci` of data type `id` at the given
    /// type arguments.
    pub(crate) fn ctor_field_types(&mut self, id: TypeId, ci: usize, args: &[Type]) -> Vec<Type> {
        let params = self.types[id].params.clone();
        let subst: Vec<(TVar, Type)> = params.iter().cloned().zip(args.iter().cloned()).collect();
        let fields: Vec<Type> = self.types[id].ctors[ci].fields.iter().map(|f| f.ty.clone()).collect();
        fields.iter().map(|t| self.store.substitute(t, &subst)).collect()
    }

    // -- defs ------------------------------------------------------------------

    pub(crate) fn new_def(&mut self, name: &str, kind: DefKind, unit: Option<DefId>, line: usize) -> DefId {
        let id = self.defs.len();
        let closure_id = id;
        let mono = self.store.fresh();
        self.defs.push(DefInfo {
            name: name.to_string(),
            kind,
            unsafe_: false,
            state: State::NotYet,
            source: None,
            mono,
            params: Vec::new(),
            ret: Type::Unit,
            scheme: None,
            body: Block::default(),
            captures: Vec::new(),
            unit: unit.unwrap_or(id),
            own_effect: Effect::PURE,
            closure_id,
            line,
            class: None,
            defaults: Vec::new(),
        });
        id
    }

    /// Note an effect performed directly by the current def's body.
    pub(crate) fn effect(&mut self, e: Effect) {
        let d = self.current_def();
        self.defs[d].own_effect = self.defs[d].own_effect.join(e);
    }

    /// Note a call from the current def.
    pub(crate) fn note_call(&mut self, callee: DefId, line: usize) {
        let caller = self.current_def();
        self.calls.push((caller, callee, line));
    }

    // -- program driver --------------------------------------------------------

    fn run(&mut self, program: &ast::Program) {
        // main: the top-level statements
        let main = self.new_def("main", DefKind::Main, None, 1);
        self.defs[main].state = State::InProgress;
        self.frames.push(Frame {
            def: main,
            kind: FrameKind::Main,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: Type::Unit,
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: false,
        });
        // declared types first: constructors and type names are global
        for s in &program.statements {
            if let ast::Statement::TypeDecl { name, ctors } = &s.node {
                self.declare_type(name, ctors, s.line);
            }
        }
        for s in &program.statements {
            if let ast::Statement::TypeDecl { name, ctors } = &s.node {
                self.fill_type(name, ctors, s.line);
            }
        }
        self.hoist_defs(&program.statements);
        let body = self.check_block_stmts(&program.statements);
        // every hoisted top-level def is checked even when never called
        let pending: Vec<DefId> = self.frames[0].scopes[0].hoisted.values().cloned().collect();
        for d in pending {
            self.ensure_def(d, 0);
        }
        // laws see every def and type of the program (inside main's scope)
        for s in &program.statements {
            if let ast::Statement::Law { name, vars, hyp, claim } = &s.node {
                self.check_law(name, vars, hyp.as_ref(), claim, s.line);
            }
        }
        let mut body = body;
        self.frames.pop();
        self.solve_pending();
        self.defs[main].body = std::mem::take(&mut body);
        self.defs[main].state = State::Done;
        self.defs[main].scheme = Some(Scheme { vars: vec![], dicts: vec![], ty: self.store.fresh_fn(vec![], Type::Unit) });
        self.finish_constraints();
        self.check_cycles();
        self.infer_effects();
        self.check_descent();
        self.check_law_subjects();
        self.check_lost_changes();
    }

    /// Declare the defs of a block in the current scope so they can be
    /// referenced before their statement. In a constructor body, defs are
    /// methods.
    pub(crate) fn hoist_defs(&mut self, stmts: &[ast::Stmt]) {
        let frame_index = self.frames.len() - 1;
        let depth = self.frame_ref().scopes.len() - 1;
        let in_ctor = match self.frame_ref().kind {
            FrameKind::Ctor(t) if depth == 0 => Some(t),
            _ => None,
        };
        for s in stmts {
            if let ast::Statement::Def { is_public: _, is_unsafe, name, params, return_type, body } = &s.node {
                if let Some(tid) = in_ctor {
                    self.declare_method(tid, name, params, return_type.clone(), body.clone(), *is_unsafe, s.line);
                    continue;
                }
                let is_class = params.iter().any(|p| p.is_public) || body.iter().any(stmt_declares_public);
                let unit = if self.frame_ref().kind == FrameKind::Main { None } else { Some(self.unit()) };
                let kind = DefKind::Plain;
                let id = self.new_def(name, kind, unit, s.line);
                self.defs[id].unsafe_ = *is_unsafe || self.frame_ref().unsafe_;
                self.defs[id].source = Some(Source {
                    params: params.clone(),
                    return_type: return_type.clone(),
                    body: body.clone(),
                    frame: frame_index,
                    depth,
                });
                if is_class {
                    let tid = self.declare_class(name, id, body, s.line);
                    self.defs[id].kind = DefKind::Ctor(tid);
                    self.defs[id].class = Some(tid);
                    self.declare(name, Binding::Class(tid));
                } else {
                    self.declare(name, Binding::Func(id));
                }
                self.frame().scopes.last_mut().unwrap().hoisted.insert(name.clone(), id);
            }
        }
    }

    /// Check a hoisted def now if it has not been checked yet. `line` is
    /// where it was needed.
    pub(crate) fn ensure_def(&mut self, id: DefId, line: usize) {
        match self.defs[id].state {
            State::Done | State::InProgress => {}
            State::NotYet => {
                let _ = line;
                self.check_def(id);
            }
        }
    }

    /// Infer a hoisted def from its source.
    fn check_def(&mut self, id: DefId) {
        let source = match self.defs[id].source.clone() {
            Some(s) => s,
            None => return,
        };
        self.defs[id].state = State::InProgress;
        // the def's scope chain: the frames up to where it was declared stay
        // visible; the frames after it are hidden while its body is checked
        let hidden: Vec<Frame> = self.frames.drain(source.frame + 1..).collect();
        let saved_depth = self.frames[source.frame].scopes.len();
        // scopes deeper than the declaration are not visible to the def
        let hidden_scopes: Vec<Scope> = self.frames[source.frame].scopes.drain(source.depth + 1..).collect();
        let _ = saved_depth;
        let kind = match self.defs[id].kind {
            DefKind::Ctor(t) => FrameKind::Ctor(t),
            DefKind::Method { rec, .. } => FrameKind::Method(rec),
            _ => FrameKind::Plain,
        };
        let is_top = self.defs[id].unit == id;
        if is_top {
            self.store.enter_level();
        }
        // the type recursive calls see, at the def's own level so that
        // binding it never pins the def's variables
        let mono = self.fresh();
        self.defs[id].mono = mono;
        let ret = self.fresh();
        self.frames.push(Frame {
            def: id,
            kind,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: ret.clone(),
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: self.defs[id].unsafe_,
        });
        let (params, mut body) = match kind {
            FrameKind::Ctor(tid) => self.check_ctor_body(id, tid, &source),
            FrameKind::Method(tid) => self.check_method_body(id, tid, &source),
            _ => self.check_plain_body(id, &source),
        };
        let frame = self.frames.pop().unwrap();
        let captures = frame.captures.clone();
        let mutates = frame.mutates_member;
        self.solve_pending();
        let mut ret = match kind {
            FrameKind::Ctor(tid) => Type::Data(tid, self.types[tid].params.iter().map(|v| Type::Var(*v)).collect()),
            _ => self.join_returns(&frame, ret),
        };
        // a mutating method answers the rebuilt receiver (and its value)
        if let FrameKind::Method(tid) = kind {
            let returns_value = !matches!(self.shallow(&ret), Type::Unit);
            if mutates {
                self.method_epilogue(tid, &mut body, returns_value);
                let selft = self.class_self_type(tid);
                ret = if returns_value { Type::pair(selft, ret) } else { selft };
            }
            self.defs[id].kind = DefKind::Method { rec: tid, mutates, returns_value };
        }
        if is_top {
            self.store.leave_level();
        }
        let param_types: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();
        let fty = match self.shallow(&self.defs[id].mono.clone()) {
            Type::Fn(_, _, c) => Type::Fn(param_types.clone(), Box::new(ret.clone()), c),
            _ => {
                let c = self.store.clos_singleton(self.defs[id].closure_id);
                Type::Fn(param_types.clone(), Box::new(ret.clone()), c)
            }
        };
        let mono = self.defs[id].mono.clone();
        // a mutating method's type was not visible to its recursive calls
        let _ = self.store.unify(&mono, &fty);
        let scheme = if is_top { self.store.generalize(&fty, id) } else { Scheme { vars: vec![], dicts: vec![], ty: self.resolve(&fty) } };
        // a dictionary of a fallible class answers a result whatever the
        // instantiation: the def may abort, and so may a lambda inside it
        // that performs the operation
        let fallible: Vec<DefId> = scheme.dicts.iter().filter(|c| self.store.constraints[**c].class.fallible()).map(|c| self.store.constraints[*c].user).collect();
        let scheme = self.merge_dicts(scheme);
        if !fallible.is_empty() {
            self.defs[id].own_effect = self.defs[id].own_effect.join(Effect::ABORT);
        }
        for user in fallible {
            self.defs[user].own_effect = self.defs[user].own_effect.join(Effect::ABORT);
        }
        let d = &mut self.defs[id];
        d.params = params;
        d.ret = ret;
        d.body = body;
        d.captures = captures;
        d.scheme = Some(scheme);
        d.state = State::Done;
        // restore the scope chain
        self.frames[source.frame].scopes.extend(hidden_scopes);
        self.frames.extend(hidden);
    }

    /// Check the parameters and body of a plain def.
    fn check_plain_body(&mut self, id: DefId, source: &Source) -> (Vec<Param>, Block) {
        let line = self.defs[id].line;
        let params = self.check_params(&source.params, line);
        if let Some(rt) = &source.return_type {
            let t = self.annotation(rt, line);
            let ret = self.frame_ref().ret.clone();
            self.unify(&ret, &t, line);
        }
        let param_types: Vec<Type> = params.iter().map(|p| p.ty.clone()).collect();
        // the monomorphic type is visible to recursive calls from here on
        let ret = self.frame_ref().ret.clone();
        let c = self.store.clos_singleton(self.defs[id].closure_id);
        let fty = Type::Fn(param_types, Box::new(ret), c);
        let mono = self.defs[id].mono.clone();
        self.unify(&mono, &fty, line);
        self.defs[id].params = params.clone();
        self.defs[id].defaults = source.params.iter().zip(params.iter()).map(|(p, cp)| {
            p.default.as_ref().map(|d| {
                let x = self.check_expr(d, Some(&cp.ty));
                self.unify(&cp.ty, &x.ty, line);
                x
            })
        }).collect();
        let mut param_stmts = Vec::new();
        for (p, ast_p) in params.iter().zip(source.params.iter()) {
            param_stmts.extend(self.destructure_param(p, &ast_p.pattern));
        }
        self.hoist_defs(&source.body);
        let mut body = self.check_block_stmts(&source.body);
        param_stmts.append(&mut body.stmts);
        body.stmts = param_stmts;
        self.finish_body_value(&mut body, line);
        (params, body)
    }

    /// Declare the parameters of a def or lambda in the current scope and
    /// return them as Core params (destructuring parameters become leading
    /// statements later; here they get synthetic names).
    pub(crate) fn check_params(&mut self, params: &[ast::Param], line: usize) -> Vec<Param> {
        let mut out = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let ty = match &p.pattern {
                ast::Pattern::Typed { type_expr, .. } => self.annotation(type_expr, line),
                _ => self.fresh(),
            };
            let name = match &p.pattern {
                ast::Pattern::Identifier(n) => n.clone(),
                ast::Pattern::Typed { pattern, .. } => match &**pattern {
                    ast::Pattern::Identifier(n) => n.clone(),
                    _ => format!("__p{}", i),
                },
                _ => format!("__p{}", i),
            };
            self.declare(&name, Binding::Local { ty: ty.clone(), mutable: p.is_var });
            out.push(Param { name, ty });
        }
        out
    }

    /// A block's value: its last expression statement, or a trailing `if`
    /// or `match` statement whose branches all end in a value (rewritten
    /// into an expression). Answers the value's type, or None when the
    /// block ends otherwise (a return, a loop, a statement without value).
    /// With `exits`, a branch that always leaves (`return`, `break`,
    /// `continue`) has no value to give, and the others make the value; the
    /// binding of such a value becomes a statement (`lift_exits`).
    pub(crate) fn block_value(&mut self, body: &mut Block, exits: bool) -> Option<Type> {
        // a trailing `if` or `match` with an early `return` stays a statement:
        // as an expression its returns would no longer leave the def
        if !exits
            && matches!(body.stmts.last(), Some(Stmt { kind: StmtKind::If { .. } | StmtKind::Match { .. }, .. }))
            && contains_return(std::slice::from_ref(body.stmts.last().unwrap())) {
            return None;
        }
        match body.stmts.last() {
            Some(Stmt { kind: StmtKind::Expr(e), .. }) => Some(e.ty.clone()),
            Some(Stmt { kind: StmtKind::If { else_, .. }, .. }) if !else_.stmts.is_empty() => {
                let Some(Stmt { kind: StmtKind::If { cond, mut then, mut else_ }, line }) = body.stmts.pop() else { unreachable!() };
                let (leave1, leave2) = (exits && always_exits(&then.stmts), exits && always_exits(&else_.stmts));
                let t1 = if leave1 { None } else { self.block_value(&mut then, exits) };
                let t2 = if leave2 { None } else { self.block_value(&mut else_, exits) };
                // a branch that leaves takes the other's type
                let (t1, t2) = match (t1, t2) {
                    (None, Some(b)) if leave1 => (Some(b.clone()), Some(b)),
                    (Some(a), None) if leave2 => (Some(a.clone()), Some(a)),
                    (None, None) if leave1 && leave2 => {
                        let t = self.fresh();
                        (Some(t.clone()), Some(t))
                    }
                    other => other,
                };
                match (t1, t2) {
                    (Some(a), Some(b)) if leave1 || leave2 => {
                        let ta = Expr { kind: ExprKind::Block(then), ty: a.clone(), line };
                        let tb = Expr { kind: ExprKind::Block(else_), ty: b, line };
                        body.stmts.push(Stmt { kind: StmtKind::Expr(Expr { kind: ExprKind::If(Box::new(cond), Box::new(ta), Box::new(tb)), ty: a.clone(), line }), line });
                        Some(a)
                    }
                    (Some(a), Some(b)) => {
                        let ta = Expr { kind: ExprKind::Block(then), ty: a, line };
                        let tb = Expr { kind: ExprKind::Block(else_), ty: b, line };
                        self.line = line;
                        let (ta, tb, ty) = self.join_branches(ta, tb);
                        body.stmts.push(Stmt { kind: StmtKind::Expr(Expr { kind: ExprKind::If(Box::new(cond), Box::new(ta), Box::new(tb)), ty: ty.clone(), line }), line });
                        Some(ty)
                    }
                    _ => {
                        body.stmts.push(Stmt { kind: StmtKind::If { cond, then, else_ }, line });
                        None
                    }
                }
            }
            Some(Stmt { kind: StmtKind::Match { .. }, .. }) => {
                let Some(Stmt { kind: StmtKind::Match { subject, mut arms }, line }) = body.stmts.pop() else { unreachable!() };
                let mut tys = Vec::new();
                let mut ok = true;
                // an arm that always leaves has no value to give
                let leaves: Vec<bool> = arms.iter().map(|a| exits && matches!(&a.body.kind, ExprKind::Block(b) if always_exits(&b.stmts))).collect();
                for (a, _) in arms.iter_mut().zip(&leaves).filter(|(_, l)| !**l) {
                    let t = match &mut a.body.kind {
                        ExprKind::Block(b) => {
                            let t = self.block_value(b, exits);
                            if let Some(t) = &t {
                                a.body.ty = t.clone();
                            }
                            t
                        }
                        _ => Some(a.body.ty.clone()),
                    };
                    match t {
                        Some(t) => tys.push(t),
                        None => ok = false,
                    }
                }
                if ok && (!tys.is_empty() || exits) {
                    // `nothing` arms lift the others into a maybe
                    let mut ty = tys.first().cloned().unwrap_or_else(|| self.fresh());
                    let nothing_arm = arms.iter().zip(&leaves).any(|(a, l)| !l && expr::is_nothing_value(&a.body));
                    let value_arm = arms.iter().zip(&leaves).any(|(a, l)| !l && !matches!(self.shallow(&a.body.ty), Type::Unit));
                    if nothing_arm && value_arm {
                        let inner = arms.iter().zip(&leaves).find(|(a, l)| !**l && !matches!(self.shallow(&a.body.ty), Type::Unit)).map(|(a, _)| a.body.ty.clone()).unwrap();
                        let inner = match self.shallow(&inner) {
                            Type::Data(MAYBE, args) => args[0].clone(),
                            _ => inner,
                        };
                        ty = Type::maybe(inner.clone());
                        for (a, _) in arms.iter_mut().zip(&leaves).filter(|(_, l)| !**l) {
                            if expr::is_nothing_value(&a.body) {
                                let b = std::mem::replace(&mut a.body, Expr { kind: ExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: a.line });
                                a.body = self.absent(b, &ty);
                            } else {
                                let b = std::mem::replace(&mut a.body, Expr { kind: ExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: a.line });
                                a.body = self.some(b);
                            }
                        }
                    }
                    for (a, l) in arms.iter_mut().zip(&leaves) {
                        if *l {
                            a.body.ty = ty.clone();
                        } else {
                            self.unify(&ty, &a.body.ty, a.line);
                        }
                    }
                    body.stmts.push(Stmt { kind: StmtKind::Expr(Expr { kind: ExprKind::Match(Box::new(subject), arms), ty: ty.clone(), line }), line });
                    Some(ty)
                } else {
                    body.stmts.push(Stmt { kind: StmtKind::Match { subject, arms }, line });
                    None
                }
            }
            _ => None,
        }
    }

    /// The last expression statement of a body is its value; a body that
    /// ends otherwise answers `nothing`. Then every return of the body is
    /// joined into the frame's result type.
    pub(crate) fn finish_body_value(&mut self, body: &mut Block, line: usize) {
        let ret = self.frame_ref().ret.clone();
        // a trailing `if`/`match` whose branches assign stays a statement: as
        // a value its branches would be terms, and the assignments (a member
        // of a method's object, say) would not leave them
        let assigns = match body.stmts.last() {
            Some(s @ Stmt { kind: StmtKind::If { .. } | StmtKind::Match { .. }, .. }) => {
                let mut found = false;
                effects::for_each_stmt(&Block { stmts: vec![s.clone()] }, &mut |s: &Stmt| {
                    if matches!(s.kind, StmtKind::Assign { .. }) {
                        found = true;
                    }
                });
                found
            }
            _ => false,
        };
        if assigns || self.block_value(body, false).is_none() {
            // a trailing `if`/`match` kept as a statement: its branch values
            // are the def's answers
            tail_returns(body);
            let ends = match body.stmts.last() {
                Some(Stmt { kind: StmtKind::Return(_), .. }) => true,
                Some(Stmt { kind: StmtKind::If { .. } | StmtKind::Match { .. }, .. }) => self.block_always_returns(body),
                _ => false,
            };
            if !ends {
                let last_line = body.stmts.last().map(|s| s.line).unwrap_or(line);
                body.stmts.push(Stmt { kind: StmtKind::Expr(Expr { kind: ExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: last_line }), line: last_line });
            }
        }
        // a trailing expression statement is the return value
        if matches!(body.stmts.last(), Some(Stmt { kind: StmtKind::Expr(_), .. }))
            && let Some(Stmt { kind: StmtKind::Expr(e), line: l }) = body.stmts.pop() {
                body.stmts.push(Stmt { kind: StmtKind::Return(e), line: l });
            }
        self.join_return_values(body, &ret, line);
    }

    /// Join the values a body returns into its result type. `nothing` on
    /// some paths and a value on others make a `T | nothing`: the values
    /// are lifted and `nothing` becomes the absent value.
    fn join_return_values(&mut self, body: &mut Block, ret: &Type, line: usize) {
        let mut rets: Vec<(Type, bool, usize)> = Vec::new();
        classes::rewrite_returns(body, &mut |e: Expr| {
            rets.push((e.ty.clone(), matches!(e.kind, ExprKind::Lit(Lit::Nothing)), e.line));
            e
        });
        let is_maybe = |c: &Checker, t: &Type| matches!(c.shallow(t), Type::Data(MAYBE, _));
        let nothing = rets.iter().any(|r| r.1);
        let maybe = rets.iter().any(|r| !r.1 && is_maybe(self, &r.0));
        // a value of a type not known yet is a value too (a generic
        // parameter, say), except the def's own result (a recursive call)
        let ret_var = match self.shallow(ret) {
            Type::Var(v) => Some(v),
            _ => None,
        };
        let plain = rets.iter().any(|r| {
            !r.1 && !is_maybe(self, &r.0)
                && match self.shallow(&r.0) {
                    Type::Unit => false,
                    Type::Var(v) => Some(v) != ret_var,
                    _ => true,
                }
        });
        let inner = match self.shallow(ret) {
            Type::Data(MAYBE, args) => Some(args[0].clone()),
            _ if (nothing || maybe) && plain => Some(self.fresh()),
            _ => None,
        };
        match inner {
            Some(inner) => {
                let mt = Type::maybe(inner.clone());
                for (t, is_nothing, l) in &rets {
                    if *is_nothing {
                        continue;
                    }
                    match self.shallow(t) {
                        Type::Data(MAYBE, a) => self.unify(&inner, &a[0], *l),
                        _ => self.unify(&inner, t, *l),
                    };
                }
                let mut lifted: Vec<Expr> = Vec::new();
                classes::rewrite_returns(body, &mut |e: Expr| {
                    lifted.push(e);
                    Expr { kind: ExprKind::Lit(Lit::Nothing), ty: Type::Unit, line: 0 }
                });
                let lifted: Vec<Expr> = lifted.into_iter().map(|e| {
                    if matches!(e.kind, ExprKind::Lit(Lit::Nothing)) {
                        self.expr(ExprKind::Con(MAYBE, 0, vec![]), mt.clone())
                    } else {
                        self.some(e)
                    }
                }).collect();
                let mut it = lifted.into_iter();
                classes::rewrite_returns(body, &mut |_e: Expr| it.next().unwrap());
                self.unify(ret, &mt, line);
            }
            None => {
                for (t, _, l) in &rets {
                    self.unify(ret, t, *l);
                }
            }
        }
    }

    pub(crate) fn block_always_returns(&self, b: &Block) -> bool {
        match b.stmts.last() {
            Some(Stmt { kind: StmtKind::Return(_), .. }) => true,
            Some(Stmt { kind: StmtKind::If { then, else_, .. }, .. }) => !else_.stmts.is_empty() && self.block_always_returns(then) && self.block_always_returns(else_),
            Some(Stmt { kind: StmtKind::Match { arms, .. }, .. }) => {
                arms.iter().all(|a| matches!(&a.body.kind, ExprKind::Block(b) if self.block_always_returns(b)))
            }
            _ => false,
        }
    }

    /// The result type of a finished body (its returns were joined by
    /// `finish_body_value`).
    fn join_returns(&mut self, _frame: &Frame, ret: Type) -> Type {
        ret
    }

    // -- finishing -------------------------------------------------------------

    /// Solve every constraint whose subject is now known.
    pub(crate) fn solve_pending(&mut self) {
        if self.solving {
            return;
        }
        self.solving = true;
        let mut progress = true;
        while progress {
            progress = false;
            for id in 0..self.store.constraints.len() {
                if self.store.constraints[id].solution.is_none() && self.solve_one(id) {
                    progress = true;
                }
            }
        }
        self.solving = false;
    }

    fn finish_constraints(&mut self) {
        self.solve_pending();
        // dictionaries of generalized defs stay open; everything else must
        // be solved, defaulting numeric variables to int first
        let dict_ids: Vec<ConstraintId> = self.defs.iter().filter_map(|d| d.scheme.as_ref()).flat_map(|s| s.dicts.clone()).collect();
        for id in 0..self.store.constraints.len() {
            if self.store.constraints[id].solution.is_some() || dict_ids.contains(&id) {
                continue;
            }
            let c = self.store.constraints[id].clone();
            if let Type::Var(v) = self.shallow(&c.subject) {
                // every open constraint on this variable
                let on_var: Vec<Class> = (0..self.store.constraints.len())
                    .filter(|k| self.store.constraints[*k].solution.is_none() && !dict_ids.contains(k))
                    .filter(|k| matches!(self.shallow(&self.store.constraints[*k].subject), Type::Var(w) if w == v))
                    .map(|k| self.store.constraints[k].class.clone())
                    .collect();
                // the first candidate that satisfies all of them
                let candidates = [Type::Int, Type::list(self.fresh()), Type::Str, Type::Float];
                let pick = candidates.iter().find(|t| on_var.iter().all(|cl| self.class_fits(cl, t))).cloned();
                if let Some(t) = pick {
                    let _ = self.store.unify(&c.subject, &t);
                    self.solve_pending();
                }
            }
        }
        self.solve_pending();
        for id in 0..self.store.constraints.len() {
            if self.store.constraints[id].solution.is_some() || dict_ids.contains(&id) {
                continue;
            }
            let c = self.store.constraints[id].clone();
            let what = solve::describe_class(&c.class);
            let subject = self.show_type(&c.subject);
            self.error(c.line, format!("cannot resolve {} on a value of type {}", what, subject));
        }
    }

    /// One dictionary per operation and subject: a second constraint for
    /// the same operation on the same type is the first one (their types
    /// are then the same, as the subject determines them) and is answered
    /// by it.
    fn merge_dicts(&mut self, scheme: Scheme) -> Scheme {
        let mut kept: Vec<ConstraintId> = Vec::new();
        for &d in &scheme.dicts {
            let c = self.store.constraints[d].clone();
            let subject = self.resolve(&c.subject);
            let found = kept.iter().position(|&k| {
                let o = &self.store.constraints[k];
                o.class.same_op(&c.class) && self.resolve(&o.subject) == subject
            });
            match found {
                Some(i) => {
                    let o = self.store.constraints[kept[i]].class.clone();
                    let (a, b) = (TypeStore::class_types(&o), TypeStore::class_types(&c.class));
                    let ok = a.iter().zip(b.iter()).all(|(x, y)| self.store.unify(x, y).is_ok());
                    if ok {
                        self.store.constraints[d].solution = Some(Solution::Param(i));
                    } else {
                        kept.push(d);
                    }
                }
                None => kept.push(d),
            }
        }
        let vars: Vec<TVar> = scheme.vars.iter().cloned().filter(|v| matches!(self.shallow(&Type::Var(*v)), Type::Var(w) if w == *v)).collect();
        Scheme { vars, dicts: kept, ty: self.resolve(&scheme.ty) }
    }

    /// Whether a class could be solved on a candidate type (for choosing
    /// the default of a type nothing fixed).
    fn class_fits(&mut self, class: &Class, t: &Type) -> bool {
        let is = |x: &Type| matches!(x, Type::Int | Type::Float);
        match class {
            Class::Eq | Class::Ord | Class::Show => true,
            Class::Arith(ArithOp::Add) => is(t) || matches!(t, Type::Str | Type::List(_)),
            Class::Arith(_) => is(t),
            Class::Zero => is(t) || matches!(t, Type::Str | Type::List(_)),
            Class::Convert(..) => matches!(t, Type::Int | Type::Float | Type::Str | Type::Bool),
            Class::Len | Class::Iter(_) => matches!(t, Type::List(_) | Type::Str),
            Class::Index(_, elem) => match t {
                Type::List(_) => true,
                Type::Str => self.compatible(elem, &Type::Str),
                _ => false,
            },
            Class::IndexSet(..) => matches!(t, Type::List(_)),
            Class::Method(name, args, ret) => match solve::method_sig(&mut self.store, t, name, args.len()) {
                Some((_, r, _)) => self.compatible(&r, ret),
                None => false,
            },
            Class::OrElse(..) => matches!(t, Type::Bool),
            Class::Field(..) | Class::SetField(..) => false,
        }
    }

    /// Whether two types could unify (a variable fits anything), without
    /// binding anything.
    fn compatible(&self, a: &Type, b: &Type) -> bool {
        match (self.shallow(a), self.shallow(b)) {
            (Type::Var(_), _) | (_, Type::Var(_)) => true,
            (Type::List(x), Type::List(y)) | (Type::Map(x), Type::Map(y)) => self.compatible(&x, &y),
            (Type::Data(i, xs), Type::Data(j, ys)) => i == j && xs.iter().zip(ys.iter()).all(|(x, y)| self.compatible(x, y)),
            (Type::Fn(ps, r, _), Type::Fn(qs, s, _)) => ps.len() == qs.len() && ps.iter().zip(qs.iter()).all(|(x, y)| self.compatible(x, y)) && self.compatible(&r, &s),
            (x, y) => std::mem::discriminant(&x) == std::mem::discriminant(&y),
        }
    }

    fn finish(self) -> Program {
        let mut defs = Vec::new();
        let n = self.defs.len();
        for id in 0..n {
            let d = self.defs[id].clone();
            let scheme = d.scheme.clone().unwrap_or(Scheme { vars: vec![], dicts: vec![], ty: d.mono.clone() });
            defs.push(Def {
                id,
                name: d.name,
                kind: d.kind,
                unit: d.unit,
                unsafe_: d.unsafe_,
                params: d.params,
                captures: d.captures,
                scheme,
                ret: d.ret,
                body: d.body,
                effect: self.effects_final.get(id).cloned().unwrap_or(d.own_effect),
                relies_on_unsafe: self.unsafe_final.get(id).cloned().unwrap_or(d.unsafe_),
                descent: self.descent_final.get(id).cloned().unwrap_or(Descent::None),
                closure_id: d.closure_id,
                line: d.line,
            });
        }
        Program { types: self.types, defs, laws: self.laws, main: 0, store: self.store }
    }
}

/// Whether a statement declares a public member (making its def a class).
pub(crate) fn stmt_declares_public(s: &ast::Stmt) -> bool {
    match &s.node {
        ast::Statement::Declaration { is_public, .. } => *is_public,
        ast::Statement::Def { is_public, .. } => *is_public,
        _ => false,
    }
}

/// Does any statement (or a block nested in one) `return`?
pub(crate) fn contains_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Return(_) => true,
        StmtKind::If { then, else_, .. } => contains_return(&then.stmts) || contains_return(&else_.stmts),
        StmtKind::Match { arms, .. } => arms.iter().any(|a| matches!(&a.body.kind, ExprKind::Block(b) if contains_return(&b.stmts))),
        StmtKind::For { body, .. } | StmtKind::While { body, .. } => contains_return(&body.stmts),
        _ => false,
    })
}

/// Does control leave a block by `return`, `break` or `continue`? A
/// `break` or `continue` inside a loop of the block stays in that loop.
pub(crate) fn contains_exit(stmts: &[Stmt]) -> bool {
    stmts_exit(stmts, false)
}

/// Whether evaluating a value may leave by `return`, `break` or `continue`
/// (through a block inside it).
pub(crate) fn value_exits(e: &Expr) -> bool {
    expr_exits(e, false)
}

fn stmts_exit(stmts: &[Stmt], in_loop: bool) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Return(_) => true,
        StmtKind::Break | StmtKind::Continue => !in_loop,
        StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) => expr_exits(value, in_loop),
        StmtKind::If { cond, then, else_ } => expr_exits(cond, in_loop) || stmts_exit(&then.stmts, in_loop) || stmts_exit(&else_.stmts, in_loop),
        StmtKind::Match { subject, arms } => expr_exits(subject, in_loop) || arms.iter().any(|a| a.guard.as_ref().is_some_and(|g| expr_exits(g, in_loop)) || expr_exits(&a.body, in_loop)),
        StmtKind::For { iters, body, .. } => iters.iter().any(|it| match it {
            Iter::Items(e, _) | Iter::Counter(e) => expr_exits(e, in_loop),
        }) || stmts_exit(&body.stmts, true),
        StmtKind::While { cond, body } => expr_exits(cond, true) || stmts_exit(&body.stmts, true),
        StmtKind::Bind { .. } => false,
    })
}

fn expr_exits(e: &Expr, in_loop: bool) -> bool {
    let sub = |x: &Expr| expr_exits(x, in_loop);
    match &e.kind {
        ExprKind::Block(b) => stmts_exit(&b.stmts, in_loop),
        // a lambda is a def of its own
        ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => false,
        ExprKind::List(items) | ExprKind::Con(_, _, items) | ExprKind::Builtin(_, items) => items.iter().any(sub),
        ExprKind::Call { args, .. } | ExprKind::Dict { args, .. } => args.iter().any(sub),
        ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => sub(o),
        ExprKind::SetField(a, _, _, b) | ExprKind::And(a, b) | ExprKind::Or(a, b) => sub(a) || sub(b),
        ExprKind::CallClosure(f, args) => sub(f) || args.iter().any(sub),
        ExprKind::If(c, t, el) => sub(c) || sub(t) || sub(el),
        ExprKind::Match(s, arms) => sub(s) || arms.iter().any(|a| a.guard.as_ref().is_some_and(sub) || sub(&a.body)),
        ExprKind::FString(parts) => parts.iter().any(|p| matches!(p, FPart::Expr(x, _) if sub(x))),
    }
}

/// Does a block always leave by `return`, `break` or `continue`?
pub(crate) fn always_exits(stmts: &[Stmt]) -> bool {
    match stmts.last().map(|s| &s.kind) {
        Some(StmtKind::Return(_) | StmtKind::Break | StmtKind::Continue) => true,
        Some(StmtKind::If { then, else_, .. }) => !else_.stmts.is_empty() && always_exits(&then.stmts) && always_exits(&else_.stmts),
        Some(StmtKind::Match { arms, .. }) => !arms.is_empty() && arms.iter().all(|a| matches!(&a.body.kind, ExprKind::Block(b) if always_exits(&b.stmts))),
        _ => false,
    }
}

/// Turn the value a block ends on into a `return`, through a trailing
/// `if`/`else` or `match`.
fn tail_returns(b: &mut Block) {
    let Some(last) = b.stmts.last_mut() else { return };
    match &mut last.kind {
        StmtKind::Expr(_) => {
            let Some(Stmt { kind: StmtKind::Expr(e), line }) = b.stmts.pop() else { unreachable!() };
            b.stmts.push(Stmt { kind: StmtKind::Return(e), line });
        }
        StmtKind::If { then, else_, .. } if !else_.stmts.is_empty() => {
            tail_returns(then);
            tail_returns(else_);
        }
        StmtKind::Match { arms, .. } => {
            for a in arms {
                if let ExprKind::Block(blk) = &mut a.body.kind {
                    tail_returns(blk);
                }
            }
        }
        _ => {}
    }
}
