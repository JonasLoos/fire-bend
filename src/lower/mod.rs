// src/lower/mod.rs
// Lowering: Core -> Bend IR. See docs/compiler.md.
//
// Every Fire def becomes one Bend def. Its quantified type variables are
// erased or template parameters, its dictionaries template parameters, a
// function-typed parameter that the body only calls is a template (code)
// plus an environment value, a self-recursive def gets its descending
// parameter first (or a Nat fuel). This file holds the driver: names,
// types, def images, closure representations, derived defs and the
// resolution of dictionaries to Bend terms. `body.rs` lowers statements
// (branches, loops, matches), `expr.rs` expressions and builtins,
// `laws.rs` laws and their proofs.

mod body;
mod expr;
mod laws;

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::core::*;
use crate::ir::{self, Body, Def as IrDef, Param as IrParam, Term, Ty, TypeDef};
use crate::types::*;
use crate::Diag;

pub const PRELUDE: &str = include_str!("../prelude.bend");

/// How a def's result is wrapped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Pure,
    Result,
    Io,
}

impl Mode {
    pub fn of(e: Effect) -> Mode {
        if e.io {
            Mode::Io
        } else if e.abort {
            Mode::Result
        } else {
            Mode::Pure
        }
    }
    pub fn join(self, other: Mode) -> Mode {
        if other > self { other } else { self }
    }
    /// The Bend type of a result of type `t` in this mode.
    pub fn wrap(self, t: Ty) -> Ty {
        match self {
            Mode::Pure => t,
            Mode::Result => Ty::result(Ty::Str, t),
            Mode::Io => Ty::io(t),
        }
    }
}

/// How a function-typed parameter of a def is passed.
#[derive(Debug, Clone, PartialEq)]
pub enum FnParamKind {
    /// Not a function.
    Value,
    /// Only called or passed on: the code as a template parameter and its
    /// environment as a value.
    Template { code: String, env_ty: String, env: String },
    /// Stored, captured or returned: a closure value.
    Data,
}

/// A dictionary parameter of a def image.
#[derive(Debug, Clone)]
pub struct DictParam {
    pub id: ConstraintId,
    pub name: String,
    pub ty: Ty,
}

/// The Bend shape of a def.
#[derive(Debug, Clone)]
pub struct Image {
    pub name: String,
    /// Quantified type variables with their names.
    pub tparams: Vec<(TVar, String)>,
    /// Emitted with `~A` (a template) rather than `-A`.
    pub template: bool,
    pub dicts: Vec<DictParam>,
    pub fnp: Vec<FnParamKind>,
    /// The environment parameter: its type name and type.
    pub env: Option<(String, Ty)>,
    /// A leading `fuel: Nat` parameter.
    pub fuel: bool,
    /// Core parameter indices in image order.
    pub order: Vec<usize>,
    pub mode: Mode,
    pub params: Vec<Ty>,
    pub ret: Ty,
    /// The unit whose template parameters this def forwards (itself for a
    /// top-level def).
    pub unit: DefId,
}

pub struct Lower<'a> {
    pub core: &'a Program,
    pub laws: Laws,
    pub store: TypeStore,
    pub types: Vec<TypeDef>,
    pub defs: Vec<IrDef>,
    pub diags: Vec<Diag>,
    pub images: Vec<Option<Image>>,
    /// Per def: how each parameter is passed.
    pub fn_kinds: Vec<Vec<FnParamKind>>,
    pub emitted_types: HashSet<String>,
    pub emitted_defs: HashSet<String>,
    pub counter: usize,
    /// Image names of data types and defs.
    pub type_names: Vec<String>,
    pub def_names: Vec<String>,
    /// Per data type: the free variables among its parameters, in order,
    /// each with the parameter position it is read from.
    pub eff_params: Vec<Vec<(TVar, usize)>>,
    /// Closure sum types by member ids.
    pub sums: HashMap<Vec<DefId>, String>,
    /// Names already taken by Base or by emitted defs/types.
    pub taken: HashSet<String>,
    /// Derived defs emitted, by name.
    pub derived: HashSet<String>,
    /// Records of live-out values by arity.
    pub outs: HashSet<usize>,
    /// Image names of the constructors of declared types.
    pub ctor_names: Vec<Vec<String>>,
    /// The mode a higher-order builtin method's term came out in (set by
    /// `builtin_method`, read by `concrete_op`).
    pub hof_mode: Option<Mode>,
    /// Units whose type parameters are templates although no dictionary
    /// or function parameter asks for it: a template argument in their
    /// image mentions one (a loop driver's state type, say).
    pub force_template: HashSet<DefId>,
    /// The unit each emitted def (its body or a helper) belongs to.
    pub ir_units: HashMap<String, DefId>,
}

/// Which laws an image carries: a runnable program carries the ones the
/// compiler proves (a false one fails the build); `fire --check` carries
/// every law, the open ones as claims for Bend to report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Laws {
    Proven,
    All,
}

pub fn lower_program(core: &Program, laws: Laws) -> Result<ir::Program, Vec<Diag>> {
    // A unit's type parameters are erased unless something needs them at
    // compile time. Where a template argument of the image still mentions
    // an erased one, the unit is lowered again with template parameters;
    // its callers then pass types as templates, which may need the same.
    let mut force_template = HashSet::new();
    loop {
        let lw = lower_once(core, laws, force_template.clone());
        if !lw.diags.is_empty() {
            return Err(lw.diags);
        }
        let mut more = false;
        for d in &lw.defs {
            if d.erased.is_empty() {
                continue;
            }
            let mut used = std::collections::BTreeSet::new();
            d.body.template_params(&mut used);
            if d.erased.iter().any(|p| used.contains(p))
                && let Some(&unit) = lw.ir_units.get(&d.name)
                && force_template.insert(unit)
            {
                more = true;
            }
        }
        if !more {
            return Ok(ir::Program { types: lw.types, defs: lw.defs, raw_prelude: PRELUDE.to_string() });
        }
    }
}

fn lower_once(core: &Program, laws: Laws, force_template: HashSet<DefId>) -> Lower<'_> {
    let mut lw = Lower {
        laws,
        core,
        store: core.store.clone(),
        types: Vec::new(),
        defs: Vec::new(),
        diags: Vec::new(),
        images: vec![None; core.defs.len()],
        fn_kinds: vec![Vec::new(); core.defs.len()],
        emitted_types: HashSet::new(),
        emitted_defs: HashSet::new(),
        counter: 0,
        type_names: Vec::new(),
        def_names: Vec::new(),
        eff_params: Vec::new(),
        sums: HashMap::new(),
        taken: HashSet::new(),
        derived: HashSet::new(),
        outs: HashSet::new(),
        ctor_names: Vec::new(),
        hof_mode: None,
        force_template,
        ir_units: HashMap::new(),
    };
    lw.run();
    lw
}

/// Names Base declares that a user name must not shadow.
const BASE_NAMES: &[&str] = &[
    "Empty", "Unit", "Bool", "Cmp", "Either", "Sigma", "Nat", "Maybe", "Result", "List", "Word", "U32", "F32", "Char", "String", "Array", "Image",
    "Event", "Map", "File", "Socket", "Listener", "Window", "Audio", "Chan", "IO", "Pair", "App", "Set", "Exists", "Or", "Nil", "Con", "None", "Some",
    "Done", "Fail", "True", "False", "Zero", "Succ", "Inl", "Inr", "Tuple", "WNil", "WCon", "Chr", "SNil", "SCon", "ALeaf", "ANode", "Pix", "Qua",
    "Key", "Mouse", "Move", "Close", "MTip", "MLeaf", "MNode", "Emit", "Halt", "LT", "EQ", "GT", "main", "import", "law", "def", "type", "match", "case", "do", "return",
];

impl<'a> Lower<'a> {
    pub fn error(&mut self, line: usize, message: impl Into<String>) {
        self.diags.push(Diag { line, message: message.into() });
    }

    pub fn fresh(&mut self, hint: &str) -> String {
        self.counter += 1;
        format!("__{}{}", hint, self.counter)
    }

    // -- names ------------------------------------------------------------------------

    /// A verbatim user name, or one with a suffix when it collides.
    fn unique(&mut self, wanted: &str) -> String {
        let mut name = wanted.to_string();
        while self.taken.contains(&name) {
            name.push('_');
        }
        self.taken.insert(name.clone());
        name
    }

    fn run(&mut self) {
        for n in BASE_NAMES {
            self.taken.insert(n.to_string());
        }
        // types: verbatim names for declared types and classes
        for (id, t) in self.core.types.iter().enumerate() {
            let name = match t.kind {
                // the record {key, value} is the runtime's pair
                _ if id == PAIR => "F.Pair".to_string(),
                DataKind::Builtin => match id {
                    RANGE => "F.Range".to_string(),
                    _ => t.name.clone(),
                },
                DataKind::Record { .. } => format!("F.Rec.{}", t.ctors[0].fields.iter().map(|f| f.name.clone()).collect::<Vec<_>>().join("_")),
                _ => t.name.clone(),
            };
            let name = if id < BUILTIN_TYPES { name } else { self.unique(&name) };
            self.type_names.push(name);
        }
        // constructors of declared types keep their names, with a `_` suffix
        // where Base (or another type) already has the name
        self.ctor_names = vec![Vec::new(); self.core.types.len()];
        for (id, t) in self.core.types.iter().enumerate().skip(BUILTIN_TYPES) {
            if let DataKind::Declared = t.kind {
                let mut names = Vec::new();
                for c in &t.ctors {
                    let n = self.unique(&c.name);
                    names.push(n);
                }
                self.ctor_names[id] = names;
            }
        }
        // defs: verbatim for top-level, dotted for nested ones and lambdas
        let n = self.core.defs.len();
        self.def_names = vec![String::new(); n];
        for d in &self.core.defs {
            if d.unit == d.id && !matches!(d.kind, DefKind::Lambda | DefKind::Law) {
                let wanted = match &d.kind {
                    DefKind::Main => "main".to_string(),
                    DefKind::Ctor(tid) => format!("{}.F.new", self.type_names[*tid]),
                    DefKind::Method { rec, .. } => format!("{}.{}", self.type_names[*rec], method_name(&d.name)),
                    _ => d.name.clone(),
                };
                let name = if matches!(d.kind, DefKind::Main) { "main".to_string() } else { self.unique(&wanted) };
                self.def_names[d.id] = name;
            }
        }
        for d in &self.core.defs {
            if self.def_names[d.id].is_empty() && !matches!(d.kind, DefKind::Law) {
                let unit = self.def_names[d.unit].clone();
                let unit = if unit.is_empty() { "f".to_string() } else { unit };
                let name = self.unique(&format!("{}.{}", unit, d.name));
                self.def_names[d.id] = name;
            }
        }
        self.compute_eff_params();
        self.classify_fn_params();
        // a law has an image, never emitted, for the lambdas inside it
        for d in &self.core.defs {
            if self.images[d.id].is_none() {
                let image = self.make_image(d.id);
                self.images[d.id] = Some(image);
            }
        }
        // data types
        for id in BUILTIN_TYPES..self.core.types.len() {
            self.emit_type(id);
        }
        // defs
        for d in &self.core.defs {
            if matches!(d.kind, DefKind::Law) {
                continue;
            }
            self.emit_def(d.id);
        }
        self.emit_laws();
    }

    // -- types --------------------------------------------------------------------------

    /// The free variables among each data type's parameters, once, before
    /// any type is rendered.
    fn compute_eff_params(&mut self) {
        for t in &self.core.types {
            let mut eff: Vec<(TVar, usize)> = Vec::new();
            for (i, p) in t.params.iter().enumerate() {
                let r = self.store.resolve(&Type::Var(*p));
                let mut fv = Vec::new();
                self.store.free_vars(&r, &mut fv);
                for v in fv {
                    if !eff.iter().any(|(w, _)| *w == v) {
                        eff.push((v, i));
                    }
                }
            }
            self.eff_params.push(eff);
        }
    }

    /// The Bend type of a Fire type, naming variables through `names`
    /// (a def image's type parameters). An unnamed unresolved variable is
    /// `Unit`: nothing ever gave it a type.
    pub fn ty(&mut self, t: &Type, names: &[(TVar, String)], line: usize) -> Ty {
        match self.store.shallow(t) {
            Type::Var(v) => match names.iter().find(|(w, _)| *w == v) {
                Some((_, n)) => Ty::Param(n.clone()),
                None => Ty::Unit,
            },
            Type::Int => Ty::U32,
            Type::Float => Ty::F32,
            Type::Str => Ty::Str,
            Type::Bool => Ty::Bool,
            Type::Unit => Ty::Unit,
            Type::List(e) => Ty::list(self.ty(&e, names, line)),
            Type::Map(e) => Ty::map(self.ty(&e, names, line)),
            Type::Fn(ps, r, c) => {
                let full = Type::Fn(ps.clone(), r.clone(), c);
                self.closure_ty(&full, c, names, line)
            }
            Type::Data(MAYBE, args) => Ty::maybe(self.ty(&args[0], names, line)),
            Type::Data(RESULT, args) => {
                let e = self.ty(&args[0], names, line);
                let a = self.ty(&args[1], names, line);
                Ty::result(e, a)
            }
            Type::Data(id, args) => {
                let eff = self.eff_params[id].clone();
                let name = self.type_names[id].clone();
                let mut targs = Vec::new();
                for (v, i) in &eff {
                    let actual = self.instantiate_eff(id, *v, *i, &args);
                    targs.push(self.ty(&actual, names, line));
                }
                Ty::Named(name, targs)
            }
        }
    }

    /// The value of an effective parameter `v` (found inside parameter
    /// `i`'s resolved type) under the arguments of a use site.
    fn instantiate_eff(&self, id: TypeId, v: TVar, i: usize, args: &[Type]) -> Type {
        let pattern = self.store.resolve(&Type::Var(self.core.types[id].params[i]));
        let actual = args.get(i).cloned().unwrap_or(Type::Unit);
        let mut m: HashMap<TVar, Type> = HashMap::new();
        self.match_type(&pattern, &actual, &mut m);
        m.get(&v).cloned().unwrap_or(Type::Unit)
    }

    /// One-way structural match of a type with variables against an actual
    /// type.
    fn match_type(&self, pattern: &Type, actual: &Type, out: &mut HashMap<TVar, Type>) {
        match (self.store.shallow(pattern), self.store.shallow(actual)) {
            (Type::Var(v), a) => {
                out.entry(v).or_insert(a);
            }
            (Type::List(p), Type::List(a)) | (Type::Map(p), Type::Map(a)) => self.match_type(&p, &a, out),
            (Type::Fn(ps, r, _), Type::Fn(qs, s, _)) => {
                for (p, q) in ps.iter().zip(qs.iter()) {
                    self.match_type(p, q, out);
                }
                self.match_type(&r, &s, out);
            }
            (Type::Data(_, ps), Type::Data(_, qs)) => {
                for (p, q) in ps.iter().zip(qs.iter()) {
                    self.match_type(p, q, out);
                }
            }
            _ => {}
        }
    }

    /// Emit a data type: its effective parameters and the fields of its
    /// constructors.
    fn emit_type(&mut self, id: TypeId) {
        let t = self.core.types[id].clone();
        let name = self.type_names[id].clone();
        if self.emitted_types.contains(&name) {
            return;
        }
        self.emitted_types.insert(name.clone());
        let names: Vec<(TVar, String)> = self.eff_params[id].iter().enumerate().map(|(k, (v, _))| (*v, tparam_name(k))).collect();
        let mut ctors = Vec::new();
        for (ci, c) in t.ctors.iter().enumerate() {
            let cname = self.ctor_name(id, ci);
            let fields = c.fields.iter().map(|f| (field_name(&f.name), self.ty(&f.ty, &names, t.line))).collect();
            ctors.push((cname, fields));
        }
        self.types.push(TypeDef { name, params: names.iter().map(|(_, n)| n.clone()).collect(), ctors });
    }

    /// The Bend constructor name of a data type's constructor.
    pub fn ctor_name(&self, id: TypeId, ci: usize) -> String {
        let t = &self.core.types[id];
        match t.kind {
            DataKind::Builtin => t.ctors[ci].name.clone(),
            DataKind::Declared => self.ctor_names[id][ci].clone(),
            _ => self.type_names[id].clone(),
        }
    }

    // -- closures -------------------------------------------------------------------------

    /// The Bend type of a function value: the environment record of the one
    /// def that can flow into it, or a sum over several.
    pub fn closure_ty(&mut self, fn_ty: &Type, c: ClosVar, names: &[(TVar, String)], line: usize) -> Ty {
        let set: Vec<DefId> = self.store.clos_set(c).into_iter().collect();
        match set.len() {
            0 => Ty::Unit,
            1 => self.env_ty(set[0], Some(fn_ty), names, line),
            _ => {
                let name = self.sum_type(&set, line);
                Ty::Named(name, vec![])
            }
        }
    }

    /// The environment record type of a def used as a value, applied to the
    /// unit's type parameters as the use site fixes them: the def's function
    /// type matched against the type at the use site (`use_ty`).
    pub fn env_ty(&mut self, d: DefId, use_ty: Option<&Type>, names: &[(TVar, String)], line: usize) -> Ty {
        let def = self.core.defs[d].clone();
        if def.captures.is_empty() {
            return Ty::Unit;
        }
        let type_name = format!("F.Env.{}", self.def_names[d]);
        let unit_params = self.unit_tparams(def.unit);
        let bindings = self.closure_bindings(d, use_ty);
        let mut args = Vec::new();
        for (v, _) in &unit_params {
            let known = bindings.contains_key(v) || names.iter().any(|(w, _)| w == v);
            if !known && def.captures.iter().any(|(_, t)| self.store.mentions(t, *v)) {
                self.error(line, format!("the function value made by {} captures a value of a type its own type does not mention; it cannot leave its def", self.core.defs[def.unit].name));
            }
            let actual = bindings.get(v).cloned().unwrap_or(Type::Var(*v));
            args.push(self.ty(&actual, names, line));
        }
        self.emit_env_type(d, &type_name, &unit_params, line);
        Ty::Named(type_name, args)
    }

    /// How a use site of a closure fixes its unit's type parameters: the
    /// def's function type matched against the type there (inside the unit
    /// every parameter maps to itself).
    pub fn closure_bindings(&self, d: DefId, use_ty: Option<&Type>) -> HashMap<TVar, Type> {
        let mut out = HashMap::new();
        if let Some(u) = use_ty {
            let pattern = self.core.defs[d].scheme.ty.clone();
            self.match_type(&pattern, u, &mut out);
        }
        out
    }

    /// Some value of a Bend type, for a branch the checker proved dead.
    pub fn default_of_ty(&mut self, ty: &Ty, line: usize) -> Term {
        match ty {
            Ty::U32 => Term::U32(0),
            Ty::F32 => Term::F32(0.0),
            Ty::Str => Term::Str(String::new()),
            Ty::Bool => Term::boolean(false),
            Ty::Unit => Term::unit(),
            Ty::Nat => Term::Nat(0),
            Ty::Char => Term::Chr(' '),
            Ty::List(_) => Term::List(vec![]),
            Ty::Maybe(_) => Term::ctor("None", vec![]),
            Ty::Result(_, a) => {
                let v = self.default_of_ty(a, line);
                Term::ctor("Done", vec![v])
            }
            Ty::Map(v) => Term::call("Map.new", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg((**v).clone())]),
            Ty::Io(t) => {
                let v = self.default_of_ty(t, line);
                Term::call("IO.pure", vec![Term::TyArg((**t).clone()), v])
            }
            Ty::Tuple(a, b) => {
                let x = self.default_of_ty(a, line);
                let y = self.default_of_ty(b, line);
                Term::Tuple(Box::new(x), Box::new(y))
            }
            Ty::Named(n, args) => {
                // the first constructor of the emitted type, its fields defaulted
                let found = self.types.iter().find(|t| &t.name == n).cloned();
                match found {
                    Some(td) => {
                        let subst: Vec<(String, Ty)> = td.params.iter().cloned().zip(args.iter().cloned()).collect();
                        let (cname, fields) = td.ctors.iter().min_by_key(|(_, f)| f.len()).cloned().unwrap();
                        let vals: Vec<Term> = fields.iter().map(|(_, ft)| {
                            let ft = ft.subst_params(&subst);
                            self.default_of_ty(&ft, line)
                        }).collect();
                        Term::Ctor(cname, vals)
                    }
                    None => match n.as_str() {
                        "F.Pair" => {
                            let x = self.default_of_ty(&args[0], line);
                            let y = self.default_of_ty(&args[1], line);
                            Term::ctor("F.Pair", vec![x, y])
                        }
                        "F.Range" => Term::ctor("F.Range", vec![Term::U32(0), Term::U32(0)]),
                        "F.Ctl" => {
                            let x = self.default_of_ty(&args[0], line);
                            Term::ctor("F.Next", vec![x])
                        }
                        _ => {
                            self.error(line, format!("internal: no default value for {}", n));
                            Term::unit()
                        }
                    },
                }
            }
            Ty::Fn(..) | Ty::Param(_) => {
                self.error(line, "internal: no default value for a function or a type parameter");
                Term::unit()
            }
        }
    }

    /// A dictionary for a class on a type at this point: a dictionary
    /// parameter of the current def when the type is one of its variables,
    /// else a fresh solved constraint (the operation is derived from the
    /// type alone).
    pub fn dict_for_id(&mut self, ctx: &body::FnCtx, class: Class, subject: Type, line: usize) -> Option<ConstraintId> {
        if let Type::Var(v) = self.store.shallow(&subject) {
            for dp in &ctx.dicts {
                let c = &self.store.constraints[dp.id];
                if same_class(&c.class, &class) && matches!(self.store.shallow(&c.subject), Type::Var(w) if w == v) {
                    return Some(dp.id);
                }
            }
            self.error(line, format!("{} on a value of a type this def does not fix is not available here", crate::check::describe_class(&class)));
            return None;
        }
        let id = self.store.constraints.len();
        self.store.constraints.push(Constraint { class, subject, line, solution: Some(Solution::Concrete(vec![])), owner: ctx.unit, user: ctx.unit });
        Some(id)
    }

    pub fn dict_for(&mut self, ctx: &body::FnCtx, class: Class, subject: Type, line: usize) -> Term {
        match self.dict_for_id(ctx, class, subject, line) {
            Some(id) => self.dict_term(ctx, id, line),
            None => Term::unit(),
        }
    }

    fn emit_env_type(&mut self, d: DefId, type_name: &str, unit_params: &[(TVar, String)], line: usize) {
        if self.emitted_types.contains(type_name) {
            return;
        }
        self.emitted_types.insert(type_name.to_string());
        let caps = self.core.defs[d].captures.clone();
        let mut fields = Vec::new();
        for (n, t) in &caps {
            let ft = match self.capture_kind(d, n) {
                Some(FnParamKind::Template { env_ty, .. }) => Ty::Param(env_ty),
                _ => self.ty(t, unit_params, line),
            };
            fields.push((field_name(n), ft));
        }
        self.types.push(TypeDef { name: type_name.to_string(), params: unit_params.iter().map(|(_, n)| n.clone()).collect(), ctors: vec![(type_name.to_string(), fields)] });
    }

    /// A captured name that is a template function parameter of the unit:
    /// the closure captures its environment and forwards its code.
    fn capture_kind(&self, d: DefId, name: &str) -> Option<FnParamKind> {
        let unit = self.core.defs[d].unit;
        let img = self.images[unit].as_ref()?;
        let udef = &self.core.defs[unit];
        let i = udef.params.iter().position(|p| p.name == name)?;
        match &img.fnp[i] {
            k @ FnParamKind::Template { .. } => Some(k.clone()),
            _ => None,
        }
    }

    /// The sum type over several closures, with its apply def.
    fn sum_type(&mut self, set: &[DefId], line: usize) -> String {
        if let Some(n) = self.sums.get(set) {
            return n.clone();
        }
        self.counter += 1;
        let name = format!("F.Fn{}", self.counter);
        self.sums.insert(set.to_vec(), name.clone());
        let mut ctors = Vec::new();
        for d in set {
            let et = self.env_ty(*d, None, &[], line);
            if let Ty::Named(_, args) = &et
                && !args.is_empty() {
                    let dn = self.def_names[*d].clone();
                    self.error(line, format!("the function {} captures values of a generic type and cannot be mixed with other functions in one value", dn));
                }
            ctors.push((format!("{}.{}", name, self.def_names[*d].replace('.', "_")), vec![("env".to_string(), et)]));
        }
        self.types.push(TypeDef { name: name.clone(), params: vec![], ctors });
        // the apply def: match the sum and call the member's code
        let (ptys, rty, mode) = self.member_signature(set[0], line);
        let mut arms = Vec::new();
        for d in set {
            let (dp, dr, dm) = self.member_signature(*d, line);
            let _ = (dp, dr, dm);
            let cname = format!("{}.{}", name, self.def_names[*d].replace('.', "_"));
            // a sum may be built while an earlier def's image is made (its
            // parameter holds functions a later lambda flows into)
            if self.images[*d].is_none() {
                let image = self.make_image(*d);
                self.images[*d] = Some(image);
            }
            let img = self.images[*d].clone().unwrap();
            if !img.tparams.is_empty() || !img.dicts.is_empty() {
                self.error(line, format!("the function {} belongs to a generic def and cannot be stored with other functions in one value", self.def_names[*d]));
            }
            let mut args = Vec::new();
            if img.env.is_some() {
                args.push(Term::var("env"));
            }
            // values in image order (a structural def puts its descending
            // parameter first)
            for &i in &img.order {
                args.push(Term::var(&format!("a{}", i)));
            }
            let callee = if img.fuel { self.fuel_entry(*d) } else { img.name.clone() };
            let call = Term::Call(callee, args);
            // the sum answers in the join mode of its members
            let call = self.lift_mode(call, img.mode, mode, &rty);
            arms.push((ir::Pat::Ctor(cname, vec![("env".to_string(), false)]), Body::term(call)));
        }
        let mut params = vec![IrParam { name: "f".into(), reusable: false, ty: Ty::Named(name.clone(), vec![]) }];
        for (i, t) in ptys.iter().enumerate() {
            params.push(IrParam { name: format!("a{}", i), reusable: false, ty: t.clone() });
        }
        let apply = IrDef {
            name: format!("{}.call", name),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            erased_types: vec![],
            params,
            ret: mode.wrap(rty),
            body: Body::Match { scrutinee: "f".into(), arms },
        };
        self.defs.push(apply);
        name
    }

    /// The parameter and return types of a closure member, and its mode.
    fn member_signature(&mut self, d: DefId, line: usize) -> (Vec<Ty>, Ty, Mode) {
        let def = &self.core.defs[d];
        let ptys: Vec<Type> = def.params.iter().map(|p| p.ty.clone()).collect();
        let ret = def.ret.clone();
        let mode = Mode::of(def.effect);
        let ps = ptys.iter().map(|t| self.ty(t, &[], line)).collect();
        let r = self.ty(&ret, &[], line);
        (ps, r, mode)
    }

    /// The join mode of every member of a closure set: what a call of a
    /// function value may do.
    pub fn closure_mode(&self, c: ClosVar) -> Mode {
        let mut m = Mode::Pure;
        for d in self.store.clos_set(c) {
            if d < self.core.defs.len() {
                m = m.join(Mode::of(self.core.defs[d].effect));
            }
        }
        m
    }

    /// A term of mode `from` used where mode `to` is expected: pure values
    /// are wrapped, results inside IO are unwrapped.
    pub fn lift_mode(&mut self, t: Term, from: Mode, to: Mode, ty: &Ty) -> Term {
        match (from, to) {
            (a, b) if a == b => t,
            (Mode::Pure, Mode::Result) => Term::ctor("Done", vec![t]),
            (Mode::Pure, Mode::Io) => Term::call("IO.pure", vec![Term::TyArg(ty.clone()), t]),
            (Mode::Result, Mode::Io) => Term::call("F.io_unwrap", vec![Term::TyArg(ty.clone()), t]),
            _ => t,
        }
    }

    // -- images -------------------------------------------------------------------------------

    /// The type parameters of a unit: its scheme's variables, named A, B, ...
    pub fn unit_tparams(&self, unit: DefId) -> Vec<(TVar, String)> {
        let d = &self.core.defs[unit];
        d.scheme.vars.iter().enumerate().map(|(i, v)| (*v, tparam_name(i))).collect()
    }

    /// Decide, for every function-typed parameter of every def, whether it
    /// is passed as code plus environment or as a value: a fixpoint,
    /// since a parameter passed to another def's value parameter must be a
    /// value itself.
    fn classify_fn_params(&mut self) {
        let n = self.core.defs.len();
        let mut kinds: Vec<Vec<bool>> = Vec::new(); // true = template
        for d in &self.core.defs {
            let top = d.unit == d.id && matches!(d.kind, DefKind::Plain | DefKind::Method { .. } | DefKind::Ctor(_));
            kinds.push(d.params.iter().map(|p| top && matches!(self.store.shallow(&p.ty), Type::Fn(..))).collect());
        }
        let mut changed = true;
        while changed {
            changed = false;
            for d in 0..n {
                let def = &self.core.defs[d];
                for (i, p) in def.params.iter().enumerate() {
                    if !kinds[d][i] {
                        continue;
                    }
                    if !self.only_called(def, &p.name, &kinds) {
                        kinds[d][i] = false;
                        changed = true;
                    }
                }
            }
        }
        let mut out = Vec::new();
        for d in 0..n {
            let def = &self.core.defs[d];
            let mut v = Vec::new();
            for (i, p) in def.params.iter().enumerate() {
                let is_fn = matches!(self.store.shallow(&p.ty), Type::Fn(..));
                v.push(if !is_fn {
                    FnParamKind::Value
                } else if kinds[d][i] {
                    FnParamKind::Template { code: format!("f_{}", p.name), env_ty: format!("E_{}", p.name), env: format!("env_{}", p.name) }
                } else {
                    FnParamKind::Data
                });
            }
            out.push(v);
        }
        self.fn_kinds = out;
    }

    /// Whether a function parameter is used only in call position or as an
    /// argument to a template parameter of another def or to a builtin.
    fn only_called(&self, def: &Def, name: &str, kinds: &[Vec<bool>]) -> bool {
        let mut ok = true;
        let check_arg = |a: &Expr, callee_template: bool, ok: &mut bool| {
            if let ExprKind::Var(v) = &a.kind
                && v == name && !callee_template {
                    *ok = false;
                }
        };
        walk_block(&def.body, &mut |e: &Expr| {
            match &e.kind {
                ExprKind::Var(v) if v == name => {
                    // a bare use: only allowed as a call target or argument,
                    // which the parent handles; a bare reference elsewhere is
                    // a stored value. We detect the good cases below and
                    // count every other occurrence.
                }
                ExprKind::CallClosure(f, args) => {
                    if !matches!(&f.kind, ExprKind::Var(v) if v == name) {
                        check_arg(f, false, &mut ok);
                    }
                    for a in args {
                        check_arg(a, false, &mut ok);
                    }
                }
                ExprKind::Call { def: callee, args, .. } => {
                    for (i, a) in args.iter().enumerate() {
                        let ct = kinds.get(*callee).and_then(|k| k.get(i)).cloned().unwrap_or(false);
                        check_arg(a, ct, &mut ok);
                    }
                }
                ExprKind::Dict { args, .. } => {
                    // builtin higher-order methods take code and environment
                    for (i, a) in args.iter().enumerate() {
                        check_arg(a, i > 0, &mut ok);
                    }
                }
                ExprKind::Builtin(_, args) | ExprKind::List(args) | ExprKind::Con(_, _, args) => {
                    for a in args {
                        check_arg(a, false, &mut ok);
                    }
                }
                ExprKind::SetField(o, _, _, v) => {
                    check_arg(o, false, &mut ok);
                    check_arg(v, false, &mut ok);
                }
                ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => check_arg(o, false, &mut ok),
                ExprKind::If(c, t, el) => {
                    check_arg(c, false, &mut ok);
                    check_arg(t, false, &mut ok);
                    check_arg(el, false, &mut ok);
                }
                ExprKind::Match(s, arms) => {
                    check_arg(s, false, &mut ok);
                    for a in arms {
                        check_arg(&a.body, false, &mut ok);
                    }
                }
                ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                    check_arg(a, false, &mut ok);
                    check_arg(b, false, &mut ok);
                }
                ExprKind::FString(parts) => {
                    for p in parts {
                        if let FPart::Expr(x, _) = p {
                            check_arg(x, false, &mut ok);
                        }
                    }
                }
                ExprKind::Var(_) | ExprKind::Block(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => {}
            }
        });
        // statements: a let or return of the bare parameter stores it
        for_each_stmt(&def.body, &mut |s: &Stmt| match &s.kind {
            StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Return(value) | StmtKind::Expr(value) => {
                if matches!(&value.kind, ExprKind::Var(v) if v == name) {
                    ok = false;
                }
            }
            _ => {}
        });
        // captured by a lambda inside the def: a value (the lambda's
        // environment holds it), unless the lambda only calls it, which is
        // handled by forwarding the code
        ok
    }

    fn make_image(&mut self, d: DefId) -> Image {
        let def = &self.core.defs[d];
        let line = def.line;
        let unit = def.unit;
        let tparams = self.unit_tparams(unit);
        let udef = &self.core.defs[unit];
        let mode = Mode::of(def.effect);
        // dictionaries: the unit's, with names
        let mut dicts = Vec::new();
        let dict_ids = udef.scheme.dicts.clone();
        for (k, id) in dict_ids.iter().enumerate() {
            let c = self.store.constraints[*id].clone();
            let name = dict_param_name(&c.class, k);
            let ty = self.dict_param_ty(&c, &tparams, line);
            dicts.push(DictParam { id: *id, name, ty });
        }
        let fnp = self.fn_kinds[d].clone();
        // the unit's template function parameters are forwarded by lambdas
        let template = !dicts.is_empty()
            || fnp.iter().any(|k| matches!(k, FnParamKind::Template { .. }))
            || self.fn_kinds[unit].iter().any(|k| matches!(k, FnParamKind::Template { .. }))
            || self.force_template.contains(&unit);
        let env = if def.captures.is_empty() {
            None
        } else {
            let tn = format!("F.Env.{}", self.def_names[d]);
            let ty = Ty::Named(tn.clone(), tparams.iter().map(|(_, n)| Ty::Param(n.clone())).collect());
            self.emit_env_type(d, &tn, &tparams, line);
            Some((tn, ty))
        };
        let (order, fuel) = match def.descent {
            Descent::Structural(ref lex) => {
                let mut o = lex.clone();
                o.extend((0..def.params.len()).filter(|j| !lex.contains(j)));
                (o, false)
            }
            Descent::Fuel(_) => ((0..def.params.len()).collect(), true),
            _ => ((0..def.params.len()).collect(), false),
        };
        let params: Vec<Ty> = def.params.iter().map(|p| self.ty(&p.ty.clone(), &tparams, line)).collect();
        let ret = self.ty(&def.ret.clone(), &tparams, line);
        Image { name: self.def_names[d].clone(), tparams, template, dicts, fnp, env, fuel, order, mode, params, ret, unit }
    }

    /// The Bend type of a dictionary parameter: the operation the class
    /// provides on its subject.
    fn dict_param_ty(&mut self, c: &Constraint, names: &[(TVar, String)], line: usize) -> Ty {
        let s = self.ty(&c.subject, names, line);
        match &c.class {
            Class::Eq | Class::Ord => Ty::func(vec![s.clone(), s], Ty::Bool),
            Class::Show => Ty::func(vec![s], Ty::Str),
            Class::Arith(ArithOp::Neg) => Ty::func(vec![s.clone()], s),
            Class::Arith(_) => Ty::func(vec![s.clone(), s.clone()], s),
            Class::OrElse(r, ret) => {
                let r = self.ty(r, names, line);
                let ret = self.ty(ret, names, line);
                Ty::func(vec![s, r], ret)
            }
            Class::Len => Ty::func(vec![s], Ty::U32),
            Class::Zero => s,
            Class::Iter(e) => {
                let e = self.ty(e, names, line);
                Ty::func(vec![s], Ty::list(e))
            }
            Class::Index(i, e) => {
                let i = self.ty(i, names, line);
                let e = self.ty(e, names, line);
                Ty::func(vec![s, i], Ty::result(Ty::Str, e))
            }
            Class::IndexSet(i, v) => {
                let i = self.ty(i, names, line);
                let v = self.ty(v, names, line);
                Ty::func(vec![s.clone(), i, v], Ty::result(Ty::Str, s))
            }
            Class::Field(_, t) => {
                let t = self.ty(t, names, line);
                Ty::func(vec![s], t)
            }
            Class::SetField(_, t) => {
                let t = self.ty(t, names, line);
                Ty::func(vec![s.clone(), t], s)
            }
            Class::Method(_, args, ret) => {
                let mut ps = vec![s];
                for a in args {
                    ps.push(self.ty(a, names, line));
                }
                let r = self.ty(ret, names, line);
                Ty::func(ps, Ty::result(Ty::Str, r))
            }
            Class::Convert(_, t) => {
                let t = self.ty(t, names, line);
                Ty::func(vec![s], Ty::result(Ty::Str, t))
            }
        }
    }

    // -- defs -----------------------------------------------------------------------------------

    fn emit_def(&mut self, d: DefId) {
        let def = self.core.defs[d].clone();
        let img = self.images[d].clone().unwrap();
        let line = def.line;
        if self.emitted_defs.contains(&img.name) {
            return;
        }
        self.emitted_defs.insert(img.name.clone());
        // the body
        let mut ctx = body::FnCtx::new(d, &img);
        let body = self.lower_def_body(&mut ctx, &def, &img);
        let mut ir_def = self.def_header(&img, &def, line);
        ir_def.body = body;
        ir_def.is_unsafe = def.unsafe_ && !matches!(def.kind, DefKind::Lambda);
        // lambdas of an unsafe def are unsafe too when they recurse (they cannot)
        self.mark_reusable(&mut ir_def);
        self.ir_units.insert(ir_def.name.clone(), def.unit);
        self.defs.push(ir_def);
    }

    /// The header of a def: its template, erased and value parameters.
    pub fn def_header(&mut self, img: &Image, def: &Def, line: usize) -> IrDef {
        let mut tmpl_types = Vec::new();
        let mut erased = Vec::new();
        for (_, n) in &img.tparams {
            if img.template {
                tmpl_types.push(n.clone());
            } else {
                erased.push(n.clone());
            }
        }
        let mut tmpl_funcs = Vec::new();
        for dp in &img.dicts {
            tmpl_funcs.push((dp.name.clone(), dp.ty.clone()));
        }
        // template function parameters: the unit's (forwarded by lambdas) or its own
        let owner = if def.unit == def.id { def.id } else { def.unit };
        let owner_img = self.images[owner].clone().unwrap();
        let owner_def = self.core.defs[owner].clone();
        for (i, k) in owner_img.fnp.iter().enumerate() {
            if let FnParamKind::Template { code, env_ty, .. } = k {
                tmpl_types.push(env_ty.clone());
                let fty = self.template_code_ty(&owner_def.params[i].ty, env_ty, &img.tparams, line);
                tmpl_funcs.push((code.clone(), fty));
            }
        }
        let mut params = Vec::new();
        if img.fuel {
            params.push(IrParam { name: "__fuel".into(), reusable: false, ty: Ty::Nat });
        }
        if let Some((_, ety)) = &img.env {
            params.push(IrParam { name: "env".into(), reusable: false, ty: ety.clone() });
        }
        for &i in &img.order {
            let p = &def.params[i];
            match &img.fnp[i] {
                FnParamKind::Template { env_ty, env, .. } => {
                    params.push(IrParam { name: env.clone(), reusable: false, ty: Ty::Param(env_ty.clone()) });
                }
                _ => params.push(IrParam { name: local_name(&p.name), reusable: false, ty: img.params[i].clone() }),
            }
        }
        IrDef { name: img.name.clone(), is_unsafe: false, tmpl_types, tmpl_funcs, erased, erased_types: vec![], params, ret: img.mode.wrap(img.ret.clone()), body: Body::term(Term::unit()) }
    }

    /// The type of a template code parameter: environment, then the
    /// function's parameters, answering in the function's mode.
    fn template_code_ty(&mut self, fty: &Type, env_ty: &str, names: &[(TVar, String)], line: usize) -> Ty {
        match self.store.shallow(fty) {
            Type::Fn(ps, r, c) => {
                let mut params = vec![Ty::Param(env_ty.to_string())];
                for p in &ps {
                    params.push(self.ty(p, names, line));
                }
                let mode = self.closure_mode(c);
                let r = self.ty(&r, names, line);
                Ty::func(params, mode.wrap(r))
            }
            _ => Ty::Unit,
        }
    }

    /// Mark parameters and lets used more than once as reusable (`+`).
    pub fn mark_reusable(&mut self, d: &mut IrDef) {
        d.body.mark_reusable_lambdas();
        let mut counts: HashMap<String, usize> = HashMap::new();
        d.body.count_vars(&mut counts);
        for p in &mut d.params {
            if counts.get(&p.name).cloned().unwrap_or(0) > 1 {
                p.reusable = true;
            }
        }
        mark_body(&mut d.body, &counts);
    }

    // -- derived defs ---------------------------------------------------------------------------

    /// A def that counts an int down, used as a value: `fact.F.value(n)`
    /// takes the def's parameters without the fuel and starts it.
    pub fn fuel_entry(&mut self, d: DefId) -> String {
        let img = self.images[d].clone().unwrap();
        let name = format!("{}.F.value", img.name);
        if self.derived.insert(name.clone()) {
            let def = self.core.defs[d].clone();
            let mut ir_def = self.def_header(&img, &def, def.line);
            ir_def.name = name.clone();
            ir_def.params.retain(|p| p.name != "__fuel");
            let mut args: Vec<Term> = ir_def.tmpl_types.iter().map(|t| Term::TmplTy(Ty::Param(t.clone()))).collect();
            args.extend(ir_def.tmpl_funcs.iter().map(|(f, _)| Term::TmplRef(f.clone())));
            args.extend(ir_def.erased.iter().map(|t| Term::TyArg(Ty::Param(t.clone()))));
            if let Descent::Fuel(i) = def.descent {
                args.push(Term::call("F.i32.fuel", vec![Term::var(&local_name(&def.params[i].name))]));
            }
            args.extend(ir_def.params.iter().map(|p| Term::var(&p.name)));
            ir_def.body = Body::term(Term::Call(img.name.clone(), args));
            self.mark_reusable(&mut ir_def);
            self.defs.push(ir_def);
        }
        name
    }

    /// A record type holding `n` live-out values of a branch.
    pub fn out_type(&mut self, n: usize) -> String {
        let name = format!("F.Out{}", n);
        if self.outs.insert(n) {
            let params: Vec<String> = (0..n).map(|i| format!("T{}", i)).collect();
            let fields = (0..n).map(|i| (format!("v{}", i), Ty::Param(format!("T{}", i)))).collect();
            self.types.push(TypeDef { name: name.clone(), params: params.clone(), ctors: vec![(name.clone(), fields)] });
            for i in 0..n {
                let mut erased = params.clone();
                let _ = &mut erased;
                self.defs.push(IrDef {
                    name: format!("{}.v{}", name, i),
                    is_unsafe: false,
                    tmpl_types: vec![],
                    tmpl_funcs: vec![],
                    erased: params.clone(),
                    erased_types: vec![],
                    params: vec![IrParam { name: "r".into(), reusable: false, ty: Ty::Named(name.clone(), params.iter().map(|p| Ty::Param(p.clone())).collect()) }],
                    ret: Ty::Param(format!("T{}", i)),
                    body: Body::Match {
                        scrutinee: "r".into(),
                        arms: vec![(ir::Pat::Ctor(name.clone(), (0..n).map(|j| (format!("v{}", j), false)).collect()), Body::term(Term::var(&format!("v{}", i))))],
                    },
                });
            }
        }
        name
    }

    /// A field accessor of a data type (constructor 0): `Type.get_field`.
    pub fn getter(&mut self, tid: TypeId, idx: usize) -> String {
        let t = self.core.types[tid].clone();
        let tname = self.type_names[tid].clone();
        let fname = field_name(&t.ctors[0].fields[idx].name);
        let name = match t.kind {
            _ if tid == PAIR => return if idx == 0 { "F.pair.key".into() } else { "F.pair.value".into() },
            DataKind::Builtin if tid == RANGE => return if idx == 0 { "F.range.start".into() } else { "F.range.end".into() },
            _ => format!("{}.F.get_{}", tname, fname),
        };
        if self.derived.insert(name.clone()) {
            let params: Vec<String> = (0..self.eff_params[tid].len()).map(tparam_name).collect();
            let selft = Ty::Named(tname.clone(), params.iter().map(|p| Ty::Param(p.clone())).collect());
            let names: Vec<(TVar, String)> = self.eff_params[tid].iter().enumerate().map(|(k, (v, _))| (*v, tparam_name(k))).collect();
            let fty = self.ty(&t.ctors[0].fields[idx].ty, &names, t.line);
            let fields: Vec<(String, bool)> = t.ctors[0].fields.iter().map(|f| (field_name(&f.name), false)).collect();
            self.defs.push(IrDef {
                name: name.clone(),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased: params,
                erased_types: vec![],
                params: vec![IrParam { name: "self_".into(), reusable: false, ty: selft }],
                ret: fty,
                body: Body::Match { scrutinee: "self_".into(), arms: vec![(ir::Pat::Ctor(self.ctor_name(tid, 0), fields.clone()), Body::term(Term::var(&fields[idx].0)))] },
            });
        }
        name
    }

    /// A field replacer of a data type: `Type.set_field(self, v)`.
    pub fn setter(&mut self, tid: TypeId, idx: usize) -> String {
        let t = self.core.types[tid].clone();
        let tname = self.type_names[tid].clone();
        let fname = field_name(&t.ctors[0].fields[idx].name);
        let name = format!("{}.F.set_{}", tname, fname);
        if self.derived.insert(name.clone()) {
            let params: Vec<String> = (0..self.eff_params[tid].len()).map(tparam_name).collect();
            let selft = Ty::Named(tname.clone(), params.iter().map(|p| Ty::Param(p.clone())).collect());
            let names: Vec<(TVar, String)> = self.eff_params[tid].iter().enumerate().map(|(k, (v, _))| (*v, tparam_name(k))).collect();
            let fty = self.ty(&t.ctors[0].fields[idx].ty, &names, t.line);
            let fields: Vec<(String, bool)> = t.ctors[0].fields.iter().map(|f| (field_name(&f.name), false)).collect();
            let rebuilt = Term::Ctor(self.ctor_name(tid, 0), fields.iter().enumerate().map(|(j, (f, _))| if j == idx { Term::var("v") } else { Term::var(f) }).collect());
            self.defs.push(IrDef {
                name: name.clone(),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased: params,
                erased_types: vec![],
                params: vec![IrParam { name: "self_".into(), reusable: false, ty: selft.clone() }, IrParam { name: "v".into(), reusable: false, ty: fty }],
                ret: selft,
                body: Body::Match { scrutinee: "self_".into(), arms: vec![(ir::Pat::Ctor(self.ctor_name(tid, 0), fields), Body::term(rebuilt))] },
            });
        }
        name
    }

    /// The case eliminator of a data type: one thunk per constructor,
    /// answering `R`. Used to match on a computed value.
    pub fn eliminator(&mut self, tid: TypeId) -> String {
        let t = self.core.types[tid].clone();
        let tname = self.type_names[tid].clone();
        let name = match tid {
            MAYBE => "F.maybe.case".to_string(),
            RESULT => "F.result.case".to_string(),
            _ => format!("{}.F.case", tname),
        };
        if tid == MAYBE || tid == RESULT {
            return name;
        }
        if self.derived.insert(name.clone()) {
            let params: Vec<String> = (0..self.eff_params[tid].len()).map(tparam_name).collect();
            let selft = Ty::Named(tname.clone(), params.iter().map(|p| Ty::Param(p.clone())).collect());
            let names: Vec<(TVar, String)> = self.eff_params[tid].iter().enumerate().map(|(k, (v, _))| (*v, tparam_name(k))).collect();
            let mut ps = vec![IrParam { name: "x".into(), reusable: false, ty: selft }];
            let mut arms = Vec::new();
            for (ci, c) in t.ctors.iter().enumerate() {
                let ftys: Vec<Ty> = c.fields.iter().map(|f| self.ty(&f.ty, &names, t.line)).collect();
                let kty = if ftys.is_empty() { Ty::func(vec![Ty::Unit], Ty::Param("R".into())) } else { Ty::func(ftys.clone(), Ty::Param("R".into())) };
                let kname = format!("k{}", ci);
                ps.push(IrParam { name: kname.clone(), reusable: false, ty: kty });
                let fields: Vec<(String, bool)> = c.fields.iter().enumerate().map(|(j, _)| (format!("f{}", j), false)).collect();
                let args: Vec<Term> = if fields.is_empty() { vec![Term::unit()] } else { fields.iter().map(|(f, _)| Term::var(f)).collect() };
                arms.push((ir::Pat::Ctor(self.ctor_name(tid, ci), fields), Body::term(Term::CallVar(kname, args))));
            }
            // the answer may be an `IO(..)`, a type that is not data
            self.defs.push(IrDef { name: name.clone(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: params, erased_types: vec!["R".into()], params: ps, ret: Ty::Param("R".into()), body: Body::Match { scrutinee: "x".into(), arms } });
        }
        name
    }

    /// A derived structural def (`show`, `eq`, `lt`, `default`) of a data
    /// type, a template over the operations of its type parameters.
    pub fn derived_def(&mut self, kind: &str, tid: TypeId, line: usize) -> String {
        let t = self.core.types[tid].clone();
        let tname = self.type_names[tid].clone();
        let name = match tid {
            MAYBE => return format!("F.maybe.{}", kind),
            RESULT => return format!("F.result.{}", kind),
            PAIR => return format!("F.pair.{}", kind),
            RANGE => return format!("F.range.{}", kind),
            _ => format!("{}.F.{}", tname, kind),
        };
        if !self.derived.insert(name.clone()) {
            return name;
        }
        let params: Vec<String> = (0..self.eff_params[tid].len()).map(tparam_name).collect();
        let names: Vec<(TVar, String)> = self.eff_params[tid].iter().enumerate().map(|(k, (v, _))| (*v, tparam_name(k))).collect();
        let selft = Ty::Named(tname.clone(), params.iter().map(|p| Ty::Param(p.clone())).collect());
        let mut tmpl_funcs = Vec::new();
        for p in &params {
            let op_ty = match kind {
                "show" => Ty::func(vec![Ty::Param(p.clone())], Ty::Str),
                "default" => Ty::Param(p.clone()),
                _ => Ty::func(vec![Ty::Param(p.clone()), Ty::Param(p.clone())], Ty::Bool),
            };
            tmpl_funcs.push((format!("{}_{}", kind, p), op_ty));
        }
        let (ir_params, ret, body) = match kind {
            "show" => {
                let mut arms = Vec::new();
                for (ci, c) in t.ctors.iter().enumerate() {
                    let fields: Vec<(String, bool)> = c.fields.iter().map(|f| (field_name(&f.name), false)).collect();
                    let shown: Vec<usize> = match &t.kind {
                        DataKind::Class { .. } | DataKind::Record { .. } => t.show_order(),
                        _ => (0..c.fields.len()).collect(),
                    };
                    let label = match t.kind {
                        DataKind::Record { .. } => String::new(),
                        DataKind::Class { .. } => t.name.clone(),
                        _ => c.name.clone(),
                    };
                    let mut parts: Vec<Term> = Vec::new();
                    for (k, &fi) in shown.iter().enumerate() {
                        let f = &c.fields[fi];
                        let ft = self.store.resolve(&f.ty);
                        let sub = self.show_term(&ft, &names, tid, line);
                        let shown_field = Term::CallVar("__s".into(), vec![Term::var(&field_name(&f.name))]);
                        let shown_field = replace_callvar(shown_field, "__s", &sub);
                        let is_parent = t.parent_field() == Some(fi);
                        let piece = if is_parent {
                            // inherited members inline: their show without the braces
                            Term::call("F.str.strip_wrapper", vec![Term::Str(format!("{}{{", self.core.types[match self.store.shallow(&ft) { Type::Data(p, _) => p, _ => tid }].name)), shown_field])
                        } else if matches!(t.kind, DataKind::Record { .. } | DataKind::Class { .. }) {
                            Term::cat(Term::Str(format!("{}: ", f.name)), shown_field)
                        } else {
                            shown_field
                        };
                        if k > 0 {
                            parts.push(Term::Str(", ".into()));
                        }
                        parts.push(piece);
                    }
                    let inner = parts.into_iter().reduce(Term::cat).unwrap_or(Term::Str(String::new()));
                    let text = if c.fields.is_empty() {
                        Term::Str(label)
                    } else if matches!(t.kind, DataKind::Declared) {
                        Term::cat(Term::cat(Term::Str(format!("{}(", label)), inner), Term::Str(")".into()))
                    } else {
                        Term::cat(Term::cat(Term::Str(format!("{}{{", label)), inner), Term::Str("}".into()))
                    };
                    arms.push((ir::Pat::Ctor(self.ctor_name(tid, ci), fields), Body::term(text)));
                }
                (vec![IrParam { name: "x".into(), reusable: false, ty: selft.clone() }], Ty::Str, Body::Match { scrutinee: "x".into(), arms })
            }
            "eq" | "lt" => {
                // compare constructor index first, then fields in order
                let mut arms = Vec::new();
                for (ci, c) in t.ctors.iter().enumerate() {
                    let fa: Vec<(String, bool)> = c.fields.iter().map(|f| (format!("a_{}", field_name(&f.name)), false)).collect();
                    let mut inner_arms = Vec::new();
                    for (cj, cc) in t.ctors.iter().enumerate() {
                        let fb: Vec<(String, bool)> = cc.fields.iter().map(|f| (format!("b_{}", field_name(&f.name)), false)).collect();
                        let term = if ci != cj {
                            if kind == "eq" { Term::boolean(false) } else { Term::boolean(ci < cj) }
                        } else {
                            let compared: Vec<usize> = match &t.kind {
                                DataKind::Class { .. } => t.show_order(),
                                _ => (0..c.fields.len()).collect(),
                            };
                            let mut acc: Option<Term> = None;
                            for &fi in compared.iter().rev() {
                                let f = &c.fields[fi];
                                let ft = self.store.resolve(&f.ty);
                                let a = Term::var(&fa[fi].0);
                                let b = Term::var(&fb[fi].0);
                                let eqt = self.cmp_term("eq", &ft, &names, tid, a.clone(), b.clone(), line);
                                let step = if kind == "eq" {
                                    match acc {
                                        None => eqt,
                                        Some(rest) => Term::And(Box::new(eqt), Box::new(rest)),
                                    }
                                } else {
                                    let ltt = self.cmp_term("lt", &ft, &names, tid, a, b, line);
                                    match acc {
                                        None => ltt,
                                        Some(rest) => Term::Or(Box::new(ltt), Box::new(Term::And(Box::new(eqt), Box::new(rest)))),
                                    }
                                };
                                acc = Some(step);
                            }
                            acc.unwrap_or(Term::boolean(kind == "eq"))
                        };
                        inner_arms.push((ir::Pat::Ctor(self.ctor_name(tid, cj), fb), Body::term(term)));
                    }
                    arms.push((ir::Pat::Ctor(self.ctor_name(tid, ci), fa), Body::Match { scrutinee: "b".into(), arms: inner_arms }));
                }
                (
                    vec![IrParam { name: "a".into(), reusable: false, ty: selft.clone() }, IrParam { name: "b".into(), reusable: false, ty: selft.clone() }],
                    Ty::Bool,
                    Body::Match { scrutinee: "a".into(), arms },
                )
            }
            _ => {
                // default: the first constructor without fields, else the first with defaults
                let ci = t.ctors.iter().position(|c| c.fields.is_empty()).unwrap_or(0);
                let args: Vec<Term> = t.ctors[ci].fields.iter().map(|f| {
                    let ft = self.store.resolve(&f.ty);
                    self.default_term(&ft, &names, tid, line)
                }).collect();
                (vec![], selft.clone(), Body::term(Term::Ctor(self.ctor_name(tid, ci), args)))
            }
        };
        self.defs.push(IrDef { name: name.clone(), is_unsafe: false, tmpl_types: params.clone(), tmpl_funcs, erased: vec![], erased_types: vec![], params: ir_params, ret, body });
        name
    }

    /// A term showing a value of a (possibly generic) type, as a closed
    /// function term, inside the derived def of `owner_tid` whose type
    /// parameters are `names`.
    fn show_term(&mut self, t: &Type, names: &[(TVar, String)], owner: TypeId, line: usize) -> Term {
        let _ = owner;
        let ops: Vec<(String, String)> = names.iter().map(|(_, n)| (n.clone(), format!("show_{}", n))).collect();
        self.derived_term("repr", t, names, &ops, line)
    }

    fn cmp_term(&mut self, kind: &str, t: &Type, names: &[(TVar, String)], owner: TypeId, a: Term, b: Term, line: usize) -> Term {
        let _ = owner;
        let ops: Vec<(String, String)> = names.iter().map(|(_, n)| (n.clone(), format!("{}_{}", kind, n))).collect();
        let f = self.derived_term(kind, t, names, &ops, line);
        apply_term(f, vec![a, b])
    }

    fn default_term(&mut self, t: &Type, names: &[(TVar, String)], owner: TypeId, line: usize) -> Term {
        let _ = owner;
        let ops: Vec<(String, String)> = names.iter().map(|(_, n)| (n.clone(), format!("default_{}", n))).collect();
        self.derived_term("default", t, names, &ops, line)
    }

    /// The operation `kind` (show / eq / lt / default) for a type, as a
    /// term: a prelude def, a derived def applied to the operations of its
    /// arguments, or a named operation for a type parameter.
    pub fn derived_term(&mut self, kind: &str, t: &Type, names: &[(TVar, String)], ops: &[(String, String)], line: usize) -> Term {
        // `repr` is `show` for a string inside a container (quoted)
        let base = if kind == "repr" { "show" } else { kind };
        let ty = self.store.shallow(t);
        match &ty {
            Type::Var(v) => {
                let n = names.iter().find(|(w, _)| *w == *v).map(|(_, n)| n.clone());
                match n.and_then(|n| ops.iter().find(|(p, _)| *p == n).map(|(_, op)| op.clone())) {
                    Some(op) => Term::var(&op),
                    None => match base {
                        "default" => {
                            self.error(line, "this def recurses on an int, and Bend needs a value of its result type for the case the recursion never reaches; the result has a generic part no parameter provides: recurse on a list instead, or mark the def `unsafe def`");
                            Term::unit()
                        }
                        _ => prim_op("F.unit", base),
                    },
                }
            }
            Type::Int => prim_op("F.i32", base),
            Type::Float => prim_op("F.f32", base),
            Type::Str => prim_op("F.str", kind),
            Type::Bool => prim_op("F.bool", base),
            Type::Unit => prim_op("F.unit", base),
            Type::List(e) | Type::Map(e) => {
                let et = self.ty(e, names, line);
                if base == "default" {
                    return if matches!(ty, Type::List(_)) { Term::List(vec![]) } else { Term::call("Map.new", vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(et)]) };
                }
                let sub = self.derived_term(if base == "show" { "repr" } else { base }, e, names, ops, line);
                let prefix = if matches!(ty, Type::List(_)) { "F.list" } else { "F.map" };
                lambda_over(if base == "show" { 1 } else { 2 }, base, Term::Call(format!("{}.{}", prefix, base), vec![Term::TmplTy(et), tmpl_arg(sub)]))
            }
            Type::Fn(..) => {
                self.error(line, format!("cannot {} a function", kind));
                Term::unit()
            }
            Type::Data(id, args) => {
                let id = *id;
                let args = args.clone();
                let name = self.derived_def(base, id, line);
                // one operation per effective parameter of the type
                let eff = self.eff_params[id].clone();
                let mut call_args = Vec::new();
                for (v, i) in &eff {
                    let actual = self.instantiate_eff(id, *v, *i, &args);
                    let at = self.ty(&actual, names, line);
                    call_args.push(Term::TmplTy(at));
                }
                let inner = expr::component_kind(id, kind);
                for (v, i) in &eff {
                    let actual = self.instantiate_eff(id, *v, *i, &args);
                    let sub = self.derived_term(inner, &actual, names, ops, line);
                    call_args.push(tmpl_arg(sub));
                }
                if base == "default" {
                    return Term::Call(name, call_args);
                }
                let arity = if base == "show" { 1 } else { 2 };
                lambda_over(arity, base, Term::Call(name, call_args))
            }
        }
    }

    // -- dictionaries -------------------------------------------------------------------------------

    /// The Bend term standing for a constraint's operation at a use site:
    /// a template parameter of the current def when the subject stayed
    /// generic, otherwise a closed term.
    pub fn dict_term(&mut self, ctx: &body::FnCtx, id: ConstraintId, line: usize) -> Term {
        // a dictionary parameter of the unit
        if let Some(dp) = ctx.dicts.iter().find(|d| d.id == id) {
            return Term::var(&dp.name);
        }
        let c = self.store.constraints[id].clone();
        match c.solution.clone() {
            Some(Solution::Param(k)) => {
                let name = ctx.dicts.get(k).map(|d| d.name.clone()).unwrap_or_else(|| "?".into());
                Term::var(&name)
            }
            Some(Solution::Method(m, targs, dicts)) => self.method_dict(ctx, m, &targs, &dicts, line),
            Some(Solution::Field(path)) => match &c.class {
                Class::Field(..) => self.field_dict(&path, &c, ctx, line),
                _ => self.set_field_dict(&path, &c, ctx, line),
            },
            Some(Solution::Concrete(subs)) => self.concrete_dict(ctx, id, &subs, line),
            None => {
                // an unsolved constraint on a variable that nothing fixed:
                // the caller's own dictionary if it is one, else unit ops
                if let Type::Var(_) = self.store.shallow(&c.subject) {
                    self.error(line, format!("an operation on a value whose type is never known: {}", crate::check::describe_class(&c.class)));
                }
                Term::unit()
            }
        }
    }
}

/// Two classes naming the same operation (their types aside).
pub fn same_class(a: &Class, b: &Class) -> bool {
    match (a, b) {
        (Class::Field(x, _), Class::Field(y, _)) | (Class::SetField(x, _), Class::SetField(y, _)) | (Class::Method(x, _, _), Class::Method(y, _, _)) => x == y,
        (Class::Convert(x, _), Class::Convert(y, _)) => x == y,
        (Class::Arith(x), Class::Arith(y)) => x == y,
        _ => std::mem::discriminant(a) == std::mem::discriminant(b),
    }
}

/// The name of a type parameter by position: A, B, ..., Z, T26, ...
pub fn tparam_name(i: usize) -> String {
    if i < 26 { ((b'A' + i as u8) as char).to_string() } else { format!("T{}", i) }
}

/// Field names Bend would reject or shadow.
pub fn field_name(n: &str) -> String {
    match n {
        "type" | "match" | "case" | "def" | "do" | "return" | "import" | "law" | "lambda" | "self" => format!("{}_", n),
        _ => n.to_string(),
    }
}

/// Local names: Fire names are Bend names, except the ones Bend reserves.
pub fn local_name(n: &str) -> String {
    field_name(n)
}

/// A method's image name: operator methods get words.
fn method_name(n: &str) -> String {
    match n {
        "+" => "add".into(),
        "-" => "sub".into(),
        "*" => "mul".into(),
        "/" => "div".into(),
        "%" => "mod".into(),
        "**" => "pow".into(),
        other => other.to_string(),
    }
}

fn dict_param_name(c: &Class, k: usize) -> String {
    let base = match c {
        Class::Eq => "eq".to_string(),
        Class::Ord => "lt".to_string(),
        Class::Show => "show".to_string(),
        Class::Arith(op) => op.name().to_string(),
        Class::OrElse(..) => "or_else".to_string(),
        Class::Len => "len".to_string(),
        Class::Zero => "zero".to_string(),
        Class::Iter(_) => "items".to_string(),
        Class::Index(..) => "index".to_string(),
        Class::IndexSet(..) => "index_set".to_string(),
        Class::Field(n, _) => format!("get_{}", n),
        Class::SetField(n, _) => format!("set_{}", n),
        Class::Method(n, _, _) => format!("m_{}", method_name(n)),
        Class::Convert(n, _) => format!("to_{}", n),
    };
    format!("{}_{}", base, k)
}

/// A term usable as a template argument: a def reference stays `~f`, a
/// lambda is wrapped in `~(...)`.
/// A derived operation of a builtin type (`F.i32.show`, ...) as a closed
/// function term. Eta-expanded: a def with reusable parameters is not
/// accepted as a template argument, a lambda is.
pub fn prim_op(prefix: &str, kind: &str) -> Term {
    let name = format!("{}.{}", prefix, kind);
    let arity = match kind {
        "show" | "repr" => 1,
        "default" => 0,
        _ => 2,
    };
    if arity == 0 {
        return Term::Call(name, vec![]);
    }
    let params: Vec<String> = (0..arity).map(|i| format!("__x{}", i)).collect();
    let args: Vec<Term> = params.iter().map(|p| Term::var(p)).collect();
    Term::Lam(params, Box::new(Term::Call(name, args)))
}

pub fn tmpl_arg(t: Term) -> Term {
    match t {
        Term::TmplRef(_) | Term::TmplTy(_) => t,
        Term::Var(v) => Term::TmplRef(v),
        other => Term::TmplTerm(Box::new(other)),
    }
}

/// Apply a function term to arguments: a def reference becomes a call.
pub fn apply_term(f: Term, args: Vec<Term>) -> Term {
    match f {
        Term::TmplRef(name) if !name.starts_with('(') => Term::Call(name, args),
        Term::Var(name) => Term::CallVar(name, args),
        Term::Lam(params, body) if params.len() == args.len() => {
            let mut b = *body;
            for (p, a) in params.iter().zip(args.into_iter()) {
                b = subst_var(b, p, &a);
            }
            b
        }
        other => Term::App(Box::new(other), args),
    }
}

/// `a b => call(.., a, b)`: a lambda over the given arity around a partial
/// template call (the operation of a structured type applied to the
/// operations of its parts, then to the values).
fn lambda_over(arity: usize, _kind: &str, call: Term) -> Term {
    let params: Vec<String> = (0..arity).map(|i| format!("__x{}", i)).collect();
    let body = match call {
        Term::Call(f, mut args) => {
            for p in &params {
                args.push(Term::var(p));
            }
            Term::Call(f, args)
        }
        other => other,
    };
    Term::Lam(params, Box::new(body))
}

fn replace_callvar(t: Term, name: &str, f: &Term) -> Term {
    match t {
        Term::CallVar(n, args) if n == name => apply_term(f.clone(), args),
        other => other,
    }
}

pub fn subst_var(t: Term, name: &str, with: &Term) -> Term {
    match t {
        Term::Var(v) if v == name => with.clone(),
        Term::Var(v) => Term::Var(v),
        Term::Ctor(c, args) => Term::Ctor(c, args.into_iter().map(|a| subst_var(a, name, with)).collect()),
        Term::Call(f, args) => Term::Call(f, args.into_iter().map(|a| subst_var(a, name, with)).collect()),
        Term::CallVar(f, args) => {
            let args: Vec<Term> = args.into_iter().map(|a| subst_var(a, name, with)).collect();
            if f == name {
                apply_term(with.clone(), args)
            } else {
                Term::CallVar(f, args)
            }
        }
        Term::Lam(ps, b) => {
            if ps.iter().any(|p| p == name) {
                Term::Lam(ps, b)
            } else {
                Term::Lam(ps, Box::new(subst_var(*b, name, with)))
            }
        }
        Term::Op(a, op, b, ty) => Term::Op(Box::new(subst_var(*a, name, with)), op, Box::new(subst_var(*b, name, with)), ty),
        Term::Cat(a, b) => Term::Cat(Box::new(subst_var(*a, name, with)), Box::new(subst_var(*b, name, with))),
        Term::And(a, b) => Term::And(Box::new(subst_var(*a, name, with)), Box::new(subst_var(*b, name, with))),
        Term::Or(a, b) => Term::Or(Box::new(subst_var(*a, name, with)), Box::new(subst_var(*b, name, with))),
        Term::Cons(a, b) => Term::Cons(Box::new(subst_var(*a, name, with)), Box::new(subst_var(*b, name, with))),
        Term::Tuple(a, b) => Term::Tuple(Box::new(subst_var(*a, name, with)), Box::new(subst_var(*b, name, with))),
        Term::List(items) => Term::List(items.into_iter().map(|a| subst_var(a, name, with)).collect()),
        Term::Ann(a, ty) => Term::Ann(Box::new(subst_var(*a, name, with)), ty),
        other => other,
    }
}

pub fn render_term(t: &Term) -> String {
    let d = IrDef {
        name: "x".into(),
        is_unsafe: false,
        tmpl_types: vec![],
        tmpl_funcs: vec![],
        erased: vec![],
        erased_types: vec![],
        params: vec![],
        ret: Ty::Unit,
        body: Body::term(t.clone()),
    };
    let p = ir::Program { types: vec![], defs: vec![d], raw_prelude: String::new() };
    let s = p.render_defs_only();
    s.trim().trim_start_matches("def x() -> Unit:").trim().to_string()
}

/// Mark lets used more than once as reusable, recursively.
fn mark_body(b: &mut Body, counts: &HashMap<String, usize>) {
    match b {
        Body::Match { arms, .. } => {
            for (pat, body) in arms {
                if let ir::Pat::Ctor(_, fields) = pat {
                    for (f, r) in fields {
                        if counts.get(f).cloned().unwrap_or(0) > 1 {
                            *r = true;
                        }
                    }
                }
                // `1n++p`: a reusable predecessor
                if let ir::Pat::Succ(p) = pat
                    && !p.starts_with('+') && counts.get(p.as_str()).cloned().unwrap_or(0) > 1 {
                        *p = format!("+{}", p);
                    }
                mark_body(body, counts);
            }
        }
        Body::Block { stmts, .. } | Body::Do { stmts, .. } => {
            for s in stmts {
                match s {
                    ir::Stmt::Let { name, reusable, .. } => {
                        if counts.get(name).cloned().unwrap_or(0) > 1 {
                            *reusable = true;
                        }
                    }
                    ir::Stmt::Bind { name, reusable, .. } => {
                        if counts.get(name).cloned().unwrap_or(0) > 1 {
                            *reusable = true;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

pub(crate) fn for_each_stmt(b: &Block, f: &mut dyn FnMut(&Stmt)) {
    for s in &b.stmts {
        f(s);
        match &s.kind {
            StmtKind::If { then, else_, .. } => {
                for_each_stmt(then, f);
                for_each_stmt(else_, f);
            }
            StmtKind::Match { arms, .. } => {
                for a in arms {
                    if let ExprKind::Block(b) = &a.body.kind {
                        for_each_stmt(b, f);
                    }
                }
            }
            StmtKind::For { body, .. } | StmtKind::While { body, .. } => for_each_stmt(body, f),
            _ => {}
        }
    }
}

// keep the map ordered for deterministic output
pub type OrderedMap<K, V> = BTreeMap<K, V>;
