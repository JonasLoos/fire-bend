// src/bend/lower/mod.rs
// Lowering: typed AST -> Bend IR. See docs/compiler.md.
//
// This file holds the driver (monomorphized def instances, record and
// closure-environment types, naming, and the post-passes that make bodies
// obey Bend's affine rules). `body.rs` lowers statements with continuation
// defs and loop drivers; `expr.rs` lowers expressions and builtins.

mod body;
mod builtins;
mod expr;
mod merge;

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::infer::{closure_effect, Diag};
use crate::ir::{self, Body, Def, DoTail, Param, Pat, Stmt, Term, Ty, TypeDef};
use crate::tast::*;
use crate::types::*;

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
        match e {
            Effect::Pure => Mode::Pure,
            Effect::Abort => Mode::Result,
            Effect::Io => Mode::Io,
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

/// A closure representation: the Data value that stands for a function
/// value of a given (resolved) function type, and how to call it.
#[derive(Debug, Clone)]
pub struct ClosRep {
    /// The Bend type of the value.
    pub ty: Ty,
    /// The def to call with the value as first argument, or None when the
    /// set is empty (a function-typed value nothing flows into).
    pub code: Option<String>,
}

/// One monomorphic instance of a def.
#[derive(Debug, Clone)]
pub struct Instance {
    pub def: DefId,
    pub name: String,
    /// Resolved type of the whole function (env excluded).
    pub subst: Vec<(TVar, Type)>,
    pub mode: Mode,
    /// Bend types of the parameters (after the env parameter, if any).
    pub params: Vec<Ty>,
    pub ret: Ty,
    /// The environment record type, if the def captures anything.
    pub env: Option<Ty>,
}

pub struct Lower<'a> {
    pub tp: &'a TProgram,
    pub store: TypeStore,
    pub effects: Vec<Effect>,
    pub types: Vec<TypeDef>,
    pub defs: Vec<Def>,
    pub diags: Vec<Diag>,
    /// (def id, type key) -> instance
    pub instances: HashMap<(DefId, String), Instance>,
    pub worklist: Vec<(DefId, String)>,
    pub emitted_types: HashSet<String>,
    pub emitted_defs: HashSet<String>,
    pub counter: usize,
    /// Closure sets already given a sum type, keyed by the sorted member
    /// code names.
    pub fn_sums: HashMap<String, ClosRep>,
    /// Closure sets whose representation is being computed (a set whose
    /// member's environment holds a function of the same set is recursive).
    pub rep_stack: Vec<Vec<DefId>>,
    /// Fields of each emitted environment type.
    pub env_fields: HashMap<String, Vec<(String, Ty)>>,
    /// Derived show/eq/cmp defs already emitted, by rendered type.
    pub derived: HashSet<String>,
}

pub fn lower_program(tp: &TProgram) -> Result<ir::Program, Vec<Diag>> {
    body::RECORD_FIELDS.with(|r| {
        *r.borrow_mut() = tp.records.iter().map(|rd| rd.fields.iter().map(|f| f.name.clone()).collect()).collect();
    });
    let mut lw = Lower {
        tp,
        store: tp.store.clone(),
        effects: tp.defs.iter().map(|d| d.effect).collect(),
        types: Vec::new(),
        defs: Vec::new(),
        diags: Vec::new(),
        instances: HashMap::new(),
        worklist: Vec::new(),
        emitted_types: HashSet::new(),
        emitted_defs: HashSet::new(),
        counter: 0,
        fn_sums: HashMap::new(),
        rep_stack: Vec::new(),
        env_fields: HashMap::new(),
        derived: HashSet::new(),
    };
    // the pair record lives in the prelude
    lw.emitted_types.insert("F.Pair".into());
    lw.emitted_types.insert("F.Ret".into());
    // main: no params, IO(Unit)
    let main_ty = Type::Fn(vec![], Box::new(Type::Unit), 0);
    let main_name = lw.instance_for(tp.main, &main_ty, 0);
    lw.drain_worklist();
    if !lw.diags.is_empty() {
        return Err(lw.diags);
    }
    lw.merge_recursive_groups();
    // rename main's instance to `main`
    for d in lw.defs.iter_mut() {
        if d.name == main_name {
            d.name = "main".into();
        }
        rename_calls(&mut d.body, &main_name, "main");
    }
    if let Some(cycle) = ir::find_mutual_recursion(&lw.defs) {
        return Err(vec![Diag { line: 0, message: format!("mutual recursion is not supported: {}", cycle.join(" -> ")) }]);
    }
    Ok(ir::Program { types: lw.types, defs: lw.defs, raw_prelude: PRELUDE.to_string() })
}

fn rename_calls(b: &mut Body, from: &str, to: &str) {
    fn term(t: &mut Term, from: &str, to: &str) {
        match t {
            Term::Call(f, args) => {
                if f == from {
                    *f = to.to_string();
                }
                for a in args {
                    term(a, from, to);
                }
            }
            Term::TmplRef(f) => {
                if f == from {
                    *f = to.to_string();
                }
            }
            Term::CallVar(_, args) | Term::Ctor(_, args) | Term::List(args) => {
                for a in args {
                    term(a, from, to);
                }
            }
            Term::Lam(_, b) | Term::Ann(b, _) => term(b, from, to),
            Term::Op(a, _, b, _) | Term::Cat(a, b) | Term::And(a, b) | Term::Or(a, b) | Term::Cons(a, b) | Term::Tuple(a, b) => {
                term(a, from, to);
                term(b, from, to);
            }
            _ => {}
        }
    }
    fn stmt(s: &mut Stmt, from: &str, to: &str) {
        match s {
            Stmt::Let { value, .. } | Stmt::Bind { value, .. } | Stmt::Destructure { value, .. } | Stmt::TupleLet { value, .. } | Stmt::Step(value) => term(value, from, to),
            Stmt::ParLet { calls, .. } => {
                for c in calls {
                    term(c, from, to);
                }
            }
        }
    }
    match b {
        Body::Match { arms, .. } => {
            for (_, a) in arms {
                rename_calls(a, from, to);
            }
        }
        Body::Block { stmts, tail } => {
            for s in stmts {
                stmt(s, from, to);
            }
            term(tail, from, to);
        }
        Body::Do { stmts, tail, .. } => {
            for s in stmts {
                stmt(s, from, to);
            }
            match tail {
                DoTail::Return(t) | DoTail::Step(t) => term(t, from, to),
            }
        }
    }
}

impl<'a> Lower<'a> {
    pub fn error(&mut self, line: usize, msg: impl Into<String>) {
        let message = msg.into();
        if !self.diags.iter().any(|d| d.line == line && d.message == message) {
            self.diags.push(Diag { line, message });
        }
    }

    pub fn fresh(&mut self, prefix: &str) -> String {
        self.counter += 1;
        format!("{}{}", prefix, self.counter)
    }

    /// A Bend-safe identifier from a Fire name.
    pub fn mangle(name: &str) -> String {
        let mut out = String::new();
        for c in name.chars() {
            match c {
                'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
                '$' => out.push_str("dollar"),
                '+' => out.push_str("op_add"),
                '-' => out.push_str("op_sub"),
                '*' => out.push_str("op_mul"),
                '/' => out.push_str("op_div"),
                '%' => out.push_str("op_mod"),
                '.' => out.push('_'),
                _ => out.push('_'),
            }
        }
        if out.is_empty() {
            out.push('x');
        }
        // Bend keywords that could clash as local names
        match out.as_str() {
            "match" | "case" | "def" | "type" | "law" | "do" | "return" | "import" | "is" | "for" | "exs" | "where" => {
                out.push('_');
            }
            _ => {}
        }
        out
    }

    // -- types ---------------------------------------------------------------

    /// Resolve a typed-AST type under an instance substitution to a
    /// concrete Bend type.
    pub fn ty(&mut self, t: &Type, subst: &[(TVar, Type)], line: usize) -> Ty {
        let t = self.store.substitute(t, subst);
        let t = self.store.resolve(&t);
        self.ty_concrete(&t, line)
    }

    fn ty_concrete(&mut self, t: &Type, line: usize) -> Ty {
        match t {
            Type::Var(_) => {
                // an unconstrained type: any Data will do
                Ty::Unit
            }
            Type::Int => Ty::U32,
            Type::Float => Ty::F32,
            Type::Str => Ty::Str,
            Type::Bool => Ty::Bool,
            Type::Unit => Ty::Unit,
            Type::List(e) => Ty::list(self.ty_concrete(e, line)),
            Type::Map(v) => Ty::Map(Box::new(self.ty_concrete(v, line))),
            Type::Maybe(e) => Ty::maybe(self.ty_concrete(e, line)),
            Type::Result(e, a) => {
                let e = self.ty_concrete(e, line);
                let a = self.ty_concrete(a, line);
                Ty::result(e, a)
            }
            Type::Fn(_, _, _) => self.closure_rep(t, line).ty,
            Type::Record(id, args) => {
                let args: Vec<Ty> = args.iter().map(|a| self.ty_concrete(a, line)).collect();
                let name = self.record_type_name(*id);
                self.ensure_record_type(*id);
                Ty::Named(name, args)
            }
            Type::Range => Ty::Named("F.Range".into(), vec![]),
            Type::Stream(_) => {
                self.error(line, "a lazy stream cannot be stored or passed around; consume it in the same expression (.take, .first, a for loop)");
                Ty::Unit
            }
        }
    }

    pub fn record_type_name(&self, id: RecId) -> String {
        format!("F.{}", Self::mangle(&self.tp.records[id].name))
    }

    pub fn record_ctor_name(&self, id: RecId) -> String {
        format!("F.{}.mk", Self::mangle(&self.tp.records[id].name))
    }

    /// Emit the generic Bend type of a record once.
    pub fn ensure_record_type(&mut self, id: RecId) {
        let name = self.record_type_name(id);
        if self.emitted_types.contains(&name) {
            return;
        }
        self.emitted_types.insert(name.clone());
        let rec = &self.tp.records[id];
        let params: Vec<String> = (0..rec.fields.len()).map(|i| format!("T{}", i)).collect();
        let fields: Vec<(String, Ty)> = rec.fields.iter().enumerate().map(|(i, f)| (Self::mangle(&f.name), Ty::Param(format!("T{}", i)))).collect();
        self.types.push(TypeDef { name: name.clone(), params, ctors: vec![(self.record_ctor_name(id), fields)] });
    }

    // -- closures ------------------------------------------------------------

    /// The representation of function values of a resolved function type.
    pub fn closure_rep(&mut self, t: &Type, line: usize) -> ClosRep {
        let (params, ret, clos) = match t {
            Type::Fn(p, r, c) => (p.clone(), (**r).clone(), *c),
            _ => unreachable!(),
        };
        let set = self.store.clos_set(clos);
        let members: Vec<DefId> = set.into_iter().collect();
        if members.is_empty() {
            return ClosRep { ty: Ty::Unit, code: None };
        }
        if self.rep_stack.contains(&members) {
            let names: Vec<String> = members.iter().map(|d| self.tp.defs[*d].name.clone()).collect();
            self.error(line, format!("a function value whose environment contains a function of the same kind ({}) has a recursive type, which is not supported", names.join(", ")));
            return ClosRep { ty: Ty::Unit, code: None };
        }
        // each member: its code instance for this signature and its env type
        self.rep_stack.push(members.clone());
        let mut codes: Vec<(String, Ty)> = Vec::new();
        for &d in &members {
            let (code, env) = self.member_code(d, &params, &ret, line);
            codes.push((code, env));
        }
        self.rep_stack.pop();
        if codes.len() == 1 {
            let (code, env) = codes.pop().unwrap();
            return ClosRep { ty: env, code: Some(code) };
        }
        // a sum type over the members
        codes.sort_by(|a, b| a.0.cmp(&b.0));
        let key = codes.iter().map(|(c, _)| c.as_str()).collect::<Vec<_>>().join("|");
        if let Some(rep) = self.fn_sums.get(&key) {
            return rep.clone();
        }
        let sum_name = self.fresh("F.Fn");
        let apply_name = format!("{}.apply", sum_name);
        let ctors: Vec<(String, Vec<(String, Ty)>)> = codes
            .iter()
            .enumerate()
            .map(|(i, (_, env))| (format!("{}.c{}", sum_name, i), vec![("env".to_string(), env.clone())]))
            .collect();
        self.types.push(TypeDef { name: sum_name.clone(), params: vec![], ctors: ctors.clone() });
        let rep = ClosRep { ty: Ty::Named(sum_name.clone(), vec![]), code: Some(apply_name.clone()) };
        self.fn_sums.insert(key, rep.clone());
        // apply: match the sum, call the member's code with its env
        let ptys: Vec<Ty> = params.iter().map(|p| self.ty_concrete(&self.store.resolve(p), line)).collect();
        let mode = self.set_mode(&members);
        let rty = self.ty_concrete(&self.store.resolve(&ret), line);
        let arg_names: Vec<String> = (0..ptys.len()).map(|i| format!("a{}", i)).collect();
        let arms: Vec<(Pat, Body)> = codes
            .iter()
            .enumerate()
            .map(|(i, (code, _))| {
                let mut args = vec![Term::var("env")];
                args.extend(arg_names.iter().map(|a| Term::var(a)));
                (Pat::Ctor(format!("{}.c{}", sum_name, i), vec![("env".into(), false)]), Body::term(Term::Call(code.clone(), args)))
            })
            .collect();
        let mut dparams = vec![Param { name: "f".into(), reusable: false, ty: Ty::Named(sum_name, vec![]) }];
        for (n, t) in arg_names.iter().zip(ptys.iter()) {
            dparams.push(Param { name: n.clone(), reusable: false, ty: t.clone() });
        }
        self.defs.push(Def {
            name: apply_name,
            is_unsafe: true,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: dparams,
            ret: mode.wrap(rty),
            body: Body::Match { scrutinee: "f".into(), arms },
        });
        rep
    }

    /// The mode shared by a set of function values (their join).
    pub fn set_mode(&self, members: &[DefId]) -> Mode {
        members.iter().fold(Mode::Pure, |m, d| m.join(Mode::of(self.effects[*d])))
    }

    /// The code def name and env type for a def used as a function value
    /// at the given signature.
    pub fn member_code(&mut self, d: DefId, params: &[Type], ret: &Type, line: usize) -> (String, Ty) {
        let def = &self.tp.defs[d];
        match &def.kind {
            DefKind::Method { rec, .. } => {
                // a bound method: env = {self}; a wrapper calls the method
                let rec = *rec;
                let self_ty = self.receiver_type_for(rec, params, ret, line);
                let mut full = vec![self_ty.clone()];
                full.extend(params.iter().cloned());
                let fn_ty = Type::Fn(full, Box::new(ret.clone()), 0);
                let inst = self.instance_for(d, &fn_ty, line);
                let self_bty = self.ty_concrete(&self.store.resolve(&self_ty), line);
                let env_name = format!("F.Env.{}", inst.replace('.', "_"));
                let wrapper = format!("{}.val", inst);
                if !self.emitted_types.contains(&env_name) {
                    self.emitted_types.insert(env_name.clone());
                    self.types.push(TypeDef { name: env_name.clone(), params: vec![], ctors: vec![(format!("{}.mk", env_name), vec![("self".into(), self_bty.clone())])] });
                }
                if !self.emitted_defs.contains(&wrapper) {
                    self.emitted_defs.insert(wrapper.clone());
                    let ptys: Vec<Ty> = params.iter().map(|p| self.ty_concrete(&self.store.resolve(p), line)).collect();
                    let mode = Mode::of(self.effects[d]);
                    let rty = self.ty_concrete(&self.store.resolve(ret), line);
                    let names: Vec<String> = (0..ptys.len()).map(|i| format!("a{}", i)).collect();
                    let mut dparams = vec![Param { name: "env".into(), reusable: false, ty: Ty::Named(env_name.clone(), vec![]) }];
                    for (n, t) in names.iter().zip(ptys.iter()) {
                        dparams.push(Param { name: n.clone(), reusable: false, ty: t.clone() });
                    }
                    let mut args = vec![Term::var("self")];
                    args.extend(names.iter().map(|n| Term::var(n)));
                    let inner = Term::Call(inst.clone(), args);
                    let ret_ty = self.method_result_type(d, mode, rty, line);
                    self.defs.push(Def {
                        name: wrapper.clone(),
                        is_unsafe: false,
                        tmpl_types: vec![],
                        tmpl_funcs: vec![],
                        erased: vec![],
                        params: dparams,
                        ret: ret_ty,
                        body: Body::Match { scrutinee: "env".into(), arms: vec![(Pat::Ctor(format!("{}.mk", env_name), vec![("self".into(), false)]), Body::term(inner))] },
                    });
                }
                (wrapper, Ty::Named(env_name, vec![]))
            }
            _ => {
                let fn_ty = Type::Fn(params.to_vec(), Box::new(ret.clone()), 0);
                let inst = self.instance_for(d, &fn_ty, line);
                let info = self.instances.values().find(|i| i.name == inst).cloned().expect("instance");
                match info.env {
                    Some(env) => (inst, env),
                    None => {
                        // no captures: a wrapper taking a unit env
                        let wrapper = format!("{}.val", inst);
                        if !self.emitted_defs.contains(&wrapper) {
                            self.emitted_defs.insert(wrapper.clone());
                            let names: Vec<String> = (0..info.params.len()).map(|i| format!("a{}", i)).collect();
                            let mut dparams = vec![Param { name: "env".into(), reusable: false, ty: Ty::Unit }];
                            for (n, t) in names.iter().zip(info.params.iter()) {
                                dparams.push(Param { name: n.clone(), reusable: false, ty: t.clone() });
                            }
                            let call = Term::Call(inst.clone(), names.iter().map(|n| Term::var(n)).collect());
                            self.defs.push(Def {
                                name: wrapper.clone(),
                                is_unsafe: false,
                                tmpl_types: vec![],
                                tmpl_funcs: vec![],
                                erased: vec![],
                                params: dparams,
                                ret: info.mode.wrap(info.ret.clone()),
                                body: Body::term(call),
                            });
                        }
                        (wrapper, Ty::Unit)
                    }
                }
            }
        }
    }

    /// The receiver type of a bound-method value: reconstructed from the
    /// method's scheme by matching its parameter types.
    fn receiver_type_for(&mut self, rec: RecId, params: &[Type], ret: &Type, _line: usize) -> Type {
        let _ = (params, ret);
        // instantiate the record with fresh args and let the scheme match fix them
        let args: Vec<Type> = self.tp.records[rec].field_vars.iter().map(|_| self.store.fresh()).collect();
        Type::Record(rec, args)
    }

    /// A method's Bend result type: mutating methods return the new self
    /// (paired with the value when there is one).
    pub fn method_result_type(&mut self, d: DefId, mode: Mode, value_ty: Ty, line: usize) -> Ty {
        let def = &self.tp.defs[d];
        if let DefKind::Method { rec, mutates: true } = &def.kind {
            let rec = *rec;
            let self_ty = match self.instances.values().find(|i| i.def == d) {
                Some(i) => i.params[0].clone(),
                None => {
                    let t = Type::Record(rec, self.tp.records[rec].field_vars.clone());
                    self.ty(&t, &[], line)
                }
            };
            if value_ty == Ty::Unit {
                return mode.wrap(self_ty);
            }
            return mode.wrap(Ty::Named("F.Ret".into(), vec![self_ty, value_ty]));
        }
        mode.wrap(value_ty)
    }

    // -- instances -----------------------------------------------------------

    /// The Bend name of the instance of `def` at the given (possibly
    /// partially unresolved) function type, creating it if needed.
    pub fn instance_for(&mut self, def: DefId, fn_ty: &Type, line: usize) -> String {
        let d = &self.tp.defs[def];
        // match the scheme against the use type to find the substitution
        let (params, ret) = match fn_ty {
            Type::Fn(p, r, _) => (p.clone(), (**r).clone()),
            _ => unreachable!(),
        };
        let mut subst: Vec<(TVar, Type)> = d.scheme.vars.iter().map(|v| (*v, self.store.fresh())).collect();
        let scheme_ty = d.scheme.ty.clone();
        let inst_ty = self.store.substitute(&scheme_ty, &subst);
        if let Type::Fn(sp, sr, _) = &inst_ty {
            for (a, b) in sp.iter().zip(params.iter()) {
                let _ = self.store.unify(a, b);
            }
            let _ = self.store.unify(sr, &ret);
        }
        // default any leftover variables so the key is stable
        for (_, t) in subst.iter_mut() {
            let r = self.store.resolve(t);
            *t = r;
        }
        let ptys: Vec<Ty> = params.iter().map(|p| self.ty(p, &subst, line)).collect();
        let rty = self.ty(&ret, &subst, line);
        let key = format!("{}|{}", ptys.iter().map(|t| t.render()).collect::<Vec<_>>().join(","), rty.render());
        if let Some(i) = self.instances.get(&(def, key.clone())) {
            return i.name.clone();
        }
        let base = match &d.kind {
            DefKind::Main => "f.main".to_string(),
            DefKind::Method { rec, .. } => format!("f.{}.{}", Self::mangle(&self.tp.records[*rec].name), Self::mangle(&d.name)),
            DefKind::Ctor(rec) => format!("f.{}.new", Self::mangle(&self.tp.records[*rec].name)),
            DefKind::Lambda => format!("f.{}", Self::mangle(&d.name)),
            DefKind::Plain => format!("f.{}", Self::mangle(&d.name)),
        };
        let name = if self.emitted_defs.contains(&base) || self.instances.values().any(|i| i.name == base) {
            let n = self.fresh(&format!("{}__i", base));
            n
        } else {
            base.clone()
        };
        // the environment record type for captures
        let env = if d.captures.is_empty() {
            None
        } else {
            let fields: Vec<(String, Ty)> = d
                .captures
                .iter()
                .map(|(n, t)| {
                    let bt = self.ty(t, &subst, line);
                    (Self::mangle(n), bt)
                })
                .collect();
            // one environment type per def, shared by its template copies
            // and instances (the closure value is built once, where the def
            // is declared); an instance whose capture types differ gets its own
            let primary = d.template_of.unwrap_or(def);
            let shared = format!("F.Env.{}_d{}", base.replace('.', "_"), primary);
            let env_name = match self.env_fields.get(&shared) {
                Some(f) if f != &fields => format!("F.Env.{}", name.replace('.', "_")),
                _ => shared,
            };
            if !self.emitted_types.contains(&env_name) {
                self.emitted_types.insert(env_name.clone());
                self.env_fields.insert(env_name.clone(), fields.clone());
                self.types.push(TypeDef { name: env_name.clone(), params: vec![], ctors: vec![(format!("{}.mk", env_name), fields)] });
            }
            Some(Ty::Named(env_name, vec![]))
        };
        let mode = if matches!(d.kind, DefKind::Main) { Mode::Io } else { Mode::of(self.effects[def]) };
        let inst = Instance { def, name: name.clone(), subst, mode, params: ptys, ret: rty, env };
        self.instances.insert((def, key.clone()), inst);
        self.worklist.push((def, key));
        name
    }

    fn drain_worklist(&mut self) {
        while let Some((def, key)) = self.worklist.pop() {
            let inst = self.instances[&(def, key)].clone();
            self.lower_def_instance(&inst);
        }
    }

    // -- post passes ---------------------------------------------------------

    /// Mark reusable (`+`) parameters, lets, and pattern fields where a
    /// name is used more than once. Template arguments go through affine
    /// wrappers (`tmpl_wrapper`), so defs may use `+` freely.
    pub fn fix_quantities(&mut self, def: &mut Def) {
        let mut counts: HashMap<String, usize> = HashMap::new();
        def.body.count_vars(&mut counts);
        for p in def.params.iter_mut() {
            if counts.get(&p.name).copied().unwrap_or(0) > 1 {
                p.reusable = true;
            }
        }
        mark_body(&mut def.body, &counts);
    }

    /// An affine wrapper of a code def, for use as a template argument:
    /// `code.t(env, a0, ..) = code(env, a0, ..)`.
    pub fn tmpl_wrapper(&mut self, code: &str) -> String {
        let name = format!("{}.t", code);
        if self.emitted_defs.contains(&name) {
            return name;
        }
        // the signature: from an instance (maybe not lowered yet) or an emitted def
        let found = self.instances.values().find(|i| i.name == code).cloned();
        let sig: Option<(Vec<Ty>, Ty)> = if let Some(inst) = found {
            let mut ps: Vec<Ty> = Vec::new();
            if let Some(e) = &inst.env {
                ps.push(e.clone());
            }
            let (is_method, dline) = {
                let d = &self.tp.defs[inst.def];
                (matches!(d.kind, DefKind::Method { .. }), d.line)
            };
            let value_ret = if is_method { self.method_result_type(inst.def, Mode::Pure, inst.ret.clone(), dline) } else { inst.ret.clone() };
            ps.extend(inst.params.iter().cloned());
            Some((ps, inst.mode.wrap(value_ret)))
        } else {
            self.defs.iter().find(|d| d.name == code).map(|d| (d.params.iter().map(|p| p.ty.clone()).collect(), d.ret.clone()))
        };
        let (ptys, ret) = match sig {
            Some(s) => s,
            None => {
                self.diags.push(Diag { line: 0, message: format!("internal: no signature for {}", code) });
                return code.to_string();
            }
        };
        let names: Vec<String> = (0..ptys.len()).map(|i| format!("a{}", i)).collect();
        let params: Vec<Param> = names.iter().zip(ptys.iter()).map(|(n, t)| Param { name: n.clone(), reusable: false, ty: t.clone() }).collect();
        let call = Term::Call(code.to_string(), names.iter().map(|n| Term::var(n)).collect());
        self.emitted_defs.insert(name.clone());
        self.defs.push(Def { name: name.clone(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params, ret, body: Body::term(call) });
        name
    }

    /// Split do-blocks so that no do-let is used more than once: the rest of
    /// the block moves into a continuation def with `+` parameters.
    pub fn split_do_blocks(&mut self, def: &mut Def) {
        let name = def.name.clone();
        let mode_ret = def.ret.clone();
        let is_unsafe = def.is_unsafe;
        self.split_body(&mut def.body, &name, &mode_ret, is_unsafe, &def.params);
    }

    /// The field types of constructor `ctor` of a value of type `scrut`.
    fn ctor_field_types(&self, ctor: &str, scrut: &Ty) -> Option<Vec<Ty>> {
        match (ctor, scrut) {
            ("Con", Ty::List(e)) => Some(vec![(**e).clone(), scrut.clone()]),
            ("Nil", _) | ("None", _) | ("True", _) | ("False", _) | ("Unit", _) => Some(vec![]),
            ("Some", Ty::Maybe(i)) => Some(vec![(**i).clone()]),
            ("Done", Ty::Result(_, a)) => Some(vec![(**a).clone()]),
            ("Fail", Ty::Result(e, _)) => Some(vec![(**e).clone()]),
            (_, Ty::Named(n, args)) => {
                let td = self.types.iter().find(|t| &t.name == n)?;
                let (_, fields) = td.ctors.iter().find(|(c, _)| c == ctor)?;
                let m: Vec<(String, Ty)> = td.params.iter().cloned().zip(args.iter().cloned()).collect();
                Some(fields.iter().map(|(_, t)| t.subst_params(&m)).collect())
            }
            _ => None,
        }
    }

    fn split_body(&mut self, body: &mut Body, name: &str, ret: &Ty, is_unsafe: bool, params: &[Param]) {
        match body {
            Body::Match { scrutinee, arms } => {
                let scrut_ty = params.iter().find(|p| &p.name == scrutinee).map(|p| p.ty.clone());
                for (pat, b) in arms.iter_mut() {
                    // pattern fields are in scope of the arm
                    let mut scope: Vec<Param> = params.to_vec();
                    if let Pat::Ctor(ctor, fields) = pat {
                        let tys = scrut_ty.as_ref().and_then(|t| self.ctor_field_types(ctor, t));
                        for (i, (f, _)) in fields.iter().enumerate() {
                            let ty = tys.as_ref().and_then(|v| v.get(i).cloned()).unwrap_or(Ty::Unit);
                            scope.push(Param { name: f.clone(), reusable: true, ty });
                        }
                    }
                    if let Pat::Succ(p) = pat {
                        scope.push(Param { name: p.clone(), reusable: true, ty: Ty::Nat });
                    }
                    self.split_body(b, name, ret, is_unsafe, &scope);
                }
            }
            Body::Block { .. } => {}
            Body::Do { monad, stmts, tail } => {
                // find the first let/bind whose name is used more than once afterwards
                let mut cut: Option<usize> = None;
                for i in 0..stmts.len() {
                    let bound = match &stmts[i] {
                        Stmt::Let { name, .. } | Stmt::Bind { name, .. } => Some((name.clone(), stmt_ty(&stmts[i]))),
                        _ => None,
                    };
                    if let Some((n, _)) = bound {
                        let mut counts = HashMap::new();
                        for s in &stmts[i + 1..] {
                            s.count_vars(&mut counts);
                        }
                        match tail {
                            DoTail::Return(t) | DoTail::Step(t) => t.count_vars(&mut counts),
                        }
                        if counts.get(&n).copied().unwrap_or(0) > 1 {
                            cut = Some(i);
                            break;
                        }
                    }
                }
                if let Some(i) = cut {
                    // live variables of the rest: params + names bound before/at i
                    let rest: Vec<Stmt> = stmts.drain(i + 1..).collect();
                    let rest_tail = std::mem::replace(tail, DoTail::Return(Term::unit()));
                    let mut counts = HashMap::new();
                    for s in &rest {
                        s.count_vars(&mut counts);
                    }
                    match &rest_tail {
                        DoTail::Return(t) | DoTail::Step(t) => t.count_vars(&mut counts),
                    }
                    let mut known: Vec<(String, Ty)> = params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect();
                    for s in stmts.iter() {
                        if let Some((n, t)) = match s {
                            Stmt::Let { name, .. } | Stmt::Bind { name, .. } => Some((name.clone(), stmt_ty(s))),
                            _ => None,
                        } {
                            known.retain(|(k, _)| k != &n);
                            known.push((n, t));
                        }
                    }
                    let live: Vec<(String, Ty)> = known.into_iter().filter(|(n, _)| counts.contains_key(n)).collect();
                    let kname = self.fresh(&format!("{}.k", name));
                    let kparams: Vec<Param> = live
                        .iter()
                        .map(|(n, t)| Param { name: n.clone(), reusable: counts.get(n).copied().unwrap_or(0) > 1, ty: t.clone() })
                        .collect();
                    let call = Term::Call(kname.clone(), live.iter().map(|(n, _)| Term::var(n)).collect());
                    *tail = DoTail::Step(call);
                    let mut kdef = Def { name: kname, is_unsafe, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params: kparams.clone(), ret: ret.clone(), body: Body::Do { monad: monad.clone(), stmts: rest, tail: rest_tail } };
                    self.split_body(&mut kdef.body, name, ret, is_unsafe, &kparams);
                    self.defs.push(kdef);
                }
            }
        }
    }
}

fn stmt_ty(s: &Stmt) -> Ty {
    match s {
        Stmt::Let { ty: Some(t), .. } | Stmt::Bind { ty: t, .. } => t.clone(),
        _ => Ty::Unit,
    }
}

/// Mark `+` on lets (pure blocks) and pattern fields used more than once.
fn mark_body(b: &mut Body, counts: &HashMap<String, usize>) {
    match b {
        Body::Match { arms, .. } => {
            for (pat, body) in arms.iter_mut() {
                if let Pat::Ctor(_, fields) = pat {
                    for (f, reusable) in fields.iter_mut() {
                        if counts.get(f).copied().unwrap_or(0) > 1 {
                            *reusable = true;
                        }
                    }
                }
                mark_body(body, counts);
            }
        }
        Body::Block { stmts, .. } => {
            for s in stmts.iter_mut() {
                if let Stmt::Let { name, reusable, .. } = s {
                    if counts.get(name).copied().unwrap_or(0) > 1 {
                        *reusable = true;
                    }
                }
            }
        }
        Body::Do { .. } => {}
    }
}

/// Effect of an expression, for choosing bind vs let.
pub fn expr_effect_of(tp: &TProgram, effects: &[Effect], e: &TExpr) -> Effect {
    crate::infer::expr_effect_pub(e, effects, &tp.store, &tp.records)
}

pub fn closure_effect_of(store: &TypeStore, effects: &[Effect], t: &Type) -> Effect {
    closure_effect(t, effects, store)
}

pub fn unique_names(v: &[String]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    v.iter().filter(|n| seen.insert((*n).clone())).cloned().collect()
}
