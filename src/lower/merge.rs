// src/bend/lower/merge.rs
// Bend has no mutual recursion, not even between a function and the
// helper defs its branches were split into. When a function recurses,
// this pass merges it with all its helpers into one self-recursive
// dispatcher def: a frame sum type with one constructor per helper (its
// parameters as fields), and a result sum type when the helpers' result
// types differ. The original entry keeps its name as a thin wrapper.

use std::collections::{BTreeSet, HashMap};

use super::*;

impl<'a> Lower<'a> {
    pub fn merge_recursive_groups(&mut self) {
        let owners: Vec<String> = self.instances.values().map(|i| i.name.clone()).collect();
        // group every def under the longest owner name that prefixes it
        let mut groups: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, d) in self.defs.iter().enumerate() {
            if d.name.ends_with(".t") || d.name.ends_with(".val") {
                continue;
            }
            let mut best: Option<&String> = None;
            for o in &owners {
                if d.name == *o || d.name.starts_with(&format!("{}.", o)) {
                    if best.map(|b| o.len() > b.len()).unwrap_or(true) {
                        best = Some(o);
                    }
                }
            }
            if let Some(o) = best {
                groups.entry(o.clone()).or_default().push(i);
            }
        }
        let mut to_remove: BTreeSet<usize> = BTreeSet::new();
        let mut new_defs: Vec<Def> = Vec::new();
        let mut owners_sorted: Vec<String> = groups.keys().cloned().collect();
        owners_sorted.sort();
        for owner in owners_sorted {
            let idxs = &groups[&owner];
            if idxs.len() < 2 {
                continue;
            }
            // recursive at all? (some def in the group calls the owner)
            let names: BTreeSet<String> = idxs.iter().map(|&i| self.defs[i].name.clone()).collect();
            let recursive = idxs.iter().any(|&i| self.defs[i].def_refs().contains(&owner));
            if !recursive {
                continue;
            }
            let members: Vec<Def> = idxs.iter().map(|&i| self.defs[i].clone()).collect();
            let merged = self.merge_group(&owner, members, &names);
            for &i in idxs {
                to_remove.insert(i);
            }
            new_defs.extend(merged);
        }
        let mut kept: Vec<Def> = Vec::new();
        for (i, d) in self.defs.drain(..).enumerate() {
            if !to_remove.contains(&i) {
                kept.push(d);
            }
        }
        kept.extend(new_defs);
        self.defs = kept;
    }

    /// Merge `members` (the owner first) into a dispatcher.
    fn merge_group(&mut self, owner: &str, members: Vec<Def>, names: &BTreeSet<String>) -> Vec<Def> {
        let kname = format!("F.K.{}", owner.replace('.', "_"));
        let disp = format!("{}.k", owner);
        // the mode is shared; results are wrapped in it
        let mode = self.instances.values().find(|i| i.name == owner).map(|i| i.mode).unwrap_or(Mode::Pure);
        // distinct unwrapped result types
        let mut result_tys: Vec<Ty> = Vec::new();
        for d in &members {
            let r = unwrap_ret(&d.ret, mode);
            if !result_tys.contains(&r) {
                result_tys.push(r);
            }
        }
        let rname = format!("F.R.{}", owner.replace('.', "_"));
        let use_sum = result_tys.len() > 1;
        let sum_ty = if use_sum { Ty::Named(rname.clone(), vec![]) } else { result_tys[0].clone() };
        let ctor_of = |ty: &Ty| -> String {
            let j = result_tys.iter().position(|t| t == ty).unwrap();
            format!("{}.r{}", rname, j)
        };
        let mut out = Vec::new();
        // frame type
        let mut kctors: Vec<(String, Vec<(String, Ty)>)> = Vec::new();
        let mut frame_ctor: HashMap<String, String> = HashMap::new();
        for (i, d) in members.iter().enumerate() {
            let c = format!("{}.c{}", kname, i);
            kctors.push((c.clone(), d.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect()));
            frame_ctor.insert(d.name.clone(), c);
        }
        self.types.push(TypeDef { name: kname.clone(), params: vec![], ctors: kctors });
        if use_sum {
            let rctors: Vec<(String, Vec<(String, Ty)>)> = result_tys.iter().enumerate().map(|(j, t)| (format!("{}.r{}", rname, j), vec![("v".to_string(), t.clone())])).collect();
            self.types.push(TypeDef { name: rname.clone(), params: vec![], ctors: rctors });
            // unwrappers
            for (j, t) in result_tys.iter().enumerate() {
                let getter = format!("{}.get{}", rname, j);
                let arms: Vec<(Pat, Body)> = result_tys
                    .iter()
                    .enumerate()
                    .map(|(jj, _)| {
                        let body = if jj == j { Body::term(Term::var("v")) } else { Body::term(Term::Call("F.crash".into(), vec![Term::TyArg(t.clone()), Term::Str("internal: result variant".into())])) };
                        (Pat::Ctor(format!("{}.r{}", rname, jj), vec![("v".into(), false)]), body)
                    })
                    .collect();
                out.push(Def {
                    name: getter,
                    is_unsafe: false,
                    tmpl_types: vec![],
                    tmpl_funcs: vec![],
                    erased: vec![],
                    params: vec![Param { name: "r".into(), reusable: false, ty: Ty::Named(rname.clone(), vec![]) }],
                    ret: t.clone(),
                    body: Body::Match { scrutinee: "r".into(), arms },
                });
            }
        }
        // the dispatcher
        let mut arms: Vec<(Pat, Body)> = Vec::new();
        for d in &members {
            let my_ret = unwrap_ret(&d.ret, mode);
            let body = self.rewrite_body(&d.body, names, &disp, &frame_ctor, use_sum, &rname, &result_tys, mode, &my_ret, &ctor_of);
            let fields: Vec<(String, bool)> = d.params.iter().map(|p| (p.name.clone(), false)).collect();
            arms.push((Pat::Ctor(frame_ctor[&d.name].clone(), fields), body));
        }
        let mut disp_def = Def {
            name: disp.clone(),
            is_unsafe: true,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: vec![Param { name: "k".into(), reusable: false, ty: Ty::Named(kname.clone(), vec![]) }],
            ret: mode.wrap(sum_ty.clone()),
            body: Body::Match { scrutinee: "k".into(), arms },
        };
        self.fix_quantities(&mut disp_def);
        out.push(disp_def);
        // the entry wrapper keeps the owner's name and signature
        let entry = members.iter().find(|d| d.name == owner).unwrap();
        let args: Vec<Term> = entry.params.iter().map(|p| Term::var(&p.name)).collect();
        let call = Term::Call(disp.clone(), vec![Term::Ctor(frame_ctor[owner].clone(), args)]);
        let entry_ret = unwrap_ret(&entry.ret, mode);
        let body = if use_sum {
            let getter = format!("{}.get{}", rname, result_tys.iter().position(|t| *t == entry_ret).unwrap());
            match mode {
                Mode::Pure => Body::term(Term::Call(getter, vec![call])),
                m => Body::Do {
                    monad: m.wrap(entry_ret.clone()),
                    stmts: vec![Stmt::Bind { name: "r".into(), ty: Ty::Named(rname.clone(), vec![]), value: call }],
                    tail: DoTail::Return(Term::Call(getter, vec![Term::var("r")])),
                },
            }
        } else {
            match mode {
                Mode::Pure => Body::term(call),
                m => Body::Do { monad: m.wrap(entry_ret.clone()), stmts: vec![], tail: DoTail::Step(call) },
            }
        };
        out.push(Def {
            name: owner.to_string(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: entry.params.iter().map(|p| Param { name: p.name.clone(), reusable: false, ty: p.ty.clone() }).collect(),
            ret: entry.ret.clone(),
            body,
        });
        out
    }

    /// Rewrite a member's body: calls to group members go through the
    /// dispatcher (unwrapped when not in tail position), and the body's own
    /// result is wrapped in the result sum.
    #[allow(clippy::too_many_arguments)]
    fn rewrite_body(&mut self, b: &Body, names: &BTreeSet<String>, disp: &str, frame_ctor: &HashMap<String, String>, use_sum: bool, rname: &str, result_tys: &[Ty], mode: Mode, my_ret: &Ty, ctor_of: &dyn Fn(&Ty) -> String) -> Body {
        let wrap = |t: Term, ty: &Ty| -> Term {
            if use_sum { Term::Ctor(ctor_of(ty), vec![t]) } else { t }
        };
        match b {
            Body::Match { scrutinee, arms } => Body::Match {
                scrutinee: scrutinee.clone(),
                arms: arms.iter().map(|(p, a)| (p.clone(), self.rewrite_body(a, names, disp, frame_ctor, use_sum, rname, result_tys, mode, my_ret, ctor_of))).collect(),
            },
            Body::Block { stmts, tail } => {
                let mut new_stmts: Vec<Stmt> = Vec::new();
                for s in stmts {
                    new_stmts.extend(self.rewrite_stmt(s, names, disp, frame_ctor, use_sum, rname, result_tys));
                }
                // tail: a call to a member passes the sum through; anything else is wrapped
                let tail = match tail {
                    Term::Call(f, args) if names.contains(f) => {
                        let args: Vec<Term> = args.iter().map(|a| self.rewrite_term(a, names, disp, frame_ctor, use_sum, rname, result_tys)).collect();
                        Term::Call(disp.to_string(), vec![Term::Ctor(frame_ctor[f].clone(), args)])
                    }
                    other => {
                        let t = self.rewrite_term(other, names, disp, frame_ctor, use_sum, rname, result_tys);
                        wrap(t, my_ret)
                    }
                };
                Body::Block { stmts: new_stmts, tail }
            }
            Body::Do { monad, stmts, tail } => {
                let mut new_stmts: Vec<Stmt> = Vec::new();
                for s in stmts {
                    new_stmts.extend(self.rewrite_stmt(s, names, disp, frame_ctor, use_sum, rname, result_tys));
                }
                let sum_ty = if use_sum { Ty::Named(rname.to_string(), vec![]) } else { unwrap_ret(monad, mode) };
                let new_monad = mode.wrap(sum_ty.clone());
                let tail = match tail {
                    DoTail::Return(t) => {
                        let t = self.rewrite_term(t, names, disp, frame_ctor, use_sum, rname, result_tys);
                        DoTail::Return(wrap(t, my_ret))
                    }
                    DoTail::Step(Term::Call(f, args)) if names.contains(f) => {
                        let args: Vec<Term> = args.iter().map(|a| self.rewrite_term(a, names, disp, frame_ctor, use_sum, rname, result_tys)).collect();
                        DoTail::Step(Term::Call(disp.to_string(), vec![Term::Ctor(frame_ctor[f].clone(), args)]))
                    }
                    DoTail::Step(other) => {
                        // a monadic call of an outside def: bind then wrap
                        if use_sum {
                            let t = self.rewrite_term(other, names, disp, frame_ctor, use_sum, rname, result_tys);
                            new_stmts.push(Stmt::Bind { name: "__r".into(), ty: my_ret.clone(), value: t });
                            DoTail::Return(wrap(Term::var("__r"), my_ret))
                        } else {
                            DoTail::Step(self.rewrite_term(other, names, disp, frame_ctor, use_sum, rname, result_tys))
                        }
                    }
                };
                Body::Do { monad: new_monad, stmts: new_stmts, tail }
            }
        }
    }

    fn rewrite_stmt(&mut self, s: &Stmt, names: &BTreeSet<String>, disp: &str, frame_ctor: &HashMap<String, String>, use_sum: bool, rname: &str, result_tys: &[Ty]) -> Vec<Stmt> {
        match s {
            Stmt::Let { name, reusable, ty, value } => vec![Stmt::Let { name: name.clone(), reusable: *reusable, ty: ty.clone(), value: self.rewrite_term(value, names, disp, frame_ctor, use_sum, rname, result_tys) }],
            Stmt::Bind { name, ty, value } => {
                // a member call bound in a do-block: the sum comes back; unwrap with a let
                if let Term::Call(f, args) = value {
                    if names.contains(f) {
                        let args: Vec<Term> = args.iter().map(|a| self.rewrite_term(a, names, disp, frame_ctor, use_sum, rname, result_tys)).collect();
                        let call = Term::Call(disp.to_string(), vec![Term::Ctor(frame_ctor[f].clone(), args)]);
                        if use_sum {
                            let j = result_tys.iter().position(|t| t == ty).unwrap_or(0);
                            let getter = format!("{}.get{}", rname, j);
                            let tmp = format!("{}__sum", name);
                            return vec![
                                Stmt::Bind { name: tmp.clone(), ty: Ty::Named(rname.to_string(), vec![]), value: call },
                                Stmt::Let { name: name.clone(), reusable: false, ty: Some(ty.clone()), value: Term::Call(getter, vec![Term::Var(tmp)]) },
                            ];
                        }
                        return vec![Stmt::Bind { name: name.clone(), ty: ty.clone(), value: call }];
                    }
                }
                vec![Stmt::Bind { name: name.clone(), ty: ty.clone(), value: self.rewrite_term(value, names, disp, frame_ctor, use_sum, rname, result_tys) }]
            }
            Stmt::Destructure { ctor, fields, value } => vec![Stmt::Destructure { ctor: ctor.clone(), fields: fields.clone(), value: self.rewrite_term(value, names, disp, frame_ctor, use_sum, rname, result_tys) }],
            Stmt::TupleLet { a, b, value } => vec![Stmt::TupleLet { a: a.clone(), b: b.clone(), value: self.rewrite_term(value, names, disp, frame_ctor, use_sum, rname, result_tys) }],
            Stmt::Step(t) => vec![Stmt::Step(self.rewrite_term(t, names, disp, frame_ctor, use_sum, rname, result_tys))],
            Stmt::ParLet { names: ns, calls } => vec![Stmt::ParLet { names: ns.clone(), calls: calls.iter().map(|c| self.rewrite_term(c, names, disp, frame_ctor, use_sum, rname, result_tys)).collect() }],
        }
    }

    fn rewrite_term(&mut self, t: &Term, names: &BTreeSet<String>, disp: &str, frame_ctor: &HashMap<String, String>, use_sum: bool, rname: &str, result_tys: &[Ty]) -> Term {
        let go = |lw: &mut Self, x: &Term| lw.rewrite_term(x, names, disp, frame_ctor, use_sum, rname, result_tys);
        match t {
            Term::Call(f, args) if names.contains(f) => {
                let args: Vec<Term> = args.iter().map(|a| go(self, a)).collect();
                let call = Term::Call(disp.to_string(), vec![Term::Ctor(frame_ctor[f].clone(), args)]);
                if use_sum {
                    // a non-tail pure call: unwrap by the member's result type
                    let ret = self.member_ret(f);
                    let j = result_tys.iter().position(|t| *t == ret).unwrap_or(0);
                    Term::Call(format!("{}.get{}", rname, j), vec![call])
                } else {
                    call
                }
            }
            Term::Call(f, args) => Term::Call(f.clone(), args.iter().map(|a| go(self, a)).collect()),
            Term::CallVar(f, args) => Term::CallVar(f.clone(), args.iter().map(|a| go(self, a)).collect()),
            Term::Ctor(c, args) => Term::Ctor(c.clone(), args.iter().map(|a| go(self, a)).collect()),
            Term::List(items) => Term::List(items.iter().map(|a| go(self, a)).collect()),
            Term::Lam(ps, b) => Term::Lam(ps.clone(), Box::new(go(self, b))),
            Term::Ann(b, ty) => Term::Ann(Box::new(go(self, b)), ty.clone()),
            Term::Op(a, op, b, ty) => Term::Op(Box::new(go(self, a)), op, Box::new(go(self, b)), ty.clone()),
            Term::Cat(a, b) => Term::Cat(Box::new(go(self, a)), Box::new(go(self, b))),
            Term::And(a, b) => Term::And(Box::new(go(self, a)), Box::new(go(self, b))),
            Term::Or(a, b) => Term::Or(Box::new(go(self, a)), Box::new(go(self, b))),
            Term::Cons(a, b) => Term::Cons(Box::new(go(self, a)), Box::new(go(self, b))),
            Term::Tuple(a, b) => Term::Tuple(Box::new(go(self, a)), Box::new(go(self, b))),
            other => other.clone(),
        }
    }

    /// The unwrapped result type of a def by name (from the emitted defs).
    fn member_ret(&self, name: &str) -> Ty {
        let mode = self.instances.values().find(|i| name == i.name || name.starts_with(&format!("{}.", i.name))).map(|i| i.mode).unwrap_or(Mode::Pure);
        self.defs.iter().find(|d| d.name == name).map(|d| unwrap_ret(&d.ret, mode)).unwrap_or(Ty::Unit)
    }
}

/// A return type without its mode wrapper.
pub fn unwrap_ret(t: &Ty, mode: Mode) -> Ty {
    match (mode, t) {
        (Mode::Io, Ty::Io(inner)) => (**inner).clone(),
        (Mode::Result, Ty::Result(_, inner)) => (**inner).clone(),
        (_, other) => other.clone(),
    }
}
