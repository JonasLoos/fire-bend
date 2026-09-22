// src/check/effects.rs
// Effect inference: a fixpoint over the call graph. A def's effect is what
// its body does directly, joined with the effects of every def it calls,
// of every function value it may invoke (the closure sets), and of the
// class methods its dictionaries resolve to at every instantiation. The
// same fixpoint computes which defs rely on `unsafe` code.

use super::*;
use std::collections::HashSet;

impl Checker {
    pub(crate) fn infer_effects(&mut self) {
        let n = self.defs.len();
        let mut edges: Vec<HashSet<DefId>> = vec![HashSet::new(); n];
        for &(caller, callee, _) in &self.calls {
            edges[caller].insert(callee);
        }
        // function values that may be invoked, and non-exhaustive matches
        for d in 0..n {
            let body = self.defs[d].body.clone();
            let mut invoked: Vec<Type> = Vec::new();
            let mut aborts = false;
            walk_block(&body, &mut |e: &Expr| match &e.kind {
                ExprKind::CallClosure(f, _) => invoked.push(f.ty.clone()),
                ExprKind::Dict { args, .. } | ExprKind::Builtin(_, args) => {
                    for a in args {
                        invoked.push(a.ty.clone());
                    }
                }
                ExprKind::Match(_, arms) => {
                    if !arms_exhaustive(arms, &self.types) {
                        aborts = true;
                    }
                }
                _ => {}
            });
            let mut stmts_abort = false;
            for_each_stmt(&body, &mut |s: &Stmt| {
                if let StmtKind::Match { arms, .. } = &s.kind {
                    if !arms_exhaustive(arms, &self.types) {
                        stmts_abort = true;
                    }
                }
            });
            if aborts || stmts_abort {
                self.defs[d].own_effect = self.defs[d].own_effect.join(Effect::ABORT);
            }
            for t in invoked {
                if let Type::Fn(_, _, c) = self.shallow(&t) {
                    for id in self.store.clos_set(c) {
                        if id < n {
                            edges[d].insert(id);
                        }
                    }
                }
            }
        }
        // constraints resolving to class methods: the def performing the
        // operation calls the method
        for c in &self.store.constraints {
            if let Some(Solution::Method(m, _, _)) = &c.solution {
                if c.user < n {
                    edges[c.user].insert(*m);
                }
            }
        }
        let mut effects: Vec<Effect> = self.defs.iter().map(|d| d.own_effect).collect();
        let mut unsafe_: Vec<bool> = self.defs.iter().map(|d| d.unsafe_).collect();
        // main performs IO (it is the IO entry point)
        effects[0] = effects[0].join(Effect::IO);
        let mut changed = true;
        while changed {
            changed = false;
            for d in 0..n {
                let mut e = effects[d];
                let mut u = unsafe_[d];
                for &c in &edges[d] {
                    e = e.join(effects[c]);
                    u = u || unsafe_[c];
                }
                if e != effects[d] || u != unsafe_[d] {
                    effects[d] = e;
                    unsafe_[d] = u;
                    changed = true;
                }
            }
        }
        self.effects_final = effects;
        self.unsafe_final = unsafe_;
    }
}

/// Visit every statement of a block, recursively.
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
