// src/check/laws.rs
// Laws: a claim about the program's defs, checked like an expression in a
// frame of its own, classified by how the compiler can prove it.

use super::*;

impl Checker {
    pub(crate) fn check_law(&mut self, name: &str, vars: &[(String, ast::Expression)], hyp: Option<&ast::Expression>, claim: &ast::Expression, line: usize) {
        self.line = line;
        if self.laws.iter().any(|l| l.name == name) {
            self.error(line, format!("law {} is declared twice", name));
            return;
        }
        // a law and a def share Bend's namespace (the proof is a def of the law's name)
        if self.lookup(name).is_some() || self.defs.iter().enumerate().any(|(i, d)| d.name == name && d.unit == i && !matches!(d.kind, DefKind::Lambda | DefKind::Law | DefKind::Main)) {
            self.error(line, format!("law {} has the name of a def; name the law differently", name));
            return;
        }
        // a frame of its own: a synthetic def that is never emitted
        let id = self.new_def(name, DefKind::Law, None, line);
        self.defs[id].state = State::InProgress;
        self.frames.push(Frame {
            def: id,
            kind: FrameKind::Plain,
            scopes: vec![Scope::default()],
            captures: Vec::new(),
            loop_depth: 0,
            returns: Vec::new(),
            ret: Type::Unit,
            mutates_member: false,
            piped: Vec::new(),
            unsafe_: false,
        });
        let mut tvars = Vec::new();
        for (v, t) in vars {
            let ty = self.annotation(t, line);
            self.declare(v, Binding::Local { ty: ty.clone(), mutable: false });
            tvars.push((v.clone(), ty));
        }
        let mut hyps = Vec::new();
        if let Some(h) = hyp {
            let x = self.check_expr(h, Some(&Type::Bool));
            self.unify(&Type::Bool, &x.ty, line);
            hyps.push(x);
        }
        let claim = match claim {
            ast::Expression::BinaryOp { left, op: ast::BinaryOperator::Eq, right } => {
                let a = self.check_expr(left, None);
                let b = self.check_expr(right, Some(&a.ty));
                self.unify(&a.ty, &b.ty, line);
                let t = a.ty.clone();
                Claim::Equation(a, b, t)
            }
            other => {
                let x = self.check_expr(other, Some(&Type::Bool));
                self.unify(&Type::Bool, &x.ty, line);
                Claim::Holds(x)
            }
        };
        if !self.pending.is_empty() {
            self.error(line, "a law cannot call a mutating method");
            self.pending.clear();
        }
        let frame = self.frames.pop().unwrap();
        for (n, _) in &frame.captures {
            self.error(line, format!("a law speaks about defs and types; '{}' is a value of the program (quantify it with `for`, or make it a def)", n));
        }
        self.defs[id].state = State::Done;
        self.solve_pending();
        // how it is proven
        let finite = !tvars.is_empty() && hyps.is_empty() && tvars.iter().all(|(_, t)| match self.shallow(t) {
            Type::Bool => true,
            Type::Data(tid, _) => self.types[tid].is_finite(),
            _ => false,
        });
        let proof = if tvars.is_empty() && hyps.is_empty() {
            Proof::Closed
        } else if finite {
            Proof::Finite
        } else {
            Proof::Open
        };
        // a variable of a function type cannot be quantified in Bend
        for (v, t) in &tvars {
            if let Type::Fn(..) = self.shallow(t) {
                self.error(line, format!("law variable {} has a function type; laws range over data", v));
            }
        }
        self.laws.push(Law { name: name.to_string(), vars: tvars, hyps, claim, proof, line });
    }

    /// After effects are known: a law may not mention an IO def or one that
    /// relies on unsafe code (the checker would hang on it).
    pub(crate) fn check_law_subjects(&mut self) {
        let laws = self.laws.clone();
        for (li, law) in laws.iter().enumerate() {
            let mut callees: Vec<DefId> = Vec::new();
            let mut visit = |e: &Expr| {
                match &e.kind {
                    ExprKind::Call { def, .. } | ExprKind::DefRef { def, .. } | ExprKind::Lambda(def) => callees.push(*def),
                    ExprKind::Dict { id, .. } => {
                        if let Some(Solution::Method(m, _, _)) = &self.store.constraints[*id].solution {
                            callees.push(*m);
                        }
                    }
                    _ => {}
                }
            };
            for h in &law.hyps {
                walk_expr(h, &mut visit);
            }
            match &law.claim {
                Claim::Equation(a, b, _) => {
                    walk_expr(a, &mut visit);
                    walk_expr(b, &mut visit);
                }
                Claim::Holds(x) => walk_expr(x, &mut visit),
            }
            // transitively
            let mut seen = std::collections::HashSet::new();
            let mut stack = callees;
            while let Some(d) = stack.pop() {
                if !seen.insert(d) {
                    continue;
                }
                for &(caller, callee, _) in &self.calls {
                    if caller == d {
                        stack.push(callee);
                    }
                }
            }
            // Bend's checker does not compute with floats: a law that does
            // is a claim, sampled by `fire --test`, not a proof
            if law.proof != Proof::Open {
                let mut floats = false;
                let mut note = |e: &Expr| {
                    if matches!(self.store.shallow(&e.ty), Type::Float) || matches!(e.kind, ExprKind::Lit(Lit::Float(_))) {
                        floats = true;
                    }
                };
                for h in &law.hyps {
                    walk_expr(h, &mut note);
                }
                match &law.claim {
                    Claim::Equation(a, b, _) => {
                        walk_expr(a, &mut note);
                        walk_expr(b, &mut note);
                    }
                    Claim::Holds(x) => walk_expr(x, &mut note),
                }
                for &d in &seen {
                    walk_block(&self.defs[d].body, &mut note);
                }
                if floats {
                    self.laws[li].proof = Proof::Open;
                }
            }
            for d in seen {
                let name = self.defs[d].name.clone();
                if self.effects_final.get(d).is_some_and(|e| e.io) {
                    self.error(law.line, format!("law {} mentions '{}', which performs IO; laws are about pure or fallible defs", law.name, name));
                }
                if self.unsafe_final.get(d).cloned().unwrap_or(false) {
                    self.error(law.line, format!("law {} mentions '{}', which relies on unsafe code; Bend's checker could not decide it", law.name, name));
                }
            }
        }
    }
}
