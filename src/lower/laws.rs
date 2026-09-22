// src/lower/laws.rs
// Laws: a Fire law becomes a Bend `law` beside the defs it is about, with
// its quantified variables as `for` parameters and its hypotheses as
// parameters of equality type. A closed law is proven by `{==}`, a law
// over finite types by a case split; the rest stay open claims.

use super::body::FnCtx;
use super::*;

/// A law as the IR carries it: rendered lines.
impl<'a> Lower<'a> {
    pub fn emit_laws(&mut self) {
        for law in self.core.laws.clone() {
            if self.laws == Laws::Proven && law.proof == Proof::Open {
                continue;
            }
            let text = self.law_text(&law);
            self.defs.push(IrDef {
                name: format!("law:{}", law.name),
                is_unsafe: false,
                tmpl_types: vec![],
                tmpl_funcs: vec![],
                erased: vec![],
                params: vec![],
                ret: Ty::Unit,
                body: Body::term(Term::Var(text)),
            });
        }
    }

    /// The Bend source of a law and, when the compiler proves it, its proof.
    fn law_text(&mut self, law: &Law) -> String {
        let line = law.line;
        // a frame for the law's expressions: no def, pure, no parameters
        let mut ctx = FnCtx::law(self.core.main);
        let mut out = String::new();
        out.push_str(&format!("law {}:\n", law.name));
        let mut names: Vec<String> = Vec::new();
        for (v, t) in &law.vars {
            let ty = self.ty_in(&ctx, t, line);
            ctx.scope.push((v.clone(), ty.clone()));
            out.push_str(&format!("  for +{}: {}\n", local_name(v), ty.render()));
            names.push(local_name(v));
        }
        for (i, h) in law.hyps.iter().enumerate() {
            let mut pre = Vec::new();
            let t = self.expr(&mut ctx, h, &mut pre);
            out.push_str(&format!("  for h{}: {{{} == True{{}} : Bool}}\n", i, render_term(&t)));
            names.push(format!("h{}", i));
        }
        let claim = match &law.claim {
            Claim::Equation(a, b, t) => {
                let mut pre = Vec::new();
                let ta = self.expr(&mut ctx, a, &mut pre);
                let tb = self.expr(&mut ctx, b, &mut pre);
                let ty = self.ty_in(&ctx, t, line);
                format!("{{{} == {} : {}}}", render_term(&ta), render_term(&tb), ty.render())
            }
            Claim::Holds(x) => {
                let mut pre = Vec::new();
                let t = self.expr(&mut ctx, x, &mut pre);
                format!("{{{} == True{{}} : Bool}}", render_term(&t))
            }
        };
        out.push_str(&format!("  {}\n", claim));
        match law.proof {
            Proof::Closed => {
                out.push_str(&format!("\ndef {}():\n  {{==}}\n", law.name));
            }
            Proof::Finite => {
                out.push_str(&format!("\ndef {}({}):\n", law.name, names.join(", ")));
                let mut body = String::new();
                self.case_split(&law.vars, 0, 1, &mut body);
                out.push_str(&body);
            }
            Proof::Open => {}
        }
        out
    }

    /// Nested matches over every variable of a finite type, `{==}` at the
    /// leaves.
    fn case_split(&mut self, vars: &[(String, Type)], i: usize, indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
        if i == vars.len() {
            out.push_str(&format!("{}{{==}}\n", pad));
            return;
        }
        let (v, t) = &vars[i];
        let ctors: Vec<String> = match self.store.shallow(t) {
            Type::Bool => vec!["False{}".into(), "True{}".into()],
            Type::Data(tid, _) => (0..self.core.types[tid].ctors.len()).map(|ci| format!("{}{{}}", self.ctor_name(tid, ci))).collect(),
            _ => vec![],
        };
        out.push_str(&format!("{}match {}:\n", pad, local_name(v)));
        for c in ctors {
            out.push_str(&format!("{}  case {}:\n", pad, c));
            self.case_split(vars, i + 1, indent + 2, out);
        }
    }
}
