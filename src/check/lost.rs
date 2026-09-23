// src/check/lost.rs
// Changes nothing reads. A statement whose only effect is to change a
// binding (`p.x = 1`, `xs.push(v)`, `m[k] = v`, a mutating method) is an
// error when nothing reads the binding afterwards: values are copied, so
// the change reaches nothing. The usual cause is changing a loop's element
// or a parameter and expecting the list or the caller's value to change.
//
// A backward liveness walk over each def's Core body: a name is live when
// something may read it later. Loops run to a fixpoint (their variables
// are new each turn); a block nested inside an expression sees everything
// the expression reads as read afterwards, which can only keep a change.

use super::*;
use std::collections::{HashMap, HashSet};

type Live = HashSet<String>;

#[derive(Clone, Copy, PartialEq)]
enum Origin {
    Param,
    Item,
    Local,
}

struct Walk<'a> {
    ck: &'a Checker,
    def: DefId,
    report: bool,
    origin: HashMap<String, Origin>,
    found: Vec<(usize, String, Origin)>,
    /// Live at each enclosing loop's exit (`break`) and head (`continue`).
    loops: Vec<(Live, Live)>,
}

impl Checker {
    pub(crate) fn check_lost_changes(&mut self) {
        let mut errors = Vec::new();
        for d in 0..self.defs.len() {
            if matches!(self.defs[d].kind, DefKind::Law) || !self.changes.iter().any(|(cd, _, _)| *cd == d) {
                continue;
            }
            let mut w = Walk { ck: self, def: d, report: true, origin: HashMap::new(), found: Vec::new(), loops: Vec::new() };
            for p in &self.defs[d].params {
                w.origin.insert(p.name.clone(), Origin::Param);
            }
            w.block(&self.defs[d].body, &Live::new());
            let mut found = w.found;
            found.sort_by_key(|(l, n, _)| (*l, n.clone()));
            found.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
            let def = self.defs[d].name.clone();
            for (line, name, origin) in found {
                errors.push((line, lost_message(&name, origin, &def, &self.defs[d].kind)));
            }
        }
        for (line, m) in errors {
            self.error(line, m);
        }
    }
}

fn lost_message(name: &str, origin: Origin, def: &str, kind: &DefKind) -> String {
    match origin {
        Origin::Item => format!("this changes '{0}', the loop's copy of an element, and nothing reads it before the turn ends: the list is unchanged. Change the list itself (`xs[i] = ...` over `for i, x in 0.., xs`) or build a new one (`xs = for x in xs do ...`)", name),
        Origin::Param if !matches!(kind, DefKind::Lambda) => format!("this changes '{0}', a copy of what the caller passed, and nothing reads it before '{1}' returns: the caller's value is unchanged. Return '{0}' and assign the result where '{1}' is called, or make '{1}' a method of its class", name, def),
        _ => format!("this changes '{0}', and nothing reads '{0}' afterwards: the change has no effect (values are copied, so no other binding sees it)", name),
    }
}

impl Walk<'_> {
    fn block(&mut self, b: &Block, after: &Live) -> Live {
        let mut live = after.clone();
        for s in b.stmts.iter().rev() {
            live = self.stmt(s, &live);
        }
        live
    }

    fn stmt(&mut self, s: &Stmt, after: &Live) -> Live {
        match &s.kind {
            StmtKind::Let { name, value } => {
                let mut l = after.clone();
                l.remove(name);
                self.expr(value, &l)
            }
            StmtKind::Assign { name, value } => {
                if self.report && !after.contains(name) && self.ck.changes.contains(&(self.def, s.line, name.clone())) {
                    let o = self.origin.get(name).copied().unwrap_or(Origin::Local);
                    self.found.push((s.line, name.clone(), o));
                }
                let mut l = after.clone();
                l.remove(name);
                self.expr(value, &l)
            }
            StmtKind::Expr(e) => self.expr(e, after),
            StmtKind::Return(e) => self.expr(e, &Live::new()),
            StmtKind::Break => self.loops.last().map(|(b, _)| b.clone()).unwrap_or_default(),
            StmtKind::Continue => self.loops.last().map(|(_, c)| c.clone()).unwrap_or_default(),
            StmtKind::If { cond, then, else_ } => {
                let mut l = self.block(then, after);
                l.extend(self.block(else_, after));
                self.expr(cond, &l)
            }
            StmtKind::Match { subject, arms } => self.arms(subject, arms, after),
            StmtKind::For { patterns, iters, body } => {
                let mut binders = Vec::new();
                for p in patterns {
                    p.binders(&mut binders);
                }
                let saved: Vec<(String, Option<Origin>)> = binders.iter().map(|b| (b.clone(), self.origin.insert(b.clone(), Origin::Item))).collect();
                let mut l = self.loop_head(body, after, &binders, None);
                for (b, o) in saved {
                    match o {
                        Some(o) => self.origin.insert(b, o),
                        None => self.origin.remove(&b),
                    };
                }
                for it in iters.iter().rev() {
                    let e = match it {
                        Iter::Items(e, _) | Iter::Counter(e) => e,
                    };
                    l = self.expr(e, &l);
                }
                l
            }
            StmtKind::While { cond, body } => self.loop_head(body, after, &[], Some(cond)),
            StmtKind::Bind { name, def } => {
                let mut l = after.clone();
                l.remove(name);
                l.extend(self.ck.defs[*def].captures.iter().map(|(n, _)| n.clone()));
                l
            }
        }
    }

    /// What is live at a loop's head: the body runs again with what it
    /// leaves live, so a fixpoint (sets only grow). The loop's own names
    /// are new each turn. Changes are reported on a last pass.
    fn loop_head(&mut self, body: &Block, after: &Live, binders: &[String], cond: Option<&Expr>) -> Live {
        let report = self.report;
        self.report = false;
        let mut head = after.clone();
        loop {
            self.loops.push((after.clone(), head.clone()));
            let mut inb = self.block(body, &head);
            self.loops.pop();
            for b in binders {
                inb.remove(b);
            }
            let mut next = after.clone();
            next.extend(inb);
            if let Some(c) = cond {
                next = self.expr(c, &next);
            }
            if next == head {
                break;
            }
            head = next;
        }
        self.report = report;
        if report {
            self.loops.push((after.clone(), head.clone()));
            self.block(body, &head);
            self.loops.pop();
        }
        head
    }

    /// A match: live before it is what its subject and any arm read.
    fn arms(&mut self, subject: &Expr, arms: &[Arm], after: &Live) -> Live {
        let mut l = Live::new();
        for a in arms {
            l.extend(self.arm(a, after));
        }
        self.expr(subject, &l)
    }

    fn arm(&mut self, a: &Arm, after: &Live) -> Live {
        let mut l = self.expr(&a.body, after);
        let mut names = Vec::new();
        a.pat.binders(&mut names);
        for n in names {
            l.remove(&n);
        }
        if let Some(g) = &a.guard {
            l = self.expr(g, &l);
        }
        l
    }

    fn expr(&mut self, e: &Expr, after: &Live) -> Live {
        match &e.kind {
            ExprKind::Block(b) => self.block(b, after),
            ExprKind::If(c, t, el) => {
                let mut l = self.expr(t, after);
                l.extend(self.expr(el, after));
                self.expr(c, &l)
            }
            ExprKind::Match(subject, arms) => self.arms(subject, arms, after),
            _ => {
                let mut out = after.clone();
                walk_expr(e, &mut |x: &Expr| match &x.kind {
                    ExprKind::Var(n) => {
                        out.insert(n.clone());
                    }
                    // a closure or a def with captures reads them
                    ExprKind::Lambda(d) | ExprKind::Call { def: d, .. } | ExprKind::DefRef { def: d, .. } => {
                        out.extend(self.ck.defs[*d].captures.iter().map(|(n, _)| n.clone()));
                    }
                    _ => {}
                });
                let mut blocks = Vec::new();
                outer_blocks(e, &mut blocks);
                for b in blocks {
                    self.block(b, &out);
                }
                out
            }
        }
    }
}

/// The blocks inside an expression that no other block of it contains.
fn outer_blocks<'e>(e: &'e Expr, out: &mut Vec<&'e Block>) {
    let sub = |x: &'e Expr, out: &mut Vec<&'e Block>| outer_blocks(x, out);
    match &e.kind {
        ExprKind::Block(b) => out.push(b),
        ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => {}
        ExprKind::List(items) | ExprKind::Con(_, _, items) | ExprKind::Builtin(_, items) => items.iter().for_each(|i| sub(i, out)),
        ExprKind::Call { args, .. } | ExprKind::Dict { args, .. } => args.iter().for_each(|i| sub(i, out)),
        ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => sub(o, out),
        ExprKind::SetField(o, _, _, v) | ExprKind::And(o, v) | ExprKind::Or(o, v) => {
            sub(o, out);
            sub(v, out);
        }
        ExprKind::CallClosure(f, args) => {
            sub(f, out);
            args.iter().for_each(|i| sub(i, out));
        }
        ExprKind::If(c, t, el) => {
            sub(c, out);
            sub(t, out);
            sub(el, out);
        }
        ExprKind::Match(s, arms) => {
            sub(s, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    sub(g, out);
                }
                sub(&a.body, out);
            }
        }
        ExprKind::FString(parts) => {
            for p in parts {
                if let FPart::Expr(x, _) = p {
                    sub(x, out);
                }
            }
        }
    }
}
