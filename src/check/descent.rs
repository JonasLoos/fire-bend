// src/check/descent.rs
// Termination: every def must get smaller on each self-call, by Bend's
// rule (a parameter matched into pieces, earlier parameters unchanged) or
// by the int-descent rule (an int parameter decreased by literals under a
// guard that keeps it non-negative, which the lowering turns into a Nat
// fuel). A def declared `unsafe` skips the check. Recursion through a
// lambda, a loop body or another def has no Bend image and is an error.

use super::*;
use std::collections::{HashMap, HashSet};

/// A self-call found in a body: its arguments and the facts (`p >= c`)
/// that hold there.
struct SelfCall {
    args: Vec<Expr>,
    facts: Vec<(String, i64)>,
    line: usize,
}

impl Checker {
    pub(crate) fn check_descent(&mut self) {
        self.descent_final = (0..self.defs.len()).map(|d| self.descent_of(d)).collect();
    }

    /// Cycles between defs, and recursion through nested defs or lambdas.
    pub(crate) fn check_cycles(&mut self) {
        let n = self.defs.len();
        // calls from a nested def or lambda count for its unit; a call from
        // a nested def to its own unit is recursion through a lambda
        let mut edges: Vec<HashSet<DefId>> = vec![HashSet::new(); n];
        let mut reported = HashSet::new();
        let calls = self.calls.clone();
        for &(caller, callee, line) in &calls {
            let cu = self.defs[caller].unit;
            let ce = self.defs[callee].unit;
            let callee_is_unit = callee == ce;
            if cu == ce && caller != callee {
                if callee_is_unit && !matches!(self.defs[callee].kind, DefKind::Method { .. } | DefKind::Ctor(_)) && reported.insert((caller, callee)) {
                    let who = if matches!(self.defs[caller].kind, DefKind::Lambda) { "a lambda" } else { "a nested def" };
                    self.error(line, format!("'{0}' is called from {1} inside its own body; Bend has no image for recursion through a lambda or a nested def: call '{0}' directly in its own body (recursing on a piece of a matched parameter, or on an int counting down), or drop the recursion and use a `for` loop with a worklist", self.defs[callee].name, who));
                }
                continue;
            }
            if cu != ce {
                edges[cu].insert(ce);
            }
        }
        // strongly connected components among units of size > 1
        let mut index = 0;
        let mut indices: HashMap<DefId, usize> = HashMap::new();
        let mut low: HashMap<DefId, usize> = HashMap::new();
        let mut stack: Vec<DefId> = Vec::new();
        let mut on_stack: HashSet<DefId> = HashSet::new();
        let mut sccs: Vec<Vec<DefId>> = Vec::new();
        fn strong(v: DefId, edges: &Vec<HashSet<DefId>>, index: &mut usize, indices: &mut HashMap<DefId, usize>, low: &mut HashMap<DefId, usize>, stack: &mut Vec<DefId>, on_stack: &mut HashSet<DefId>, sccs: &mut Vec<Vec<DefId>>) {
            indices.insert(v, *index);
            low.insert(v, *index);
            *index += 1;
            stack.push(v);
            on_stack.insert(v);
            let succ: Vec<DefId> = edges[v].iter().cloned().collect();
            for w in succ {
                if !indices.contains_key(&w) {
                    strong(w, edges, index, indices, low, stack, on_stack, sccs);
                    let lw = low[&w];
                    let lv = low[&v];
                    low.insert(v, lv.min(lw));
                } else if on_stack.contains(&w) {
                    let iw = indices[&w];
                    let lv = low[&v];
                    low.insert(v, lv.min(iw));
                }
            }
            if low[&v] == indices[&v] {
                let mut comp = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack.remove(&w);
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                sccs.push(comp);
            }
        }
        for v in 0..n {
            if self.defs[v].unit == v && !indices.contains_key(&v) {
                strong(v, &edges, &mut index, &mut indices, &mut low, &mut stack, &mut on_stack, &mut sccs);
            }
        }
        for comp in sccs {
            if comp.len() > 1 {
                let names: Vec<String> = comp.iter().map(|d| self.defs[*d].name.clone()).collect();
                let line = comp.iter().map(|d| self.defs[*d].line).min().unwrap_or(0);
                self.error(line, format!("mutual recursion between {} is not supported (Bend has none): merge them into one def, with a parameter saying which of them it is acting as", names.join(", ")));
            }
        }
    }

    fn descent_of(&mut self, d: DefId) -> Descent {
        let def = self.defs[d].clone();
        if matches!(def.kind, DefKind::Main) {
            return Descent::None;
        }
        let params: Vec<String> = def.params.iter().map(|p| p.name.clone()).collect();
        // a parameter that is reassigned is no longer the parameter
        let mut reassigned: HashSet<String> = HashSet::new();
        for_each_stmt(&def.body, &mut |s: &Stmt| {
            if let StmtKind::Assign { name, .. } = &s.kind
                && params.contains(name) {
                    reassigned.insert(name.clone());
                }
        });
        // self-calls, with the facts in scope at each, and the pieces
        let mut collector = Collector { ck: self, d, params: &params, facts: Vec::new(), pieces: HashMap::new(), calls: Vec::new(), in_loop: Vec::new() };
        collector.block(&def.body, false);
        let Collector { pieces, calls, in_loop, .. } = collector;
        for line in in_loop {
            self.error(line, format!("'{0}' calls itself inside a loop body; a loop body is its own def in Bend and cannot call the def around it: recurse over the list instead of looping (`match xs` with `[x, ...rest]`, calling '{0}' on `rest`), or drop the recursion and keep a worklist in the loop (`for _ in 0..limit` with `break` when it is empty)", def.name));
        }
        if calls.is_empty() {
            return Descent::None;
        }
        if def.unsafe_ {
            return Descent::Unsafe;
        }
        // structural, lexicographic: pick a parameter every remaining call
        // passes unchanged or shrinks (and some call shrinks); the calls that
        // shrink it are settled; repeat on the rest
        if calls.iter().all(|c| c.args.len() == params.len()) {
            let unchanged = |c: &SelfCall, j: usize| matches!(&c.args[j].kind, ExprKind::Var(v) if v == &params[j]);
            let smaller = |c: &SelfCall, j: usize| matches!(&c.args[j].kind, ExprKind::Var(v) if pieces.get(v) == Some(&j));
            let mut open: Vec<usize> = (0..calls.len()).collect();
            let mut order: Vec<usize> = Vec::new();
            while !open.is_empty() {
                let next = (0..params.len()).find(|&j| {
                    !order.contains(&j)
                        && !reassigned.contains(&params[j])
                        && open.iter().all(|&k| unchanged(&calls[k], j) || smaller(&calls[k], j))
                        && open.iter().any(|&k| smaller(&calls[k], j))
                });
                match next {
                    Some(j) => {
                        open.retain(|&k| !smaller(&calls[k], j));
                        order.push(j);
                    }
                    None => break,
                }
            }
            if open.is_empty() {
                return Descent::Structural(order);
            }
        }
        // fuel: an int parameter decreased by literals under a guard
        for (i, p) in params.iter().enumerate() {
            if reassigned.contains(p) {
                continue;
            }
            if !matches!(self.shallow(&def.params[i].ty), Type::Int) {
                continue;
            }
            let ok = calls.iter().all(|c| {
                if c.args.len() != params.len() {
                    return false;
                }
                let need = self.decrement_of(&c.args[i], p);
                match need {
                    Some(k) => c.facts.iter().any(|(v, lower)| v == p && *lower >= k),
                    None => false,
                }
            });
            if ok {
                return Descent::Fuel(i);
            }
        }
        let line = calls.first().map(|c| c.line).unwrap_or(def.line);
        let hint = if def.params.iter().any(|p| matches!(self.shallow(&p.ty), Type::Int)) {
            "recurse on a piece of a matched parameter, or on an int decreased by a literal (`n - 1`) under a guard such as `if n <= 0 do return ...`"
        } else {
            "recurse on a piece of a matched parameter (`match xs` with `[h, ...t]`, or a constructor pattern)"
        };
        self.error(line, format!("cannot show that '{}' terminates: {}; or mark it `unsafe def` to skip the check", def.name, hint));
        Descent::Unsafe
    }

    /// `p - k` with k >= 1 (needs p >= k) or `p / k` with k >= 2 (needs
    /// p >= 1): the least value of p the guard must establish.
    fn decrement_of(&self, arg: &Expr, p: &str) -> Option<i64> {
        if let ExprKind::Dict { id, args } = &arg.kind {
            let c = &self.store.constraints[*id];
            // `int(p / 2)`: the conversion of an int is the int itself
            if let (Class::Convert("int", _), [inner]) = (&c.class, args.as_slice())
                && matches!(self.shallow(&inner.ty), Type::Int) {
                    return self.decrement_of(inner, p);
                }
            if args.len() == 2
                && let (ExprKind::Var(v), ExprKind::Lit(Lit::Int(k))) = (&args[0].kind, &args[1].kind)
                    && v == p {
                        match c.class {
                            Class::Arith(ArithOp::Sub) if *k >= 1 => return Some(*k),
                            Class::Arith(ArithOp::Div) if *k >= 2 => return Some(1),
                            _ => {}
                        }
                    }
        }
        None
    }
}

/// Walks a def's body collecting its self-calls with the facts that hold
/// at each, and the variables that are pieces of a parameter (bound by a
/// match on it).
struct Collector<'a> {
    ck: &'a Checker,
    d: DefId,
    params: &'a [String],
    facts: Vec<(String, i64)>,
    pieces: HashMap<String, usize>,
    calls: Vec<SelfCall>,
    /// Lines of self-calls inside a loop body.
    in_loop: Vec<usize>,
}

impl Collector<'_> {
    fn block(&mut self, b: &Block, loop_body: bool) {
        for s in &b.stmts {
            match &s.kind {
                StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) | StmtKind::Return(value) => {
                    self.expr(value, loop_body);
                }
                StmtKind::If { cond, then, else_ } => {
                    self.expr(cond, loop_body);
                    let pos = facts_from(cond, true, self.params, self.ck);
                    let neg = facts_from(cond, false, self.params, self.ck);
                    let n0 = self.facts.len();
                    self.facts.extend(pos);
                    self.block(then, loop_body);
                    self.facts.truncate(n0);
                    self.facts.extend(neg.clone());
                    self.block(else_, loop_body);
                    self.facts.truncate(n0);
                    // an early return: the negation holds for the rest of the block
                    if else_.stmts.is_empty() && self.ck.block_always_returns(then) {
                        self.facts.extend(neg);
                    }
                }
                StmtKind::Match { subject, arms } => {
                    self.expr(subject, loop_body);
                    let of_param = self.param_of(subject);
                    for a in arms {
                        let n0 = self.facts.len();
                        self.arm(a, of_param, loop_body);
                        self.facts.truncate(n0);
                    }
                }
                StmtKind::For { iters, body, .. } => {
                    for it in iters {
                        match it {
                            Iter::Items(e, _) | Iter::Counter(e) => self.expr(e, loop_body),
                        }
                    }
                    self.block(body, true);
                }
                StmtKind::While { cond, body } => {
                    self.expr(cond, true);
                    self.block(body, true);
                }
                StmtKind::Break | StmtKind::Continue | StmtKind::Bind { .. } => {}
            }
        }
    }

    /// The parameter a match subject is (or is a piece of).
    fn param_of(&self, subject: &Expr) -> Option<usize> {
        match &subject.kind {
            ExprKind::Var(v) => self.params.iter().position(|p| p == v).or_else(|| self.pieces.get(v).cloned()),
            _ => None,
        }
    }

    /// A match arm; on a parameter, the names it binds are its pieces.
    fn arm(&mut self, a: &Arm, of_param: Option<usize>, loop_body: bool) {
        if let Some(pi) = of_param {
            let mut names = Vec::new();
            pattern_pieces(&a.pat, &mut names);
            for nm in names {
                self.pieces.insert(nm, pi);
            }
        }
        if let Some(g) = &a.guard {
            self.expr(g, loop_body);
        }
        self.expr(&a.body, loop_body);
    }

    fn expr(&mut self, e: &Expr, loop_body: bool) {
        match &e.kind {
            ExprKind::Call { def, args, .. } => {
                for a in args {
                    self.expr(a, loop_body);
                }
                if *def == self.d {
                    if loop_body {
                        self.in_loop.push(e.line);
                    }
                    self.calls.push(SelfCall { args: args.clone(), facts: self.facts.clone(), line: e.line });
                }
            }
            ExprKind::If(c, t, el) => {
                self.expr(c, loop_body);
                let pos = facts_from(c, true, self.params, self.ck);
                let neg = facts_from(c, false, self.params, self.ck);
                let n0 = self.facts.len();
                self.facts.extend(pos);
                self.expr(t, loop_body);
                self.facts.truncate(n0);
                self.facts.extend(neg);
                self.expr(el, loop_body);
                self.facts.truncate(n0);
            }
            ExprKind::Match(subject, arms) => {
                // unlike in a statement match, facts an arm leaves are kept
                self.expr(subject, loop_body);
                let of_param = self.param_of(subject);
                for a in arms {
                    self.arm(a, of_param, loop_body);
                }
            }
            ExprKind::Block(b) => self.block(b, loop_body),
            ExprKind::And(a, b) => {
                self.expr(a, loop_body);
                let pos = facts_from(a, true, self.params, self.ck);
                let n0 = self.facts.len();
                self.facts.extend(pos);
                self.expr(b, loop_body);
                self.facts.truncate(n0);
            }
            ExprKind::Or(a, b) => {
                self.expr(a, loop_body);
                let neg = facts_from(a, false, self.params, self.ck);
                let n0 = self.facts.len();
                self.facts.extend(neg);
                self.expr(b, loop_body);
                self.facts.truncate(n0);
            }
            ExprKind::List(items) | ExprKind::Con(_, _, items) | ExprKind::Builtin(_, items) | ExprKind::Dict { args: items, .. } => {
                for it in items {
                    self.expr(it, loop_body);
                }
            }
            ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => self.expr(o, loop_body),
            ExprKind::SetField(o, _, _, v) => {
                self.expr(o, loop_body);
                self.expr(v, loop_body);
            }
            ExprKind::CallClosure(f, args) => {
                self.expr(f, loop_body);
                for a in args {
                    self.expr(a, loop_body);
                }
            }
            ExprKind::FString(parts) => {
                for p in parts {
                    if let FPart::Expr(x, _) = p {
                        self.expr(x, loop_body);
                    }
                }
            }
            ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => {}
        }
    }
}

/// Names bound by a constructor or list pattern (pieces of the subject).
fn pattern_pieces(p: &Pat, out: &mut Vec<String>) {
    if !matches!(p, Pat::Bind(_)) {
        p.binders(out);
    }
}

/// Facts `p >= c` a condition establishes when it is true (`positive`) or
/// false. Comparisons are `Dict(Ord)(a, b)` meaning a < b, possibly under
/// `Not`; conjunctions and disjunctions combine.
fn facts_from(cond: &Expr, positive: bool, params: &[String], ck: &Checker) -> Vec<(String, i64)> {
    match &cond.kind {
        ExprKind::Not(inner) => facts_from(inner, !positive, params, ck),
        ExprKind::And(a, b) => {
            if positive {
                let mut f = facts_from(a, true, params, ck);
                f.extend(facts_from(b, true, params, ck));
                f
            } else {
                vec![]
            }
        }
        ExprKind::Or(a, b) => {
            if !positive {
                let mut f = facts_from(a, false, params, ck);
                f.extend(facts_from(b, false, params, ck));
                f
            } else {
                vec![]
            }
        }
        ExprKind::Dict { id, args } if args.len() == 2 => {
            let c = &ck.store.constraints[*id];
            match &c.class {
                // a < b
                Class::Ord => {
                    let (a, b) = (&args[0], &args[1]);
                    match (&a.kind, &b.kind) {
                        // k < p : p >= k + 1 when true
                        (ExprKind::Lit(Lit::Int(k)), ExprKind::Var(p)) if params.contains(p) => {
                            if positive { vec![(p.clone(), k + 1)] } else { vec![] }
                        }
                        // p < k : p >= k when false
                        (ExprKind::Var(p), ExprKind::Lit(Lit::Int(k))) if params.contains(p) => {
                            if positive { vec![] } else { vec![(p.clone(), *k)] }
                        }
                        _ => vec![],
                    }
                }
                _ => vec![],
            }
        }
        _ => vec![],
    }
}
