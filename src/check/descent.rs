// src/check/descent.rs
// Termination: every def must get smaller on each self-call, by Bend's
// rule (a parameter matched into pieces, earlier parameters unchanged) or
// by the int-descent rule (an int parameter decreased by literals under a
// guard that keeps it non-negative, which the lowering turns into a Nat
// fuel). A def declared `unsafe` skips the check. Recursion through a
// lambda, a loop body or another def has no Bend image and is an error.

use super::*;
use std::collections::{HashMap, HashSet};

/// A self-call found in a body: its arguments, the facts (`p >= c`) that
/// hold there, and the variables known to be pieces of each parameter.
struct SelfCall {
    args: Vec<Expr>,
    facts: Vec<(String, i64)>,
    line: usize,
}

impl Checker {
    pub(crate) fn check_descent(&mut self) {
        let n = self.defs.len();
        let mut out = vec![Descent::None; n];
        for d in 0..n {
            out[d] = self.descent_of(d);
        }
        self.descent_final = out;
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
                    self.error(line, format!("'{}' is called from {} inside its own body; recursion through a lambda or a nested def has no image in Bend: write the loop as a `for`, or the recursion directly", self.defs[callee].name, who));
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
                self.error(line, format!("mutual recursion between {} is not supported (Bend has none): merge them into one def", names.join(", ")));
            }
        }
    }

    fn descent_of(&mut self, d: DefId) -> Descent {
        let def = self.defs[d].clone();
        if matches!(def.kind, DefKind::Main) {
            return Descent::None;
        }
        // self-calls, with the facts and pieces in scope at each
        let mut calls: Vec<SelfCall> = Vec::new();
        let mut pieces: HashMap<String, usize> = HashMap::new();
        let mut in_loop_calls = Vec::new();
        let params: Vec<String> = def.params.iter().map(|p| p.name.clone()).collect();
        // a parameter that is reassigned is no longer the parameter
        let mut reassigned: HashSet<String> = HashSet::new();
        for_each_stmt_local(&def.body, &mut |s: &Stmt| {
            if let StmtKind::Assign { name, .. } = &s.kind {
                if params.contains(name) {
                    reassigned.insert(name.clone());
                }
            }
        });
        self.collect_calls(d, &def.body, &mut Vec::new(), &mut pieces, &params, &mut calls, &mut in_loop_calls, false);
        for line in in_loop_calls {
            self.error(line, format!("'{}' calls itself inside a loop body; a loop body is its own def in Bend and cannot reach back: write the loop as recursion, or the recursion as a loop", def.name));
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
        let hint = if params.iter().any(|p| matches!(self.shallow(&def.params[params.iter().position(|q| q == p).unwrap()].ty), Type::Int)) {
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
            if let (Class::Convert("int", _), [inner]) = (&c.class, args.as_slice()) {
                if matches!(self.shallow(&inner.ty), Type::Int) {
                    return self.decrement_of(inner, p);
                }
            }
            if args.len() == 2 {
                if let (ExprKind::Var(v), ExprKind::Lit(Lit::Int(k))) = (&args[0].kind, &args[1].kind) {
                    if v == p {
                        match c.class {
                            Class::Arith(ArithOp::Sub) if *k >= 1 => return Some(*k),
                            Class::Arith(ArithOp::Div) if *k >= 2 => return Some(1),
                            _ => {}
                        }
                    }
                }
            }
        }
        None
    }

    /// Walk a block collecting self-calls with their facts, and the
    /// variables that are pieces of a parameter (bound by a match on it).
    fn collect_calls(&self, d: DefId, b: &Block, facts: &mut Vec<(String, i64)>, pieces: &mut HashMap<String, usize>, params: &[String], calls: &mut Vec<SelfCall>, in_loop: &mut Vec<usize>, loop_body: bool) {
        let mut i = 0;
        while i < b.stmts.len() {
            let s = &b.stmts[i];
            match &s.kind {
                StmtKind::Let { value, .. } | StmtKind::Assign { value, .. } | StmtKind::Expr(value) | StmtKind::Return(value) => {
                    self.collect_expr(d, value, facts, pieces, params, calls, in_loop, loop_body);
                }
                StmtKind::If { cond, then, else_ } => {
                    self.collect_expr(d, cond, facts, pieces, params, calls, in_loop, loop_body);
                    let pos = facts_from(cond, true, params, self);
                    let neg = facts_from(cond, false, params, self);
                    let n0 = facts.len();
                    facts.extend(pos);
                    self.collect_calls(d, then, facts, pieces, params, calls, in_loop, loop_body);
                    facts.truncate(n0);
                    facts.extend(neg.clone());
                    self.collect_calls(d, else_, facts, pieces, params, calls, in_loop, loop_body);
                    facts.truncate(n0);
                    // an early return: the negation holds for the rest of the block
                    if else_.stmts.is_empty() && self.block_always_returns(then) {
                        facts.extend(neg);
                    }
                }
                StmtKind::Match { subject, arms } => {
                    self.collect_expr(d, subject, facts, pieces, params, calls, in_loop, loop_body);
                    let of_param = match &subject.kind {
                        ExprKind::Var(v) => params.iter().position(|p| p == v).or_else(|| pieces.get(v).cloned()),
                        _ => None,
                    };
                    for a in arms {
                        let n0 = facts.len();
                        if let Some(pi) = of_param {
                            let mut names = Vec::new();
                            pattern_pieces(&a.pat, &mut names);
                            for nm in names {
                                pieces.insert(nm, pi);
                            }
                        }
                        if let Some(g) = &a.guard {
                            self.collect_expr(d, g, facts, pieces, params, calls, in_loop, loop_body);
                        }
                        self.collect_expr(d, &a.body, facts, pieces, params, calls, in_loop, loop_body);
                        facts.truncate(n0);
                    }
                }
                StmtKind::For { iters, body, .. } => {
                    for it in iters {
                        match it {
                            Iter::Items(e, _) | Iter::Counter(e) => self.collect_expr(d, e, facts, pieces, params, calls, in_loop, loop_body),
                        }
                    }
                    self.collect_calls(d, body, facts, pieces, params, calls, in_loop, true);
                }
                StmtKind::While { cond, body } => {
                    self.collect_expr(d, cond, facts, pieces, params, calls, in_loop, true);
                    self.collect_calls(d, body, facts, pieces, params, calls, in_loop, true);
                }
                StmtKind::Break | StmtKind::Continue | StmtKind::Bind { .. } => {}
            }
            i += 1;
        }
    }

    fn collect_expr(&self, d: DefId, e: &Expr, facts: &mut Vec<(String, i64)>, pieces: &mut HashMap<String, usize>, params: &[String], calls: &mut Vec<SelfCall>, in_loop: &mut Vec<usize>, loop_body: bool) {
        match &e.kind {
            ExprKind::Call { def, args, .. } => {
                for a in args {
                    self.collect_expr(d, a, facts, pieces, params, calls, in_loop, loop_body);
                }
                if *def == d {
                    if loop_body {
                        in_loop.push(e.line);
                    }
                    calls.push(SelfCall { args: args.clone(), facts: facts.clone(), line: e.line });
                }
            }
            ExprKind::If(c, t, el) => {
                self.collect_expr(d, c, facts, pieces, params, calls, in_loop, loop_body);
                let pos = facts_from(c, true, params, self);
                let neg = facts_from(c, false, params, self);
                let n0 = facts.len();
                facts.extend(pos);
                self.collect_expr(d, t, facts, pieces, params, calls, in_loop, loop_body);
                facts.truncate(n0);
                facts.extend(neg);
                self.collect_expr(d, el, facts, pieces, params, calls, in_loop, loop_body);
                facts.truncate(n0);
            }
            ExprKind::Match(subject, arms) => {
                self.collect_expr(d, subject, facts, pieces, params, calls, in_loop, loop_body);
                let of_param = match &subject.kind {
                    ExprKind::Var(v) => params.iter().position(|p| p == v).or_else(|| pieces.get(v).cloned()),
                    _ => None,
                };
                for a in arms {
                    if let Some(pi) = of_param {
                        let mut names = Vec::new();
                        pattern_pieces(&a.pat, &mut names);
                        for nm in names {
                            pieces.insert(nm, pi);
                        }
                    }
                    if let Some(g) = &a.guard {
                        self.collect_expr(d, g, facts, pieces, params, calls, in_loop, loop_body);
                    }
                    self.collect_expr(d, &a.body, facts, pieces, params, calls, in_loop, loop_body);
                }
            }
            ExprKind::Block(b) => self.collect_calls(d, b, facts, pieces, params, calls, in_loop, loop_body),
            ExprKind::And(a, b) => {
                self.collect_expr(d, a, facts, pieces, params, calls, in_loop, loop_body);
                let pos = facts_from(a, true, params, self);
                let n0 = facts.len();
                facts.extend(pos);
                self.collect_expr(d, b, facts, pieces, params, calls, in_loop, loop_body);
                facts.truncate(n0);
            }
            ExprKind::Or(a, b) => {
                self.collect_expr(d, a, facts, pieces, params, calls, in_loop, loop_body);
                let neg = facts_from(a, false, params, self);
                let n0 = facts.len();
                facts.extend(neg);
                self.collect_expr(d, b, facts, pieces, params, calls, in_loop, loop_body);
                facts.truncate(n0);
            }
            ExprKind::List(items) | ExprKind::Con(_, _, items) | ExprKind::Builtin(_, items) => {
                for it in items {
                    self.collect_expr(d, it, facts, pieces, params, calls, in_loop, loop_body);
                }
            }
            ExprKind::Dict { args, .. } => {
                for it in args {
                    self.collect_expr(d, it, facts, pieces, params, calls, in_loop, loop_body);
                }
            }
            ExprKind::Field(o, _, _) | ExprKind::Not(o) | ExprKind::Abort(o) => self.collect_expr(d, o, facts, pieces, params, calls, in_loop, loop_body),
            ExprKind::SetField(o, _, _, v) => {
                self.collect_expr(d, o, facts, pieces, params, calls, in_loop, loop_body);
                self.collect_expr(d, v, facts, pieces, params, calls, in_loop, loop_body);
            }
            ExprKind::CallClosure(f, args) => {
                self.collect_expr(d, f, facts, pieces, params, calls, in_loop, loop_body);
                for a in args {
                    self.collect_expr(d, a, facts, pieces, params, calls, in_loop, loop_body);
                }
            }
            ExprKind::FString(parts) => {
                for p in parts {
                    if let FPart::Expr(x, _) = p {
                        self.collect_expr(d, x, facts, pieces, params, calls, in_loop, loop_body);
                    }
                }
            }
            ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::EmptyMap | ExprKind::Lambda(_) | ExprKind::DefRef { .. } | ExprKind::SelfValue(_) => {}
        }
    }
}

/// Names bound by a constructor or list pattern (pieces of the subject).
fn pattern_pieces(p: &Pat, out: &mut Vec<String>) {
    match p {
        Pat::Con(_, _, subs) => {
            for s in subs {
                match s {
                    Pat::Bind(n) => out.push(n.clone()),
                    other => pattern_pieces(other, out),
                }
            }
        }
        Pat::List(items, rest) => {
            for s in items {
                match s {
                    Pat::Bind(n) => out.push(n.clone()),
                    other => pattern_pieces(other, out),
                }
            }
            if let Some(Some(r)) = rest {
                out.push(r.clone());
            }
        }
        _ => {}
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
                Class::Eq => {
                    // p == k gives no lower bound; p != k neither
                    vec![]
                }
                _ => vec![],
            }
        }
        _ => vec![],
    }
}

/// Visit every statement of a block, not descending into nested lambdas
/// (which are separate defs anyway).
pub(crate) fn for_each_stmt_local(b: &Block, f: &mut dyn FnMut(&Stmt)) {
    super::effects::for_each_stmt(b, f)
}
