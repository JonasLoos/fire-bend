// src/testgen.rs
// `fire --test`: every law becomes a property check. The test program keeps
// the program's types, defs and top-level bindings (defs may read them),
// drops its other top-level statements, and adds one predicate def per law
// and a loop over generated instances of the law's variable types. It is
// then compiled like any program.

use crate::ast::{self, Expression as E, NumberLiteral, Pattern, Statement as S, Stmt};
use std::collections::HashSet;

use crate::core::{walk_expr, DataKind, ExprKind, Program, StmtKind};
use crate::types::*;
use crate::Diag;

/// How many cases a law is checked on, at most.
const MAX_CASES: usize = 400;

pub fn test_program(program: &ast::Program, core: &Program) -> Result<ast::Program, Vec<Diag>> {
    let mut out: Vec<Stmt> = Vec::new();
    let mut checks: Vec<Stmt> = Vec::new();
    let mut diags = Vec::new();
    let needed = needed_bindings(core);
    for s in &program.statements {
        match &s.node {
            S::Def { .. } | S::TypeDecl { .. } | S::Documentation(_) | S::Comment(_) => out.push(s.clone()),
            // a top-level binding stays when a def reads it (the statements
            // that would complete it, loops say, are dropped)
            S::Declaration { pattern, value, .. } => {
                if matches!(value, E::Import(_)) || binds_any(pattern, &needed) {
                    out.push(s.clone());
                }
            }
            S::Assignment { targets, value } => {
                if matches!(value, E::Import(_)) || targets.iter().any(|(p, _)| binds_any(p, &needed)) {
                    out.push(s.clone());
                }
            }
            S::Law { name, vars, hyp, claim } => {
                let Some(law) = core.laws.iter().find(|l| &l.name == name) else {
                    continue;
                };
                // instances per variable, trimmed so that the product stays small
                let mut pools: Vec<Vec<E>> = Vec::new();
                for (v, t) in &law.vars {
                    match instances(&core.store, core, t, 2) {
                        Some(xs) if !xs.is_empty() => pools.push(xs),
                        _ => {
                            diags.push(Diag { line: s.line, message: format!("law {}: no instances to test the variable {} with (its type has no generator)", name, v) });
                            pools.push(vec![]);
                        }
                    }
                }
                let n = pools.len().max(1);
                let per = ((MAX_CASES as f64).powf(1.0 / n as f64).floor() as usize).max(2);
                for p in pools.iter_mut() {
                    p.truncate(per);
                }
                let (defs, run) = check_law(name, vars, hyp.as_ref(), claim, &pools, s.line);
                out.extend(defs);
                checks.extend(run);
            }
            _ => {}
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }
    if checks.is_empty() {
        checks.push(print(E::Str("no laws to test".into()), 0));
    } else {
        // a failing law fails the run
        checks.push(stmt(S::Expression(call("assert", vec![E::Identifier("__all_hold".into()), E::Str("some laws do not hold".into())])), 0));
        out.push(var("__all_hold", E::Boolean(true), 0));
    }
    out.extend(checks);
    Ok(ast::Program { statements: out })
}

/// The top-level bindings the program's defs read: what they capture, and
/// what the values of those bindings read in turn.
fn needed_bindings(core: &Program) -> HashSet<String> {
    let mut needed: HashSet<String> = HashSet::new();
    for d in &core.defs {
        if d.id != core.main {
            needed.extend(d.captures.iter().map(|(n, _)| n.clone()));
        }
    }
    let main = &core.defs[core.main];
    loop {
        let before = needed.len();
        for st in &main.body.stmts {
            if let StmtKind::Let { name, value } | StmtKind::Assign { name, value } = &st.kind
                && needed.contains(name)
            {
                walk_expr(value, &mut |e| {
                    if let ExprKind::Var(v) = &e.kind {
                        needed.insert(v.clone());
                    }
                });
            }
        }
        if needed.len() == before {
            return needed;
        }
    }
}

/// Whether a binding pattern binds one of the names.
fn binds_any(p: &Pattern, names: &HashSet<String>) -> bool {
    match p {
        Pattern::Identifier(n) => names.contains(n),
        Pattern::Typed { pattern, .. } => binds_any(pattern, names),
        Pattern::List(items) => items.iter().any(|i| binds_any(i, names)),
        Pattern::Rest(Some(n)) => names.contains(n),
        Pattern::Object(entries) => entries.iter().any(|(_, p)| binds_any(p, names)),
        Pattern::Ctor(_, subs) => subs.iter().any(|i| binds_any(i, names)),
        _ => false,
    }
}

fn stmt(node: S, line: usize) -> Stmt {
    Stmt { node, line }
}

fn call(f: &str, args: Vec<E>) -> E {
    E::Call { function: Box::new(E::Identifier(f.into())), args, named_args: vec![] }
}

fn int(i: i64) -> E {
    num(&i.to_string())
}

/// A number literal from its text, negated when it starts with `-`.
fn num(text: &str) -> E {
    match text.strip_prefix('-') {
        Some(n) => E::UnaryOp { op: ast::UnaryOperator::Minus, operand: Box::new(num(n)) },
        None => E::Number(NumberLiteral::Decimal(text.into())),
    }
}

fn print(value: E, line: usize) -> Stmt {
    stmt(S::Expression(call("print", vec![value])), line)
}

/// `var name = value`
fn var(name: &str, value: E, line: usize) -> Stmt {
    stmt(S::Declaration { is_public: false, is_mutable: true, pattern: Pattern::Identifier(name.into()), value }, line)
}

/// `def __law_name(x: T, ...)`: whether the claim holds for these values;
/// `def __hyp_name(x: T, ...)`: whether they meet the hypothesis.
fn predicate_def(prefix: &str, name: &str, vars: &[(String, E)], body: &E, line: usize) -> Stmt {
    let params = vars.iter()
        .map(|(v, t)| ast::Param::plain(Pattern::Typed { pattern: Box::new(Pattern::Identifier(v.clone())), type_expr: t.clone() }, None))
        .collect();
    stmt(S::Def { is_public: false, is_unsafe: false, name: format!("{}_{}", prefix, name), params, return_type: None, body: vec![stmt(S::Return(Some(body.clone())), line)] }, line)
}

fn text(parts: Vec<ast::FStringPart>) -> E {
    E::FString(parts)
}

fn t(s: &str) -> ast::FStringPart {
    ast::FStringPart::Text(s.into())
}

fn v(name: &str) -> ast::FStringPart {
    ast::FStringPart::Expression(E::Identifier(name.into()), None)
}

fn set(name: &str, value: E, line: usize) -> Stmt {
    stmt(S::Assignment { targets: vec![(Pattern::Identifier(name.into()), ast::AssignmentOp::Assign)], value }, line)
}

fn when(cond: E, body: Vec<Stmt>, else_body: Option<Vec<Stmt>>, line: usize) -> Stmt {
    stmt(S::If { condition: cond, body, elif_branches: vec![], else_body }, line)
}

fn eq(a: E, b: E) -> E {
    E::BinaryOp { left: Box::new(a), op: ast::BinaryOperator::Eq, right: Box::new(b) }
}

fn not(a: E) -> E {
    E::UnaryOp { op: ast::UnaryOperator::Not, operand: Box::new(a) }
}

/// The law's defs and the loops over the instances; the first
/// counterexample is reported, and a law whose hypothesis no generated case
/// meets is reported as untested.
fn check_law(name: &str, vars: &[(String, E)], hyp: Option<&E>, claim: &E, pools: &[Vec<E>], line: usize) -> (Vec<Stmt>, Vec<Stmt>) {
    let mut defs = vec![predicate_def("__law", name, vars, claim, line)];
    if let Some(h) = hyp {
        defs.push(predicate_def("__hyp", name, vars, h, line));
    }
    let bad = format!("__bad_{}", name);
    let met = format!("__met_{}", name);
    let args: Vec<E> = vars.iter().map(|(v, _)| E::Identifier(v.clone())).collect();
    // "x = {x}, t = {t}"
    let mut parts = Vec::new();
    for (i, (n, _)) in vars.iter().enumerate() {
        if i > 0 {
            parts.push(t(", "));
        }
        parts.push(t(&format!("{} = ", n)));
        parts.push(v(n));
    }
    if vars.is_empty() {
        parts.push(t("its sides"));
    }
    let record = when(eq(E::Identifier(bad.clone()), E::Str(String::new())), vec![set(&bad, text(parts), line)], None, line);
    let test = when(not(call(&format!("__law_{}", name), args.clone())), vec![record], None, line);
    let mut inner = match hyp {
        Some(_) => vec![when(call(&format!("__hyp_{}", name), args), vec![
            stmt(S::Assignment { targets: vec![(Pattern::Identifier(met.clone()), ast::AssignmentOp::Compound(ast::BinaryOperator::Add))], value: int(1) }, line),
            test,
        ], None, line)],
        None => vec![test],
    };
    for (i, (n, _)) in vars.iter().enumerate().rev() {
        inner = vec![stmt(S::For { pattern: Pattern::Identifier(n.clone()), iterables: vec![E::List(pools[i].clone())], body: inner }, line)];
    }
    let cases: usize = pools.iter().map(|p| p.len()).product();
    let ok = match (vars.is_empty(), hyp.is_some()) {
        (true, _) => text(vec![t(&format!("law {}: holds", name))]),
        (false, false) => text(vec![t(&format!("law {}: holds on {} generated cases", name, cases))]),
        (false, true) => text(vec![t(&format!("law {}: holds on the ", name)), v(&met), t(&format!(" of {} generated cases that meet its hypothesis", cases))]),
    };
    let fail = text(vec![t(&format!("law {}: FAILS for ", name)), v(&bad)]);
    let mut out = vec![var(&bad, E::Str(String::new()), line), var(&met, int(0), line)];
    out.extend(inner);
    let report_ok = if hyp.is_some() {
        when(eq(E::Identifier(met.clone()), int(0)),
            vec![print(text(vec![t(&format!("law {}: untested, no generated case meets its hypothesis", name))]), line)],
            Some(vec![print(ok, line)]), line)
    } else {
        print(ok, line)
    };
    out.push(when(eq(E::Identifier(bad.clone()), E::Str(String::new())), vec![report_ok], Some(vec![
        print(fail, line),
        set("__all_hold", E::Boolean(false), line),
    ]), line));
    (defs, out)
}

/// Sample values of a type, as Fire expressions: small, varied, and for a
/// declared type every constructor down to `depth` levels of nesting.
fn instances(store: &TypeStore, core: &Program, t: &Type, depth: usize) -> Option<Vec<E>> {
    match store.shallow(t) {
        Type::Int | Type::Var(_) => Some([0, 1, -1, 2, 5, -7, 42, 1000].iter().map(|i| int(*i)).collect()),
        Type::Float => Some(["0.0", "1.5", "-2.25", "10.0"].iter().map(|s| num(s)).collect()),
        Type::Str => Some(["", "a", "ab", "hello", "Z z"].iter().map(|s| E::Str((*s).into())).collect()),
        Type::Bool => Some(vec![E::Boolean(false), E::Boolean(true)]),
        Type::Unit => Some(vec![E::Nothing]),
        Type::List(e) => {
            let xs = instances(store, core, &e, depth.saturating_sub(1))?;
            let a = xs.first().cloned()?;
            let b = xs.get(1).cloned().unwrap_or(a.clone());
            let c = xs.get(2).cloned().unwrap_or(b.clone());
            // empty, one, unordered, and repeated elements
            Some(vec![
                E::List(vec![]),
                E::List(vec![a.clone()]),
                E::List(vec![b.clone(), a.clone()]),
                E::List(vec![a.clone(), c.clone(), b.clone()]),
                E::List(vec![a.clone(), a.clone()]),
                E::List(vec![b.clone(), c, a, b]),
            ])
        }
        Type::Data(tid, args) if tid >= BUILTIN_TYPES && matches!(core.types[tid].kind, DataKind::Declared) => {
            let dt = core.types[tid].clone();
            let subst: Vec<(TVar, Type)> = dt.params.iter().cloned().zip(args.iter().cloned()).collect();
            let mut out = Vec::new();
            for c in &dt.ctors {
                if c.fields.is_empty() {
                    out.push(E::Identifier(c.name.clone()));
                    continue;
                }
                let field_tys: Vec<Type> = c.fields.iter().map(|f| store.substitute(&f.ty, &subst)).collect();
                // at the last level only constructors over plain values
                if depth == 0 && field_tys.iter().any(|ft| !plain(store, ft)) {
                    continue;
                }
                let mut field_pools = Vec::new();
                for ft in &field_tys {
                    field_pools.push(instances(store, core, ft, depth.saturating_sub(1))?);
                }
                // a field with no instances leaves the constructor out
                if field_pools.iter().any(|p| p.is_empty()) {
                    continue;
                }
                // a few combinations: the i-th instance of every field
                let most = field_pools.iter().map(|p| p.len()).max().unwrap_or(0).min(4);
                for i in 0..most {
                    let fields: Vec<E> = field_pools.iter().map(|p| p[i % p.len()].clone()).collect();
                    out.push(call(&c.name, fields));
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// A type whose instances need no further nesting: scalars and lists of them.
fn plain(store: &TypeStore, t: &Type) -> bool {
    match store.shallow(t) {
        Type::Int | Type::Var(_) | Type::Float | Type::Str | Type::Bool | Type::Unit => true,
        Type::List(e) => plain(store, &e),
        _ => false,
    }
}
