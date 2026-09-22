// src/testgen.rs
// `fire --test`: every law becomes a property check. The test program keeps
// the program's types, defs and top-level bindings (defs may read them),
// drops its other top-level statements, and adds one predicate def per law
// and a loop over generated instances of the law's variable types. It is
// then compiled like any program.

use crate::ast::{self, Expression as E, NumberLiteral, Pattern, Statement as S, Stmt};
use crate::core::{DataKind, Program};
use crate::types::*;
use crate::Diag;

/// How many cases a law is checked on, at most.
const MAX_CASES: usize = 400;

pub fn test_program(program: &ast::Program, core: &Program) -> Result<ast::Program, Vec<Diag>> {
    let mut store = core.store.clone();
    let mut out: Vec<Stmt> = Vec::new();
    let mut checks: Vec<Stmt> = Vec::new();
    let mut diags = Vec::new();
    for s in &program.statements {
        match &s.node {
            S::Def { .. } | S::TypeDecl { .. } | S::Declaration { .. } | S::Assignment { .. } | S::Documentation(_) | S::Comment(_) => out.push(s.clone()),
            S::Law { name, vars, hyp, claim } => {
                let law = match core.laws.iter().find(|l| &l.name == name) {
                    Some(l) => l.clone(),
                    None => continue,
                };
                // instances per variable, trimmed so that the product stays small
                let mut pools: Vec<Vec<E>> = Vec::new();
                for (v, t) in &law.vars {
                    match instances(&mut store, core, t, 2) {
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
                out.push(predicate_def(name, vars, hyp.as_ref(), claim, s.line));
                checks.extend(check_loop(name, vars, &pools, s.line));
            }
            _ => {}
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }
    if checks.is_empty() {
        checks.push(stmt(S::Expression(call("print", vec![E::Str("no laws to test".into())])), 0));
    } else {
        // a failing law fails the run
        checks.push(stmt(S::Expression(call("assert", vec![E::Identifier("__all_hold".into()), E::Str("some laws do not hold".into())])), 0));
        out.push(stmt(S::Declaration { is_public: false, is_mutable: true, pattern: Pattern::Identifier("__all_hold".into()), value: E::Boolean(true) }, 0));
    }
    out.extend(checks);
    Ok(ast::Program { statements: out })
}

fn stmt(node: S, line: usize) -> Stmt {
    Stmt { node, line }
}

fn call(f: &str, args: Vec<E>) -> E {
    E::Call { function: Box::new(E::Identifier(f.into())), args, named_args: vec![] }
}

fn int(i: i64) -> E {
    if i < 0 {
        E::UnaryOp { op: ast::UnaryOperator::Minus, operand: Box::new(int(-i)) }
    } else {
        E::Number(NumberLiteral::Decimal(i.to_string()))
    }
}

/// `def __law_name(x: T, ...)`: whether the law holds for these values
/// (a false hypothesis makes it hold).
fn predicate_def(name: &str, vars: &[(String, E)], hyp: Option<&E>, claim: &E, line: usize) -> Stmt {
    let params = vars.iter().map(|(v, t)| ast::Param {
        is_public: false,
        is_var: false,
        pattern: Pattern::Typed { pattern: Box::new(Pattern::Identifier(v.clone())), type_expr: t.clone() },
        default: None,
    }).collect();
    let mut body = Vec::new();
    if let Some(h) = hyp {
        body.push(stmt(S::If {
            condition: E::UnaryOp { op: ast::UnaryOperator::Not, operand: Box::new(h.clone()) },
            body: vec![stmt(S::Return(Some(E::Boolean(true))), line)],
            elif_branches: vec![],
            else_body: None,
        }, line));
    }
    body.push(stmt(S::Return(Some(claim.clone())), line));
    stmt(S::Def { is_public: false, is_unsafe: false, name: format!("__law_{}", name), params, return_type: None, body }, line)
}

/// Nested loops over the instances; the first counterexample is reported.
fn check_loop(name: &str, vars: &[(String, E)], pools: &[Vec<E>], line: usize) -> Vec<Stmt> {
    let bad = format!("__bad_{}", name);
    let count = format!("__cases_{}", name);
    let args: Vec<E> = vars.iter().map(|(v, _)| E::Identifier(v.clone())).collect();
    // "x = {x}, t = {t}"
    let mut parts = Vec::new();
    for (i, (v, _)) in vars.iter().enumerate() {
        if i > 0 {
            parts.push(ast::FStringPart::Text(", ".into()));
        }
        parts.push(ast::FStringPart::Text(format!("{} = ", v)));
        parts.push(ast::FStringPart::Expression(E::Identifier(v.clone()), None));
    }
    let record = stmt(S::If {
        condition: E::BinaryOp { left: Box::new(E::Identifier(bad.clone())), op: ast::BinaryOperator::Eq, right: Box::new(E::Str(String::new())) },
        body: vec![stmt(S::Assignment { targets: vec![(Pattern::Identifier(bad.clone()), ast::AssignmentOp::Assign)], value: E::FString(parts) }, line)],
        elif_branches: vec![],
        else_body: None,
    }, line);
    let mut inner = vec![
        stmt(S::If {
            condition: E::UnaryOp { op: ast::UnaryOperator::Not, operand: Box::new(call(&format!("__law_{}", name), args)) },
            body: vec![record],
            elif_branches: vec![],
            else_body: None,
        }, line),
        stmt(S::Assignment { targets: vec![(Pattern::Identifier(count.clone()), ast::AssignmentOp::AddAssign)], value: int(1) }, line),
    ];
    for (i, (v, _)) in vars.iter().enumerate().rev() {
        inner = vec![stmt(S::For { pattern: Pattern::Identifier(v.clone()), iterables: vec![E::List(pools[i].clone())], body: inner }, line)];
    }
    if vars.is_empty() {
        inner = vec![stmt(S::If {
            condition: E::UnaryOp { op: ast::UnaryOperator::Not, operand: Box::new(call(&format!("__law_{}", name), vec![])) },
            body: vec![stmt(S::Assignment { targets: vec![(Pattern::Identifier(bad.clone()), ast::AssignmentOp::Assign)], value: E::Str("the closed claim".into()) }, line)],
            elif_branches: vec![],
            else_body: None,
        }, line), stmt(S::Assignment { targets: vec![(Pattern::Identifier(count.clone()), ast::AssignmentOp::AddAssign)], value: int(1) }, line)];
    }
    let ok = E::FString(vec![
        ast::FStringPart::Text(format!("law {}: holds on ", name)),
        ast::FStringPart::Expression(E::Identifier(count.clone()), None),
        ast::FStringPart::Text(" cases".into()),
    ]);
    let fail = E::FString(vec![
        ast::FStringPart::Text(format!("law {}: FAILS for ", name)),
        ast::FStringPart::Expression(E::Identifier(bad.clone()), None),
    ]);
    let mut out = vec![
        stmt(S::Declaration { is_public: false, is_mutable: true, pattern: Pattern::Identifier(bad.clone()), value: E::Str(String::new()) }, line),
        stmt(S::Declaration { is_public: false, is_mutable: true, pattern: Pattern::Identifier(count.clone()), value: int(0) }, line),
    ];
    out.extend(inner);
    out.push(stmt(S::If {
        condition: E::BinaryOp { left: Box::new(E::Identifier(bad.clone())), op: ast::BinaryOperator::Eq, right: Box::new(E::Str(String::new())) },
        body: vec![stmt(S::Expression(call("print", vec![ok])), line)],
        elif_branches: vec![],
        else_body: Some(vec![
            stmt(S::Expression(call("print", vec![fail])), line),
            stmt(S::Assignment { targets: vec![(Pattern::Identifier("__all_hold".into()), ast::AssignmentOp::Assign)], value: E::Boolean(false) }, line),
        ]),
    }, line));
    out
}

/// Sample values of a type, as Fire expressions: small, varied, and for a
/// declared type every constructor down to `depth` levels of nesting.
fn instances(store: &mut TypeStore, core: &Program, t: &Type, depth: usize) -> Option<Vec<E>> {
    match store.shallow(t) {
        Type::Int | Type::Var(_) => Some([0, 1, -1, 2, 5, -7, 42, 1000].iter().map(|i| int(*i)).collect()),
        Type::Float => Some(["0.0", "1.5", "-2.25", "10.0"].iter().map(|s| {
            if let Some(p) = s.strip_prefix('-') {
                E::UnaryOp { op: ast::UnaryOperator::Minus, operand: Box::new(E::Number(NumberLiteral::Decimal(p.into()))) }
            } else {
                E::Number(NumberLiteral::Decimal((*s).into()))
            }
        }).collect()),
        Type::Str => Some(["", "a", "ab", "hello", "Z z"].iter().map(|s| E::Str((*s).into())).collect()),
        Type::Bool => Some(vec![E::Boolean(false), E::Boolean(true)]),
        Type::Unit => Some(vec![E::Nothing]),
        Type::List(e) => {
            let xs = instances(store, core, &e, depth.saturating_sub(1))?;
            let a = xs.first().cloned()?;
            let b = xs.get(1).cloned().unwrap_or(a.clone());
            let c = xs.get(2).cloned().unwrap_or(b.clone());
            Some(vec![E::List(vec![]), E::List(vec![a.clone()]), E::List(vec![b.clone(), a.clone()]), E::List(vec![a, c, b])])
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
                if depth == 0 {
                    continue;
                }
                let mut field_pools = Vec::new();
                for f in &c.fields {
                    let ft = store.substitute(&f.ty, &subst);
                    field_pools.push(instances(store, core, &ft, depth - 1)?);
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
