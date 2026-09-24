// src/check/pattern.rs
// Patterns: match arms (refutable, become Core patterns) and destructuring
// bindings (lets and parameters, become projections).

use super::*;

/// `[k, v]` against a dictionary entry (or any `{key, value}` record).
pub(crate) const ENTRY_NOT_A_LIST: &str = "a dictionary entry is the record {key, value}, not a list: take it apart with `{key, value}`, or `{key: k, value: v}` to rename";

impl Checker {
    /// A match-arm pattern against a subject type. Binders are declared in
    /// the current scope. `maybe_value` says the subject is `T | nothing`
    /// with a `nothing` arm, so a plain name binds the value.
    pub(crate) fn check_pattern(&mut self, p: &ast::Pattern, subject: &Type, maybe_value: bool) -> Pat {
        let line = self.line;
        let st = self.shallow(subject);
        // beside a `nothing` arm, a structured pattern matches the value
        if maybe_value
            && let Type::Data(MAYBE, args) = &st
        {
            let structured = match p {
                ast::Pattern::Object(_) | ast::Pattern::List(_) | ast::Pattern::Ctor(..) => true,
                ast::Pattern::Identifier(name) => self.ctor_names.contains_key(name),
                ast::Pattern::Literal(e) => !matches!(e, ast::Expression::Nothing),
                _ => false,
            };
            if structured {
                let inner = args[0].clone();
                let sub = self.check_pattern(p, &inner, false);
                return Pat::Con(MAYBE, 1, vec![sub]);
            }
        }
        match p {
            ast::Pattern::Identifier(name) => {
                if name == "_" {
                    return Pat::Wild;
                }
                if let Some((tid, ci)) = self.ctor_names.get(name).cloned() {
                    let (t, _) = self.instantiate_type(tid);
                    self.unify(subject, &t, line);
                    let n = self.types[tid].ctors[ci].fields.len();
                    if n > 0 {
                        self.error(line, format!("the constructor {} has {} field(s): write {}({})", name, n, name, vec!["_"; n].join(", ")));
                    }
                    return Pat::Con(tid, ci, vec![]);
                }
                if maybe_value
                    && let Type::Data(MAYBE, args) = &st {
                        let inner = args[0].clone();
                        self.declare(name, Binding::Local { ty: inner, mutable: false });
                        return Pat::Con(MAYBE, 1, vec![Pat::Bind(name.clone())]);
                    }
                self.declare(name, Binding::Local { ty: subject.clone(), mutable: false });
                Pat::Bind(name.clone())
            }
            ast::Pattern::Typed { pattern, type_expr } => {
                // `n: int` on a maybe narrows to the value
                let t = self.annotation(type_expr, line);
                if let Type::Data(MAYBE, args) = &st {
                    let inner = args[0].clone();
                    self.unify(&inner, &t, line);
                    let sub = self.check_pattern(pattern, &inner, false);
                    return Pat::Con(MAYBE, 1, vec![sub]);
                }
                self.unify(subject, &t, line);
                self.check_pattern(pattern, subject, false)
            }
            ast::Pattern::Literal(e) => match e {
                ast::Expression::Nothing => {
                    if let Type::Data(MAYBE, _) = &st {
                        return Pat::Con(MAYBE, 0, vec![]);
                    }
                    self.unify(subject, &Type::Unit, line);
                    Pat::Lit(Lit::Nothing)
                }
                other => {
                    let x = self.check_expr(other, Some(subject));
                    self.unify(subject, &x.ty, line);
                    match x.kind {
                        ExprKind::Lit(l) => Pat::Lit(l),
                        _ => {
                            self.error(line, "a literal pattern must be a number, string, bool or nothing");
                            Pat::Wild
                        }
                    }
                }
            },
            ast::Pattern::Ctor(name, subs) => {
                let (tid, ci) = match self.ctor_names.get(name).cloned() {
                    Some(x) => x,
                    None => {
                        self.error(line, format!("unknown constructor {}", name));
                        return Pat::Wild;
                    }
                };
                let (t, _) = self.instantiate_type(tid);
                self.unify(subject, &t, line);
                let args = match &t {
                    Type::Data(_, a) => a.clone(),
                    _ => vec![],
                };
                let ftys = self.ctor_field_types(tid, ci, &args);
                if ftys.len() != subs.len() {
                    self.error(line, format!("{} has {} field(s), the pattern gives {}", name, ftys.len(), subs.len()));
                    return Pat::Wild;
                }
                let ps = subs.iter().zip(ftys.iter()).map(|(s, ft)| self.check_pattern(s, ft, false)).collect();
                Pat::Con(tid, ci, ps)
            }
            ast::Pattern::List(items) => {
                let elem = self.list_pattern_elem(subject);
                let mut ps = Vec::new();
                let mut rest = None;
                for it in items {
                    match it {
                        ast::Pattern::Rest(r) => {
                            if let Some(n) = r {
                                self.declare(n, Binding::Local { ty: Type::list(elem.clone()), mutable: false });
                            }
                            rest = Some(r.clone());
                        }
                        other => ps.push(self.check_pattern(other, &elem, false)),
                    }
                }
                Pat::List(ps, rest)
            }
            ast::Pattern::Object(entries) => {
                // {ok} / {err} on a result
                if entries.len() == 1 && (entries[0].0 == "ok" || entries[0].0 == "err") {
                    let (e, a) = self.result_parts(subject);
                    let (ci, inner_ty) = if entries[0].0 == "ok" { (1, a) } else { (0, e) };
                    let sub = self.check_pattern(&entries[0].1, &inner_ty, false);
                    return Pat::Con(RESULT, ci, vec![sub]);
                }
                let tid = match &st {
                    Type::Data(tid, _) if !matches!(self.types[*tid].kind, DataKind::Builtin) => *tid,
                    Type::Var(_) => {
                        let names: Vec<String> = entries.iter().map(|(k, _)| k.clone()).collect();
                        let id = self.record_shape(names, line);
                        let (t, _) = self.instantiate_type(id);
                        self.unify(subject, &t, line);
                        id
                    }
                    _ => {
                        let s = self.show_type(subject);
                        self.error(line, format!("a record pattern cannot match a value of type {}", s));
                        return Pat::Wild;
                    }
                };
                let args = match self.shallow(subject) {
                    Type::Data(_, a) => a,
                    _ => vec![],
                };
                let ftys = self.ctor_field_types(tid, 0, &args);
                let nfields = ftys.len();
                let mut subs: Vec<Pat> = (0..nfields).map(|_| Pat::Wild).collect();
                for (key, p) in entries {
                    match self.types[tid].field_index(key) {
                        Some(idx) => {
                            let ft = ftys[idx].clone();
                            subs[idx] = self.check_pattern(p, &ft, false);
                        }
                        None => self.error(line, format!("no field {} in {}", key, self.types[tid].name)),
                    }
                }
                Pat::Con(tid, 0, subs)
            }
            ast::Pattern::Rest(_) => {
                self.error(line, "`...` is only valid inside a list pattern");
                Pat::Wild
            }
            ast::Pattern::FString(_) => {
                self.error(line, "f-string patterns are not supported");
                Pat::Wild
            }
            ast::Pattern::Member { .. } | ast::Pattern::Index { .. } | ast::Pattern::SpreadInto { .. } => {
                self.error(line, "this pattern is only valid as an assignment target");
                Pat::Wild
            }
        }
    }

    /// A destructuring binding: statements that bind every name of the
    /// pattern from the value. A list pattern that can fail aborts.
    pub(crate) fn bind_pattern(&mut self, p: &ast::Pattern, value: Expr, mutable: bool) -> Vec<Stmt> {
        let line = self.line;
        match p {
            ast::Pattern::Identifier(name) => {
                if name == "_" {
                    return vec![Stmt { kind: StmtKind::Expr(value), line }];
                }
                if self.ctor_names.contains_key(name) {
                    self.error(line, format!("{} is a constructor and cannot be bound", name));
                }
                self.declare(name, Binding::Local { ty: value.ty.clone(), mutable });
                vec![Stmt { kind: StmtKind::Let { name: name.clone(), value }, line }]
            }
            ast::Pattern::Typed { pattern, type_expr } => {
                let t = self.annotation(type_expr, line);
                self.unify(&t, &value.ty, line);
                self.bind_pattern(pattern, value, mutable)
            }
            ast::Pattern::List(items) => {
                let tmp = self.temp("d");
                let vt = value.ty.clone();
                let mut out = vec![Stmt { kind: StmtKind::Let { name: tmp.clone(), value }, line }];
                let elem = self.list_pattern_elem(&vt);
                let fixed = items.iter().filter(|i| !matches!(i, ast::Pattern::Rest(_))).count();
                let has_rest = items.iter().any(|i| matches!(i, ast::Pattern::Rest(_)));
                // the list must be long enough: an abort otherwise
                self.effect(Effect::ABORT);
                let tv = self.var(&tmp, vt.clone());
                let n = self.lit(Lit::Int(fixed as i64));
                let check = self.expr(ExprKind::Builtin(if has_rest { "list.need_at_least".into() } else { "list.need_exactly".into() }, vec![tv, n]), Type::Unit);
                out.push(Stmt { kind: StmtKind::Expr(check), line });
                let mut pos = 0i64;
                for it in items {
                    match it {
                        ast::Pattern::Rest(r) => {
                            if let Some(name) = r {
                                let tv = self.var(&tmp, vt.clone());
                                let n = self.lit(Lit::Int(pos));
                                let rest = self.expr(ExprKind::Builtin("list.drop".into(), vec![tv, n]), Type::list(elem.clone()));
                                self.declare(name, Binding::Local { ty: Type::list(elem.clone()), mutable });
                                out.push(Stmt { kind: StmtKind::Let { name: name.clone(), value: rest }, line });
                            }
                        }
                        other => {
                            let tv = self.var(&tmp, vt.clone());
                            let n = self.lit(Lit::Int(pos));
                            let x = self.expr(ExprKind::Builtin("list.at".into(), vec![tv, n]), elem.clone());
                            out.extend(self.bind_pattern(other, x, mutable));
                            pos += 1;
                        }
                    }
                }
                out
            }
            ast::Pattern::Object(entries) => {
                // {ok} = result: unwrap or abort
                if entries.len() == 1 && (entries[0].0 == "ok" || entries[0].0 == "err") {
                    let (e, a) = self.result_parts(&value.ty);
                    self.effect(Effect::ABORT);
                    let (b, t) = if entries[0].0 == "ok" { ("result.unwrap_ok", a) } else { ("result.unwrap_err", e) };
                    let x = self.expr(ExprKind::Builtin(b.into(), vec![value]), t);
                    return self.bind_pattern(&entries[0].1, x, mutable);
                }
                let tmp = self.temp("d");
                let vt = value.ty.clone();
                let mut out = vec![Stmt { kind: StmtKind::Let { name: tmp.clone(), value }, line }];
                for (key, sub) in entries {
                    let tv = self.var(&tmp, vt.clone());
                    let x = self.check_member_of(tv, key);
                    out.extend(self.bind_pattern(sub, x, mutable));
                }
                out
            }
            ast::Pattern::Literal(_) | ast::Pattern::Ctor(..) => {
                self.error(line, "a refutable pattern needs a `match`");
                vec![]
            }
            ast::Pattern::Rest(_) | ast::Pattern::FString(_) => {
                self.error(line, "invalid binding pattern");
                vec![]
            }
            ast::Pattern::Member { .. } | ast::Pattern::Index { .. } | ast::Pattern::SpreadInto { .. } => {
                self.error(line, "this target needs an assignment, not a declaration");
                vec![]
            }
        }
    }

    /// The element type a list pattern binds from a value of type `t`: a
    /// `{key, value}` entry is said not to be a list (the names are bound
    /// anyway).
    fn list_pattern_elem(&mut self, t: &Type) -> Type {
        match self.shallow(t) {
            Type::List(e) => *e,
            Type::Data(PAIR, _) => {
                self.error(self.line, ENTRY_NOT_A_LIST);
                self.fresh()
            }
            _ => {
                let e = self.fresh();
                self.unify(t, &Type::list(e.clone()), self.line);
                e
            }
        }
    }

    /// The error and value types of a result of type `t`.
    fn result_parts(&mut self, t: &Type) -> (Type, Type) {
        match self.shallow(t) {
            Type::Data(RESULT, args) => (args[0].clone(), args[1].clone()),
            _ => {
                let e = self.fresh();
                let a = self.fresh();
                self.unify(t, &Type::result(e.clone(), a.clone()), self.line);
                (e, a)
            }
        }
    }

    /// Destructuring parameters (`{age} => ...`): statements binding their
    /// names from the synthetic parameters.
    pub(crate) fn destructure_params(&mut self, params: &[Param], ast_params: &[ast::Param]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for (p, ast_p) in params.iter().zip(ast_params) {
            if plain_name(&ast_p.pattern).is_none() {
                let v = self.var(&p.name, p.ty.clone());
                out.extend(self.bind_pattern(&ast_p.pattern, v, false));
            }
        }
        out
    }
}
