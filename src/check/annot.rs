// src/check/annot.rs
// Type annotations: the expressions `int`, `[str]`, `{}`, `{name: str}`,
// `Tree`, `int | nothing`, `fn(int) -> str` read as types.

use super::*;

impl Checker {
    /// Read a type annotation. Unknown forms are reported and yield a
    /// fresh variable so checking can go on.
    pub(crate) fn annotation(&mut self, e: &ast::Expression, line: usize) -> Type {
        match e {
            ast::Expression::Identifier(name) => match name.as_str() {
                "int" => Type::Int,
                "float" => Type::Float,
                "str" | "string" => Type::Str,
                "bool" => Type::Bool,
                "nothing" => Type::Unit,
                "list" => Type::list(self.fresh()),
                "dict" => Type::map(self.fresh()),
                "range" => Type::range(),
                "any" => self.fresh(),
                _ => {
                    if let Some(id) = self.type_names.get(name).cloned() {
                        // a class's fields are known once its constructor is checked
                        if let DataKind::Class { ctor, .. } = self.types[id].kind {
                            self.ensure_def(ctor);
                        }
                        let (t, _) = self.instantiate_type(id);
                        return t;
                    }
                    self.error(line, format!("unknown type '{}'", name));
                    self.fresh()
                }
            },
            ast::Expression::Nothing => Type::Unit,
            ast::Expression::List(items) => match items.len() {
                0 => Type::list(self.fresh()),
                1 => {
                    let t = self.annotation(&items[0], line);
                    Type::list(t)
                }
                _ => {
                    self.error(line, "a list type has one element type: [T]");
                    Type::list(self.fresh())
                }
            },
            ast::Expression::Object(entries) => {
                if entries.is_empty() {
                    return Type::map(self.fresh());
                }
                let mut names = Vec::new();
                let mut tys = Vec::new();
                for en in entries {
                    match en {
                        ast::ObjectEntry::KeyValue { key, value } => {
                            names.push(key.clone());
                            tys.push(self.annotation(value, line));
                        }
                        _ => {
                            self.error(line, "a record type lists its fields as name: type");
                        }
                    }
                }
                let id = self.record_shape(names.clone(), line);
                let (t, subst) = self.instantiate_type(id);
                // fields are stored sorted by name, one parameter each
                for (n, ty) in names.iter().zip(tys.iter()) {
                    let idx = self.types[id].field_index(n).unwrap();
                    self.unify(&subst[idx].1, ty, line);
                }
                t
            }
            ast::Expression::BinaryOp { left, op: ast::BinaryOperator::TypeOr, right } => {
                let is_nothing = |e: &ast::Expression| matches!(e, ast::Expression::Nothing) || matches!(e, ast::Expression::Identifier(n) if n == "nothing");
                if is_nothing(right) {
                    let t = self.annotation(left, line);
                    return Type::maybe(t);
                }
                if is_nothing(left) {
                    let t = self.annotation(right, line);
                    return Type::maybe(t);
                }
                self.error(line, "a union type is `T | nothing`; other alternatives need a `type` declaration");
                self.fresh()
            }
            ast::Expression::Call { function, args, .. } => {
                // fn(A, B) -> R is written as a call of `fn`; the arrow is
                // not parsed, so accept `fn(A, B)` and a result annotation
                if let ast::Expression::Identifier(n) = &**function {
                    if n == "fn" {
                        let ps: Vec<Type> = args.iter().map(|a| self.annotation(a, line)).collect();
                        let r = self.fresh();
                        return self.store.fresh_fn(ps, r);
                    }
                    if n == "result" && args.len() == 2 {
                        let e = self.annotation(&args[0], line);
                        let a = self.annotation(&args[1], line);
                        return Type::result(e, a);
                    }
                }
                self.error(line, "unsupported type annotation");
                self.fresh()
            }
            _ => {
                self.error(line, "unsupported type annotation");
                self.fresh()
            }
        }
    }
}
