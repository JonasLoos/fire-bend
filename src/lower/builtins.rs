// src/bend/lower/builtins.rs
// Builtin functions, methods on builtin types, operators, f-strings, and
// derived show/eq/lt defs, mapped onto the prelude.

use super::body::*;
use super::*;

impl<'a> Lower<'a> {
    // -- operators -----------------------------------------------------------

    pub fn lower_binop(&mut self, ctx: &mut FnCtx, op: BinOp, a: Term, b: Term, ty: &Type, line: usize) -> Term {
        let ty = self.store.resolve(ty);
        match op {
            BinOp::Eq | BinOp::Ne => {
                let eq = self.derive_eq(&ty, line);
                let t = Term::Call(eq, vec![a, b]);
                if op == BinOp::Ne { Term::Call("Bool.not".into(), vec![t]) } else { t }
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let f = match (&ty, op) {
                    (Type::Int, BinOp::Lt) => "F.i32.lt",
                    (Type::Int, BinOp::Le) => "F.i32.le",
                    (Type::Int, BinOp::Gt) => "F.i32.gt",
                    (Type::Int, BinOp::Ge) => "F.i32.ge",
                    (Type::Float, BinOp::Lt) => "F32.is_lt",
                    (Type::Float, BinOp::Le) => "F32.is_le",
                    (Type::Float, BinOp::Gt) => "F32.is_gt",
                    (Type::Float, BinOp::Ge) => "F32.is_ge",
                    (Type::Str, BinOp::Lt) => "String.is_lt",
                    (Type::Str, BinOp::Le) => "String.is_le",
                    (Type::Str, BinOp::Gt) => "String.is_gt",
                    (Type::Str, BinOp::Ge) => "String.is_ge",
                    _ => {
                        let lt = self.derive_lt(&ty, line);
                        return match op {
                            BinOp::Lt => Term::Call(lt, vec![a, b]),
                            BinOp::Gt => Term::Call(lt, vec![b, a]),
                            BinOp::Le => Term::Call("Bool.not".into(), vec![Term::Call(lt, vec![b, a])]),
                            _ => Term::Call("Bool.not".into(), vec![Term::Call(lt, vec![a, b])]),
                        };
                    }
                };
                Term::Call(f.into(), vec![a, b])
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod | BinOp::Pow => match &ty {
                Type::Int => match op {
                    BinOp::Add => Term::op(a, "+", b, Ty::U32),
                    BinOp::Sub => Term::op(a, "-", b, Ty::U32),
                    BinOp::Mul => Term::op(a, "*", b, Ty::U32),
                    BinOp::Div => Term::Call("F.i32.div".into(), vec![a, b]),
                    BinOp::Mod => Term::Call("F.i32.mod".into(), vec![a, b]),
                    _ => Term::Call("F.i32.pow".into(), vec![a, b]),
                },
                Type::Float => match op {
                    BinOp::Add => Term::op(a, "+", b, Ty::F32),
                    BinOp::Sub => Term::op(a, "-", b, Ty::F32),
                    BinOp::Mul => Term::op(a, "*", b, Ty::F32),
                    BinOp::Div => Term::op(a, "/", b, Ty::F32),
                    BinOp::Mod => Term::op(a, "%", b, Ty::F32),
                    _ => Term::Call("F32.pow".into(), vec![a, b]),
                },
                Type::Str if op == BinOp::Add => Term::cat(a, b),
                Type::List(e) if op == BinOp::Add => {
                    let ebt = self.ty(e, &[], line);
                    Term::Call("F.list.append".into(), vec![Term::TyArg(ebt), a, b])
                }
                other => {
                    let _ = ctx;
                    self.error(line, format!("operator {:?} on {:?}", op, other));
                    a
                }
            },
        }
    }

    // -- derived functions ---------------------------------------------------

    fn type_key(t: &Ty) -> String {
        Self::mangle(&t.render())
    }

    /// `F.show.<type>(x) -> String`, Fire's repr format (strings quoted).
    pub fn derive_show(&mut self, t: &Type, repr: bool, line: usize) -> String {
        let t = self.store.resolve(t);
        match &t {
            Type::Int => return "F.i32.show.t".into(),
            Type::Float => return "F.f32.show.t".into(),
            Type::Str => return if repr { "F.str.repr".into() } else { "F.str.id".into() },
            Type::Bool => return "F.bool.show".into(),
            Type::Unit => return "F.unit.show".into(),
            Type::Range => return "F.range.show".into(),
            _ => {}
        }
        let bt = self.ty(&t, &[], line);
        let name = format!("f.show.{}", Self::type_key(&bt));
        if self.derived.contains(&name) {
            return name;
        }
        self.derived.insert(name.clone());
        let body = match &t {
            Type::List(e) => {
                let f = self.derive_show(e, true, line);
                let ebt = self.ty(e, &[], line);
                Body::term(Term::Call("F.list.show".into(), vec![Term::TmplTy(ebt), Term::TmplRef(f), Term::var("__x")]))
            }
            Type::Maybe(e) => {
                let f = self.derive_show(e, repr, line);
                let ebt = self.ty(e, &[], line);
                Body::term(Term::Call("F.maybe.show".into(), vec![Term::TmplTy(ebt), Term::TmplRef(f), Term::var("__x")]))
            }
            Type::Result(e, a) => {
                let fe = self.derive_show(e, true, line);
                let fa = self.derive_show(a, true, line);
                let ebt = self.ty(e, &[], line);
                let abt = self.ty(a, &[], line);
                Body::term(Term::Call("F.result.show".into(), vec![Term::TmplTy(ebt), Term::TmplTy(abt), Term::TmplRef(fe), Term::TmplRef(fa), Term::var("__x")]))
            }
            Type::Map(v) => {
                let f = self.derive_show(v, true, line);
                let vbt = self.ty(v, &[], line);
                Body::term(Term::Call("F.map.show".into(), vec![Term::TmplTy(vbt), Term::TmplRef(f), Term::var("__x")]))
            }
            Type::Record(rec, args) => {
                let rec = *rec;
                self.ensure_record_type(rec);
                let rdef = &self.tp.records[rec];
                let is_class = matches!(rdef.kind, RecordKind::Class { .. });
                let prefix = if is_class && rec != crate::sigs::PAIR_REC { rdef.name.clone() } else { String::new() };
                let n = rdef.fields.len();
                let fields: Vec<(String, bool, String)> = rdef.fields.iter().map(|f| (f.name.clone(), f.public, Self::mangle(&f.name))).collect();
                let args = args.clone();
                // a dictionary entry prints as the interpreter's `[key, value]`
                let is_pair = rec == crate::sigs::PAIR_REC;
                let parent_idx = self.tp.records[rec].parent_field();
                let mut parts: Vec<Term> = vec![Term::Str(if is_pair { "[".into() } else { format!("{}{{", prefix) })];
                let mut first = true;
                let order = self.tp.records[rec].show_order();
                for i in order {
                    let (fname, public, mname) = &fields[i];
                    // the parent's public members, flattened where the spread is
                    if Some(i) == parent_idx {
                        let pt = self.store.resolve(&args[i]);
                        if let Type::Record(_, _) = pt {
                            let f = self.derive_show_fields(&pt, line);
                            let inner = Term::Call(f, vec![Term::var(mname)]);
                            let sep = Term::Str(if first { String::new() } else { ", ".into() });
                            // the parent may show nothing; a separator only when it does
                            parts.push(Term::Call("F.str.join_nonempty".into(), vec![sep, inner]));
                            first = false;
                        }
                        continue;
                    }
                    if !public || fname == "__parent" {
                        continue;
                    }
                    let ft = self.store.resolve(&args[i]);
                    let shown = match ft {
                        Type::Fn(_, _, _) => Term::Str("<fn>".into()),
                        _ => {
                            let f = self.derive_show(&ft, true, line);
                            Term::Call(f, vec![Term::var(mname)])
                        }
                    };
                    let label = if is_pair {
                        if first { String::new() } else { ", ".into() }
                    } else if first {
                        format!("{}: ", fname)
                    } else {
                        format!(", {}: ", fname)
                    };
                    first = false;
                    if !label.is_empty() {
                        parts.push(Term::Str(label));
                    }
                    parts.push(shown);
                }
                parts.push(Term::Str(if is_pair { "]".into() } else { "}".into() }));
                let mut acc = parts.remove(0);
                for p in parts {
                    acc = Term::cat(acc, p);
                }
                let pat_fields: Vec<(String, bool)> = fields.iter().map(|(_, _, m)| (m.clone(), false)).collect();
                let _ = n;
                Body::Match { scrutinee: "__x".into(), arms: vec![(Pat::Ctor(self.record_ctor_name(rec), pat_fields), Body::term(acc))] }
            }
            Type::Fn(_, _, _) => Body::term(Term::Str("<fn>".into())),
            Type::Stream(_) | Type::Var(_) => Body::term(Term::Str("<stream>".into())),
            _ => unreachable!(),
        };
        let mut def = Def { name: name.clone(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params: vec![Param { name: "__x".into(), reusable: false, ty: bt }], ret: Ty::Str, body };
        self.fix_quantities(&mut def);
        self.emitted_defs.insert(name.clone());
        self.defs.push(def);
        name
    }

    /// `f.showf.<key>(x) -> String`: a record's public members without the
    /// `Name{...}` wrapper, for flattening into a child's display.
    pub fn derive_show_fields(&mut self, t: &Type, line: usize) -> String {
        let t = self.store.resolve(t);
        let bt = self.ty(&t, &[], line);
        let name = format!("f.showf.{}", Self::type_key(&bt));
        if self.derived.contains(&name) {
            return name;
        }
        self.derived.insert(name.clone());
        let full = self.derive_show(&t, true, line);
        let rec_name = match &t {
            Type::Record(rec, _) => self.tp.records[*rec].name.clone(),
            _ => String::new(),
        };
        // strip the `Name{` prefix and the closing brace
        let body = Body::term(Term::Call("F.str.strip_wrapper".into(), vec![Term::Str(format!("{}{{", rec_name)), Term::Call(full, vec![Term::var("__x")])]));
        let mut def = Def { name: name.clone(), is_unsafe: false, tmpl_types: vec![], tmpl_funcs: vec![], erased: vec![], params: vec![Param { name: "__x".into(), reusable: false, ty: bt }], ret: Ty::Str, body };
        self.fix_quantities(&mut def);
        self.emitted_defs.insert(name.clone());
        self.defs.push(def);
        name
    }

    /// `F.eq.<type>(a, b) -> Bool`: structural equality over public data.
    pub fn derive_eq(&mut self, t: &Type, line: usize) -> String {
        let t = self.store.resolve(t);
        match &t {
            Type::Int => return "U32.is_eq".into(),
            Type::Float => return "F32.is_eq".into(),
            Type::Str => return "String.eq".into(),
            Type::Bool => return "F.bool.eq".into(),
            Type::Unit => return "F.unit.eq".into(),
            Type::Range => return "F.range.eq".into(),
            _ => {}
        }
        let bt = self.ty(&t, &[], line);
        let name = format!("f.eq.{}", Self::type_key(&bt));
        if self.derived.contains(&name) {
            return name;
        }
        self.derived.insert(name.clone());
        let body = match &t {
            Type::List(e) => {
                let f = self.derive_eq(e, line);
                let ebt = self.ty(e, &[], line);
                Body::term(Term::Call("F.list.eq".into(), vec![Term::TmplTy(ebt), Term::TmplRef(f), Term::var("a"), Term::var("b")]))
            }
            Type::Maybe(e) => {
                let f = self.derive_eq(e, line);
                let ebt = self.ty(e, &[], line);
                Body::term(Term::Call("F.maybe.eq".into(), vec![Term::TmplTy(ebt), Term::TmplRef(f), Term::var("a"), Term::var("b")]))
            }
            Type::Result(e, a) => {
                let fe = self.derive_eq(e, line);
                let fa = self.derive_eq(a, line);
                let ebt = self.ty(e, &[], line);
                let abt = self.ty(a, &[], line);
                Body::term(Term::Call("F.result.eq".into(), vec![Term::TmplTy(ebt), Term::TmplTy(abt), Term::TmplRef(fe), Term::TmplRef(fa), Term::var("a"), Term::var("b")]))
            }
            Type::Map(v) => {
                let f = self.derive_eq(v, line);
                let vbt = self.ty(v, &[], line);
                Body::term(Term::Call("F.map.eq".into(), vec![Term::TmplTy(vbt), Term::TmplRef(f), Term::var("a"), Term::var("b")]))
            }
            Type::Record(rec, args) => {
                let rec = *rec;
                self.ensure_record_type(rec);
                let fields: Vec<(String, bool)> = self.tp.records[rec].fields.iter().map(|f| (f.name.clone(), f.public)).collect();
                let args = args.clone();
                let mut acc: Option<Term> = None;
                let parent_idx = self.tp.records[rec].parent_field();
                for (i, (fname, public)) in fields.iter().enumerate() {
                    // inherited members compare through the parent object
                    if (!public || fname == "__parent") && parent_idx != Some(i) {
                        continue;
                    }
                    let ft = self.store.resolve(&args[i]);
                    if let Type::Fn(_, _, _) = ft {
                        continue;
                    }
                    let f = self.derive_eq(&ft, line);
                    let m = Self::mangle(fname);
                    let cmp = Term::Call(f, vec![Term::Var(format!("a_{}", m)), Term::Var(format!("b_{}", m))]);
                    acc = Some(match acc {
                        None => cmp,
                        Some(prev) => Term::And(Box::new(prev), Box::new(cmp)),
                    });
                }
                let a_pat: Vec<(String, bool)> = fields.iter().map(|(f, _)| (format!("a_{}", Self::mangle(f)), false)).collect();
                let b_pat: Vec<(String, bool)> = fields.iter().map(|(f, _)| (format!("b_{}", Self::mangle(f)), false)).collect();
                let inner = Body::term(acc.unwrap_or_else(|| Term::boolean(true)));
                Body::Match {
                    scrutinee: "a".into(),
                    arms: vec![(Pat::Ctor(self.record_ctor_name(rec), a_pat), Body::Match { scrutinee: "b".into(), arms: vec![(Pat::Ctor(self.record_ctor_name(rec), b_pat), inner)] })],
                }
            }
            Type::Fn(_, _, _) => Body::term(Term::boolean(false)),
            _ => Body::term(Term::boolean(false)),
        };
        let mut def = Def {
            name: name.clone(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: vec![Param { name: "a".into(), reusable: false, ty: bt.clone() }, Param { name: "b".into(), reusable: false, ty: bt }],
            ret: Ty::Bool,
            body,
        };
        self.fix_quantities(&mut def);
        self.emitted_defs.insert(name.clone());
        self.defs.push(def);
        name
    }

    /// `F.lt.<type>(a, b) -> Bool`: ordering (numbers, strings, lists
    /// lexicographically, records by public data fields in order).
    pub fn derive_lt(&mut self, t: &Type, line: usize) -> String {
        let t = self.store.resolve(t);
        match &t {
            Type::Int => return "F.i32.lt".into(),
            Type::Float => return "F32.is_lt".into(),
            Type::Str => return "String.is_lt".into(),
            Type::Bool => return "F.bool.lt".into(),
            _ => {}
        }
        let bt = self.ty(&t, &[], line);
        let name = format!("f.lt.{}", Self::type_key(&bt));
        if self.derived.contains(&name) {
            return name;
        }
        self.derived.insert(name.clone());
        let body = match &t {
            Type::List(e) => {
                let lt = self.derive_lt(e, line);
                let eq = self.derive_eq(e, line);
                let ebt = self.ty(e, &[], line);
                Body::term(Term::Call("F.list.lt".into(), vec![Term::TmplTy(ebt), Term::TmplRef(lt), Term::TmplRef(eq), Term::var("a"), Term::var("b")]))
            }
            Type::Record(rec, args) => {
                let rec = *rec;
                self.ensure_record_type(rec);
                let fields: Vec<(String, bool)> = self.tp.records[rec].fields.iter().map(|f| (f.name.clone(), f.public)).collect();
                let args = args.clone();
                // lexicographic: lt(f1) or (eq(f1) and lt(f2)) ...
                let mut terms: Vec<(Term, Term)> = Vec::new();
                for (i, (fname, public)) in fields.iter().enumerate() {
                    if !public || fname == "__parent" {
                        continue;
                    }
                    let ft = self.store.resolve(&args[i]);
                    if let Type::Fn(_, _, _) = ft {
                        continue;
                    }
                    let lt = self.derive_lt(&ft, line);
                    let eq = self.derive_eq(&ft, line);
                    let m = Self::mangle(fname);
                    terms.push((Term::Call(lt, vec![Term::Var(format!("a_{}", m)), Term::Var(format!("b_{}", m))]), Term::Call(eq, vec![Term::Var(format!("a_{}", m)), Term::Var(format!("b_{}", m))])));
                }
                let mut acc = Term::boolean(false);
                for (lt, eq) in terms.into_iter().rev() {
                    acc = Term::Or(Box::new(lt), Box::new(Term::And(Box::new(eq), Box::new(acc))));
                }
                let a_pat: Vec<(String, bool)> = fields.iter().map(|(f, _)| (format!("a_{}", Self::mangle(f)), false)).collect();
                let b_pat: Vec<(String, bool)> = fields.iter().map(|(f, _)| (format!("b_{}", Self::mangle(f)), false)).collect();
                Body::Match {
                    scrutinee: "a".into(),
                    arms: vec![(Pat::Ctor(self.record_ctor_name(rec), a_pat), Body::Match { scrutinee: "b".into(), arms: vec![(Pat::Ctor(self.record_ctor_name(rec), b_pat), Body::term(acc))] })],
                }
            }
            other => {
                self.error(line, format!("values of type {:?} cannot be ordered", other));
                Body::term(Term::boolean(false))
            }
        };
        let mut def = Def {
            name: name.clone(),
            is_unsafe: false,
            tmpl_types: vec![],
            tmpl_funcs: vec![],
            erased: vec![],
            params: vec![Param { name: "a".into(), reusable: false, ty: bt.clone() }, Param { name: "b".into(), reusable: false, ty: bt }],
            ret: Ty::Bool,
            body,
        };
        self.fix_quantities(&mut def);
        self.emitted_defs.insert(name.clone());
        self.defs.push(def);
        name
    }

    // -- f-strings -----------------------------------------------------------

    pub fn lower_fstring(&mut self, ctx: &mut FnCtx, parts: &[FPart], line: usize) -> Term {
        let mut acc: Option<Term> = None;
        for p in parts {
            let t = match p {
                FPart::Text(s) => Term::Str(s.clone()),
                FPart::Expr(e, spec) => {
                    let et = self.rty(ctx, &e.ty);
                    let v = self.lower_expr(ctx, e);
                    let shown = match (&et, spec.as_deref()) {
                        (Type::Float, Some(sp)) if sp.contains('f') => {
                            let digits = sp.split('.').nth(1).and_then(|d| d.trim_end_matches('f').parse::<u32>().ok()).unwrap_or(6);
                            Term::Call("F.f32.show_fixed".into(), vec![v, Term::U32(digits)])
                        }
                        _ => {
                            let f = self.derive_show(&et, false, line);
                            Term::Call(f, vec![v])
                        }
                    };
                    match spec.as_deref() {
                        Some(sp) => self.apply_width(shown, sp, &et),
                        None => shown,
                    }
                }
            };
            acc = Some(match acc {
                None => t,
                Some(prev) => Term::cat(prev, t),
            });
        }
        acc.unwrap_or_else(|| Term::Str(String::new()))
    }

    /// Width / alignment of a format spec.
    fn apply_width(&mut self, shown: Term, spec: &str, ty: &Type) -> Term {
        // [[fill]align][sign][0][width][.precision][type]
        let chars: Vec<char> = spec.chars().collect();
        let mut i = 0;
        let mut fill = ' ';
        let mut align: Option<char> = None;
        if chars.len() >= 2 && matches!(chars[1], '<' | '>' | '^') {
            fill = chars[0];
            align = Some(chars[1]);
            i = 2;
        } else if !chars.is_empty() && matches!(chars[0], '<' | '>' | '^') {
            align = Some(chars[0]);
            i = 1;
        }
        if i < chars.len() && matches!(chars[i], '+' | ' ') {
            i += 1;
        }
        if i < chars.len() && chars[i] == '0' {
            fill = '0';
            i += 1;
        }
        let mut width = 0usize;
        while i < chars.len() && chars[i].is_ascii_digit() {
            width = width * 10 + chars[i].to_digit(10).unwrap() as usize;
            i += 1;
        }
        if width == 0 {
            return shown;
        }
        let default_align = if matches!(ty, Type::Int | Type::Float) { '>' } else { '<' };
        let align = align.unwrap_or(default_align);
        let f = match align {
            '<' => "F.fmt.pad_right",
            '^' => "F.fmt.pad_center",
            _ => "F.fmt.pad_left",
        };
        Term::Call(f.into(), vec![shown, Term::U32(width as u32), Term::Chr(fill)])
    }

    // -- globals -------------------------------------------------------------

    pub fn lower_builtin(&mut self, ctx: &mut FnCtx, name: &str, args: &[TExpr], ret: &Type, line: usize) -> Term {
        let arg_tys: Vec<Type> = args.iter().map(|a| self.rty(ctx, &a.ty)).collect();
        let first = arg_tys.first().cloned().unwrap_or(Type::Unit);
        match name {
            "print" | "debug" => {
                // print returns its argument: bind it first so it can be returned
                if args.len() == 1 {
                    let v = self.lower_expr(ctx, &args[0]);
                    let bt = self.ty(&first, &[], line);
                    let tmp = self.temp(ctx, v, bt.clone(), false);
                    let f = self.derive_show(&first, name == "debug", line);
                    let call = Term::Call("IO.print".into(), vec![Term::Call(f, vec![tmp.clone()])]);
                    ctx.seg.push(Stmt::Step(call));
                    return tmp;
                }
                let mut shown: Vec<Term> = Vec::new();
                for (a, t) in args.iter().zip(arg_tys.iter()) {
                    let v = self.lower_expr(ctx, a);
                    let f = self.derive_show(t, name == "debug", line);
                    shown.push(Term::Call(f, vec![v]));
                }
                let text = if shown.is_empty() {
                    Term::Str(String::new())
                } else {
                    let mut acc = shown[0].clone();
                    for s in &shown[1..] {
                        acc = Term::cat(Term::cat(acc, Term::Str(" ".into())), s.clone());
                    }
                    acc
                };
                let call = Term::Call("IO.print".into(), vec![text]);
                ctx.seg.push(Stmt::Step(call));
                Term::unit()
            }
            "len" => {
                let v = self.lower_expr(ctx, &args[0]);
                match first {
                    Type::Str => Term::Call("F.str.len".into(), vec![v]),
                    Type::Range => Term::Call("F.range.len".into(), vec![v]),
                    Type::Map(vt) => {
                        let vbt = self.ty(&vt, &[], line);
                        Term::Call("F.map.size".into(), vec![Term::TyArg(vbt), v])
                    }
                    Type::List(e) => {
                        let ebt = self.ty(&e, &[], line);
                        Term::Call("F.list.len".into(), vec![Term::TyArg(ebt), v])
                    }
                    _ => Term::U32(0),
                }
            }
            "sum" | "min" | "max" => {
                if args.len() == 1 {
                    let v = self.lower_expr(ctx, &args[0]);
                    let elem = match &first {
                        Type::List(e) => (**e).clone(),
                        Type::Range => Type::Int,
                        _ => Type::Int,
                    };
                    let v = if let Type::Range = first { Term::Call("F.range.list".into(), vec![v]) } else { v };
                    let f = match (name, &elem) {
                        ("sum", Type::Float) => "F.list.sum_f32".to_string(),
                        ("sum", _) => "F.list.sum_u32".to_string(),
                        ("min", Type::Float) => "F.list.min_f32".to_string(),
                        ("min", _) => "F.list.min_i32".to_string(),
                        ("max", Type::Float) => "F.list.max_f32".to_string(),
                        _ => "F.list.max_i32".to_string(),
                    };
                    if name == "sum" {
                        return Term::Call(f, vec![v]);
                    }
                    let rt = self.ty(&elem, &[], line);
                    let call = Term::Call(f, vec![v]);
                    return self.adapt_call(ctx, call, Mode::Result, rt, line);
                }
                let a = self.lower_expr(ctx, &args[0]);
                let b = self.lower_expr(ctx, &args[1]);
                let f = match (name, &first) {
                    ("min", Type::Float) => "F32.min",
                    ("min", _) => "F.i32.min",
                    ("max", Type::Float) => "F32.max",
                    _ => "F.i32.max",
                };
                Term::Call(f.into(), vec![a, b])
            }
            "abs" => {
                let v = self.lower_expr(ctx, &args[0]);
                match first {
                    Type::Float => Term::Call("F32.abs".into(), vec![v]),
                    _ => Term::Call("F.i32.abs".into(), vec![v]),
                }
            }
            "round" => {
                let v = self.lower_expr(ctx, &args[0]);
                match first {
                    Type::Float => {
                        if args.len() == 1 {
                            Term::Call("F.f32.round_to_int".into(), vec![v])
                        } else {
                            let d = self.lower_expr(ctx, &args[1]);
                            Term::Call("F.f32.round_digits".into(), vec![v, d])
                        }
                    }
                    _ => v,
                }
            }
            "str" => {
                let v = self.lower_expr(ctx, &args[0]);
                let f = self.derive_show(&first, false, line);
                Term::Call(f, vec![v])
            }
            "int" => {
                let v = self.lower_expr(ctx, &args[0]);
                match first {
                    Type::Float => Term::Call("F.f32.to_i32".into(), vec![v]),
                    Type::Str => {
                        let call = Term::Call("F.i32.parse_or_abort".into(), vec![v]);
                        self.adapt_call(ctx, call, Mode::Result, Ty::U32, line)
                    }
                    Type::Bool => Term::Call("Bool.to_u32".into(), vec![v]),
                    _ => v,
                }
            }
            "float" => {
                let v = self.lower_expr(ctx, &args[0]);
                match first {
                    Type::Int => Term::Call("F.i32.to_f32".into(), vec![v]),
                    Type::Str => {
                        let call = Term::Call("F.f32.parse_or_abort".into(), vec![v]);
                        self.adapt_call(ctx, call, Mode::Result, Ty::F32, line)
                    }
                    _ => v,
                }
            }
            "bool" => self.lower_cond(ctx, &args[0]),
            "sorted" | "reversed" => {
                let v = self.lower_expr(ctx, &args[0]);
                let (v, elem) = match &first {
                    Type::Range => (Term::Call("F.range.list".into(), vec![v]), Type::Int),
                    Type::List(e) => (v, (**e).clone()),
                    _ => (v, Type::Int),
                };
                let ebt = self.ty(&elem, &[], line);
                if name == "reversed" {
                    return Term::Call("F.list.reverse".into(), vec![Term::TyArg(ebt), v]);
                }
                if args.len() == 2 {
                    return self.sort_by_key(ctx, v, &elem, &args[1], line);
                }
                let lt = self.derive_lt(&elem, line);
                Term::Call("F.list.sort".into(), vec![Term::TmplTy(ebt), Term::TmplRef(lt), v])
            }
            "range" => {
                let (a, b) = if args.len() == 1 {
                    (Term::U32(0), self.lower_expr(ctx, &args[0]))
                } else {
                    let a = self.lower_expr(ctx, &args[0]);
                    let b = self.lower_expr(ctx, &args[1]);
                    (a, b)
                };
                Term::ctor("F.Range.mk", vec![a, b])
            }
            "error" => {
                let m = self.lower_expr(ctx, &args[0]);
                let rt = self.bty(ctx, ret, line);
                self.abort_term(ctx, m, rt, line)
            }
            "assert" => {
                let c = self.lower_cond(ctx, &args[0]);
                let msg = if args.len() > 1 { self.lower_expr(ctx, &args[1]) } else { Term::Str("assertion failed".into()) };
                let call = Term::Call("F.assert".into(), vec![c, msg]);
                self.adapt_call(ctx, call, Mode::Result, Ty::Unit, line)
            }
            "index" if matches!(first, Type::Stream(_)) => {
                // stream[i]: drop i then first
                let dropped = TExpr { kind: TExprKind::MethodCall { recv: Box::new(args[0].clone()), name: "drop".into(), args: vec![args[1].clone()] }, ty: first.clone(), line };
                self.lower_stream_method(ctx, &dropped, "first", &[], ret, line)
            }
            "index" => {
                if let (Type::Record(crate::sigs::PAIR_REC, _), TExprKind::Lit(Lit::Int(i @ (0 | 1)))) = (&first, &args[1].kind) {
                    let get = TExpr { kind: TExprKind::Field(Box::new(args[0].clone()), crate::sigs::PAIR_REC, *i as usize), ty: ret.clone(), line };
                    return self.lower_expr(ctx, &get);
                }
                let recv = self.lower_expr(ctx, &args[0]);
                let idx = self.lower_expr(ctx, &args[1]);
                match &first {
                    Type::Str => {
                        let call = Term::Call("F.str.index".into(), vec![recv, idx]);
                        self.adapt_call(ctx, call, Mode::Result, Ty::Str, line)
                    }
                    Type::List(e) => {
                        let ebt = self.ty(e, &[], line);
                        let call = Term::Call("F.list.index".into(), vec![Term::TyArg(ebt.clone()), recv, idx]);
                        self.adapt_call(ctx, call, Mode::Result, ebt, line)
                    }
                    Type::Range => Term::Call("F.range.index".into(), vec![recv, idx]),
                    Type::Map(v) => {
                        let vbt = self.ty(v, &[], line);
                        Term::Call("F.map.lookup".into(), vec![Term::TyArg(vbt), recv, idx])
                    }
                    _ => Term::unit(),
                }
            }
            "slice" if matches!(first, Type::Stream(_)) => {
                // stream[..n] / stream[a..b]: take after an optional drop
                match &args[1].kind {
                    TExprKind::Range { start, end: Some(end) } => {
                        let dropped = TExpr { kind: TExprKind::MethodCall { recv: Box::new(args[0].clone()), name: "drop".into(), args: vec![(**start).clone()] }, ty: first.clone(), line };
                        let count = TExpr { kind: TExprKind::BinOp(BinOp::Sub, end.clone(), start.clone()), ty: Type::Int, line };
                        let elem_tt = match &first {
                            Type::Stream(e) => (**e).clone(),
                            _ => Type::Int,
                        };
                        self.stream_take(ctx, &dropped, &count, &elem_tt, line)
                    }
                    _ => {
                        self.error(line, "an open slice of a stream is itself a stream; consume it with .take(n)");
                        Term::unit()
                    }
                }
            }
            "slice" => {
                let recv = self.lower_expr(ctx, &args[0]);
                let (a, b, open) = match &args[1].kind {
                    TExprKind::Range { start, end } => {
                        let a = self.lower_expr(ctx, start);
                        match end {
                            Some(e) => (a, self.lower_expr(ctx, e), false),
                            None => (a, Term::U32(0), true),
                        }
                    }
                    _ => (Term::U32(0), Term::U32(0), true),
                };
                match &first {
                    Type::Str => Term::Call(if open { "F.str.slice_from" } else { "F.str.slice" }.into(), if open { vec![recv, a] } else { vec![recv, a, b] }),
                    Type::List(e) => {
                        let ebt = self.ty(e, &[], line);
                        Term::Call(if open { "F.list.slice_from" } else { "F.list.slice" }.into(), if open { vec![Term::TyArg(ebt), recv, a] } else { vec![Term::TyArg(ebt), recv, a, b] })
                    }
                    Type::Range => Term::Call(if open { "F.range.slice_from" } else { "F.range.slice" }.into(), if open { vec![recv, a] } else { vec![recv, a, b] }),
                    _ => Term::unit(),
                }
            }
            "unwrap_ok" | "unwrap_err" => {
                let v = self.lower_expr(ctx, &args[0]);
                let (e, a) = match &first {
                    Type::Result(e, a) => (self.ty(e, &[], line), self.ty(a, &[], line)),
                    _ => (Ty::Str, Ty::Unit),
                };
                let f = if name == "unwrap_ok" { "F.result.unwrap_ok" } else { "F.result.unwrap_err" };
                let rt = if name == "unwrap_ok" { a.clone() } else { e.clone() };
                let call = Term::Call(f.into(), vec![Term::TyArg(e), Term::TyArg(a), v]);
                self.adapt_call(ctx, call, Mode::Result, rt, line)
            }
            "is_nothing" | "is_something" => {
                let v = self.lower_expr(ctx, &args[0]);
                let ibt = match &first {
                    Type::Maybe(i) => self.ty(i, &[], line),
                    _ => Ty::Unit,
                };
                let f = if name == "is_nothing" { "Maybe.is_none" } else { "Maybe.is_some" };
                Term::Call(f.into(), vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(ibt), v])
            }
            "or_dyn" => {
                // decided by the (now known) type of the left side
                if let Type::Maybe(_) = &first {
                    return self.lower_builtin(ctx, "maybe_or", args, ret, line);
                }
                let e = TExpr { kind: TExprKind::Or(Box::new(args[0].clone()), Box::new(args[1].clone())), ty: ret.clone(), line };
                self.lower_expr(ctx, &e)
            }
            "index_cur" => {
                let name = if matches!(first, Type::Map(_)) { "map_get_or" } else { "index" };
                self.lower_builtin(ctx, name, args, ret, line)
            }
            "index_set" => {
                let name = if matches!(first, Type::Map(_)) { "map_set" } else { "list_set" };
                self.lower_builtin(ctx, name, args, ret, line)
            }
            "maybe_or" => {
                let m = self.lower_expr(ctx, &args[0]);
                let d = self.lower_expr(ctx, &args[1]);
                let ibt = match &first {
                    Type::Maybe(i) => self.ty(i, &[], line),
                    _ => Ty::Unit,
                };
                Term::Call("Maybe.default".into(), vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(ibt), m, d])
            }
            "map_get_or" => {
                let m = self.lower_expr(ctx, &args[0]);
                let k = self.lower_expr(ctx, &args[1]);
                let vbt = match &first {
                    Type::Map(v) => self.ty(v, &[], line),
                    _ => Ty::Unit,
                };
                let call = Term::Call("F.map.get_or_abort".into(), vec![Term::TyArg(vbt.clone()), m, k]);
                self.adapt_call(ctx, call, Mode::Result, vbt, line)
            }
            "map_set" => {
                let m = self.lower_expr(ctx, &args[0]);
                let k = self.lower_expr(ctx, &args[1]);
                let v = self.lower_expr(ctx, &args[2]);
                let vbt = match &first {
                    Type::Map(v) => self.ty(v, &[], line),
                    _ => Ty::Unit,
                };
                Term::Call("Map.set".into(), vec![Term::TyArg(Ty::Param("&2".into())), Term::TyArg(vbt), m, k, v])
            }
            "list_set" => {
                let xs = self.lower_expr(ctx, &args[0]);
                let i = self.lower_expr(ctx, &args[1]);
                let v = self.lower_expr(ctx, &args[2]);
                let ebt = match &first {
                    Type::List(e) => self.ty(e, &[], line),
                    _ => Ty::Unit,
                };
                let call = Term::Call("F.list.set".into(), vec![Term::TyArg(ebt.clone()), xs, i, v]);
                self.adapt_call(ctx, call, Mode::Result, Ty::list(ebt), line)
            }
            "list_concat" => {
                let parts: Vec<Term> = args.iter().map(|a| self.lower_expr(ctx, a)).collect();
                let ebt = match &first {
                    Type::List(e) => self.ty(e, &[], line),
                    _ => Ty::Unit,
                };
                let mut acc = parts[0].clone();
                for p in &parts[1..] {
                    acc = Term::Call("F.list.append".into(), vec![Term::TyArg(ebt.clone()), acc, p.clone()]);
                }
                acc
            }
            "list_reverse" => {
                let xs = self.lower_expr(ctx, &args[0]);
                let ebt = match &first {
                    Type::List(e) => self.ty(e, &[], line),
                    _ => Ty::Unit,
                };
                Term::Call("F.list.reverse".into(), vec![Term::TyArg(ebt), xs])
            }
            "cons" => {
                let h = self.lower_expr(ctx, &args[0]);
                let t = self.lower_expr(ctx, &args[1]);
                Term::Cons(Box::new(h), Box::new(t))
            }
            "__iter_head" | "__iter_tail" | "__iter_done" => {
                let xs = self.lower_expr(ctx, &args[0]);
                let ebt = match &first {
                    Type::List(e) => self.ty(e, &[], line),
                    _ => Ty::Unit,
                };
                let f = match name {
                    "__iter_head" => "F.list.head_unsafe",
                    "__iter_tail" => "F.list.tail",
                    _ => "F.list.is_empty",
                };
                Term::Call(f.into(), vec![Term::TyArg(ebt), xs])
            }
            other if other.contains('.') => self.lower_module_call(ctx, other, args, &arg_tys, ret, line),
            other => {
                self.error(line, format!("unsupported builtin {}", other));
                Term::unit()
            }
        }
    }

    fn sort_by_key(&mut self, ctx: &mut FnCtx, list: Term, elem: &Type, key: &TExpr, line: usize) -> Term {
        let (code, env, env_ty, fmode) = match self.stage_parts(ctx, key, line) {
            Some(p) => p,
            None => return list,
        };
        let key_ty = match self.store.resolve(&key.ty) {
            Type::Fn(_, r, _) => self.store.resolve(&r),
            _ => Type::Int,
        };
        let lt = self.derive_lt(&key_ty, line);
        let ebt = self.ty(elem, &[], line);
        let kbt = self.ty(&key_ty, &[], line);
        if fmode != Mode::Pure {
            // a key that can fail or print: compute the keys first (in this
            // function's mode), then sort the (key, element) pairs purely
            let list_tt = Type::list(elem.clone());
            let xs = self.temp(ctx, list, Ty::list(ebt.clone()), false);
            let xs_name = match &xs {
                Term::Var(n) => n.clone(),
                _ => unreachable!(),
            };
            ctx.locals.insert(xs_name.clone(), Local { ty: Ty::list(ebt.clone()), tt: list_tt.clone() });
            let xs_expr = TExpr { kind: TExprKind::Local(xs_name), ty: list_tt, line };
            let stage = TExpr { kind: TExprKind::Stage { op: StageOp::Map, input: Box::new(xs_expr), func: Box::new(key.clone()) }, ty: Type::list(key_ty.clone()), line };
            let keys = self.lower_expr(ctx, &stage);
            self.ensure_record_type(crate::sigs::PAIR_REC);
            return Term::Call("F.list.sort_decorated".into(), vec![Term::TmplTy(kbt), Term::TmplTy(ebt), Term::TmplRef(lt), keys, xs]);
        }
        Term::Call("F.list.sort_by_key_env".into(), vec![Term::TmplTy(env_ty), Term::TmplTy(ebt), Term::TmplTy(kbt), Term::TmplRef(code), Term::TmplRef(lt), env, list])
    }

    fn lower_module_call(&mut self, ctx: &mut FnCtx, name: &str, args: &[TExpr], _arg_tys: &[Type], _ret: &Type, line: usize) -> Term {
        let targs: Vec<Term> = args.iter().map(|a| self.lower_expr(ctx, a)).collect();
        let (module, member) = name.split_once('.').unwrap();
        match (module, member) {
            ("math", "pi") => Term::Call("F32.pi".into(), vec![]),
            ("math", "e") => Term::F32(std::f32::consts::E),
            ("math", "tau") => Term::F32(std::f32::consts::TAU),
            ("math", "inf") => Term::Call("F.f32.inf".into(), vec![]),
            ("math", f) if ["sqrt", "sin", "cos", "tan", "exp", "floor", "ceil", "abs", "log2", "log10", "asin", "acos", "atan"].contains(&f) => {
                Term::Call(format!("F32.{}", f), targs)
            }
            ("math", "log") => {
                if targs.len() == 1 {
                    Term::Call("F32.log".into(), targs)
                } else {
                    Term::Call("F.f32.log_base".into(), targs)
                }
            }
            ("math", "pow") => Term::Call("F32.pow".into(), targs),
            ("math", "atan2") => Term::Call("F32.atan2".into(), targs),
            ("math", "min") => Term::Call("F32.min".into(), targs),
            ("math", "max") => Term::Call("F32.max".into(), targs),
            ("strings", "join") => {
                if targs.len() == 1 {
                    Term::Call("F.list.join".into(), vec![targs[0].clone(), Term::Str(String::new())])
                } else {
                    Term::Call("F.list.join".into(), targs)
                }
            }
            ("strings", "char_code") => Term::Call("F.str.char_code".into(), targs),
            ("strings", "from_char_code") => Term::Call("F.str.from_char_code".into(), targs),
            ("lists", "flatten") => {
                let ebt = match self.store.resolve(&args[0].ty) {
                    Type::List(inner) => match self.store.resolve(&inner) {
                        Type::List(e) => self.ty(&e, &[], line),
                        _ => Ty::Unit,
                    },
                    _ => Ty::Unit,
                };
                Term::Call("F.list.flatten".into(), vec![Term::TyArg(ebt), targs[0].clone()])
            }
            ("lists", "repeat") => {
                let ebt = self.bty(ctx, &args[0].ty, line);
                Term::Call("F.list.repeat".into(), vec![Term::TyArg(ebt), targs[0].clone(), targs[1].clone()])
            }
            ("lists", "enumerate") => {
                let ebt = match self.store.resolve(&args[0].ty) {
                    Type::List(e) => self.ty(&e, &[], line),
                    _ => Ty::Unit,
                };
                self.ensure_record_type(crate::sigs::PAIR_REC);
                Term::Call("F.list.enumerate".into(), vec![Term::TyArg(ebt), targs[0].clone()])
            }
            ("lists", "zip") => {
                let a = match self.store.resolve(&args[0].ty) {
                    Type::List(e) => self.ty(&e, &[], line),
                    _ => Ty::Unit,
                };
                let b = match self.store.resolve(&args[1].ty) {
                    Type::List(e) => self.ty(&e, &[], line),
                    _ => Ty::Unit,
                };
                self.ensure_record_type(crate::sigs::PAIR_REC);
                Term::Call("F.list.zip".into(), vec![Term::TyArg(a), Term::TyArg(b), targs[0].clone(), targs[1].clone()])
            }
            ("io", "read_file") => {
                let call = Term::Call("F.io.read_file".into(), targs);
                self.temp(ctx, call, Ty::result(Ty::Str, Ty::Str), true)
            }
            ("io", "write_file") => {
                let call = Term::Call("F.io.write_file".into(), targs);
                self.temp(ctx, call, Ty::result(Ty::Str, Ty::Unit), true)
            }
            ("time", "now") => {
                let call = Term::Call("F.time.now".into(), vec![]);
                self.temp(ctx, call, Ty::U32, true)
            }
            _ => {
                self.error(line, format!("unsupported module member ${}", name));
                Term::unit()
            }
        }
    }

    // -- methods on builtin types --------------------------------------------

    #[allow(clippy::too_many_arguments)]
    pub fn lower_builtin_method(&mut self, ctx: &mut FnCtx, recv_ty: &Type, name: &str, recv: Term, args: Vec<Term>, arg_tys: &[Type], arg_exprs: &[&TExpr], ret: &Type, line: usize) -> Term {
        let _ = arg_tys;
        match recv_ty {
            Type::Str => {
                let f = match name {
                    "length" => "F.str.len",
                    "upper" => "String.to_upper",
                    "lower" => "String.to_lower",
                    "trim" => "String.trim",
                    "trim_start" => "String.trim_start",
                    "trim_end" => "String.trim_end",
                    "split" => {
                        if args.is_empty() {
                            return Term::Call("F.str.split_ws".into(), vec![recv]);
                        }
                        "F.str.split"
                    }
                    "lines" => "String.lines",
                    "replace" => "F.str.replace",
                    "contains" => "String.contains",
                    "starts_with" => "String.starts_with",
                    "ends_with" => "String.ends_with",
                    "index_of" => "F.str.index_of",
                    "chars" => "F.str.chars",
                    "repeat" => "F.str.repeat",
                    "to_int" => {
                        let call = Term::Call("F.i32.parse_or_abort".into(), vec![recv]);
                        return self.adapt_call(ctx, call, Mode::Result, Ty::U32, line);
                    }
                    "to_float" => {
                        let call = Term::Call("F.f32.parse_or_abort".into(), vec![recv]);
                        return self.adapt_call(ctx, call, Mode::Result, Ty::F32, line);
                    }
                    "parse_int" => "F.i32.parse_result",
                    "parse_float" => "F.f32.parse_result",
                    "is_empty" => "String.is_empty",
                    "reverse" | "reversed" => "String.reverse",
                    "to_str" => return recv,
                    "char_code" => "F.str.char_code",
                    "join" => {
                        return Term::Call("F.list.join".into(), vec![args[0].clone(), recv]);
                    }
                    "take" => "F.str.take",
                    "drop" => "F.str.drop",
                    _ => {
                        self.error(line, format!("unsupported string method .{}()", name));
                        return recv;
                    }
                };
                let mut a = vec![recv];
                a.extend(args);
                Term::Call(f.into(), a)
            }
            Type::Int => match name {
                "abs" => Term::Call("F.i32.abs".into(), vec![recv]),
                "to_str" => Term::Call("F.i32.show".into(), vec![recv]),
                "to_float" => Term::Call("F.i32.to_f32".into(), vec![recv]),
                "sqrt" => Term::Call("F32.sqrt".into(), vec![Term::Call("F.i32.to_f32".into(), vec![recv])]),
                _ => recv,
            },
            Type::Float => match name {
                "abs" => Term::Call("F32.abs".into(), vec![recv]),
                "floor" => Term::Call("F32.floor".into(), vec![recv]),
                "ceil" => Term::Call("F32.ceil".into(), vec![recv]),
                "sqrt" => Term::Call("F32.sqrt".into(), vec![recv]),
                "round" => {
                    if args.is_empty() {
                        Term::Call("F32.round".into(), vec![recv])
                    } else {
                        Term::Call("F.f32.round_digits".into(), vec![recv, args[0].clone()])
                    }
                }
                "to_str" => Term::Call("F.f32.show".into(), vec![recv]),
                "to_int" => Term::Call("F.f32.to_i32".into(), vec![recv]),
                _ => recv,
            },
            Type::List(elem) => {
                let e = (**elem).clone();
                let ebt = self.ty(&e, &[], line);
                let ta = Term::TyArg(ebt.clone());
                let tt = Term::TmplTy(ebt.clone());
                match name {
                    "length" => Term::Call("F.list.len".into(), vec![ta, recv]),
                    "map" | "filter" | "each" | "any" | "all" | "find" | "count" => {
                        let (code, env, env_ty, fmode) = match self.stage_parts(ctx, arg_exprs[0], line) {
                            Some(p) => p,
                            None => return recv,
                        };
                        let suffix = match fmode {
                            Mode::Pure => "_env",
                            Mode::Result => "_res_env",
                            Mode::Io => "_io_env",
                        };
                        let out_bt = match self.store.resolve(&arg_exprs[0].ty) {
                            Type::Fn(_, r, _) => self.ty(&self.store.resolve(&r), &[], line),
                            _ => Ty::Unit,
                        };
                        let rt = self.bty(ctx, ret, line);
                        let mut targs = vec![Term::TmplTy(env_ty), tt];
                        if name == "map" {
                            targs.push(Term::TmplTy(out_bt.clone()));
                        }
                        if name == "each" {
                            targs.push(Term::TmplTy(out_bt.clone()));
                        }
                        targs.push(Term::TmplRef(code));
                        targs.push(env);
                        targs.push(recv);
                        let f = format!("F.list.{}{}", name, suffix);
                        let call = Term::Call(f, targs);
                        match fmode {
                            Mode::Pure => call,
                            m => self.adapt_call(ctx, call, m, rt, line),
                        }
                    }
                    "reduce" => {
                        let (code, env, env_ty, fmode) = match self.stage_parts(ctx, arg_exprs[0], line) {
                            Some(p) => p,
                            None => return recv,
                        };
                        let suffix = match fmode {
                            Mode::Pure => "_env",
                            Mode::Result => "_res_env",
                            Mode::Io => "_io_env",
                        };
                        let rt = self.bty(ctx, ret, line);
                        if args.len() == 2 {
                            let call = Term::Call(format!("F.list.foldl{}", suffix), vec![Term::TmplTy(env_ty), tt, Term::TmplTy(rt.clone()), Term::TmplRef(code), env, recv, args[1].clone()]);
                            match fmode {
                                Mode::Pure => call,
                                m => self.adapt_call(ctx, call, m, rt, line),
                            }
                        } else {
                            let call = Term::Call(format!("F.list.reduce1{}", suffix), vec![Term::TmplTy(env_ty), tt, Term::TmplRef(code), env, recv]);
                            let m = fmode.join(Mode::Result);
                            self.adapt_call(ctx, call, m, rt, line)
                        }
                    }
                    "sum" => match e {
                        Type::Float => Term::Call("F.list.sum_f32".into(), vec![recv]),
                        _ => Term::Call("F.list.sum_u32".into(), vec![recv]),
                    },
                    "min" | "max" => {
                        let f = match (name, &e) {
                            ("min", Type::Float) => "F.list.min_f32",
                            ("min", _) => "F.list.min_i32",
                            ("max", Type::Float) => "F.list.max_f32",
                            _ => "F.list.max_i32",
                        };
                        let call = Term::Call(f.into(), vec![recv]);
                        self.adapt_call(ctx, call, Mode::Result, ebt, line)
                    }
                    "join" => Term::Call("F.list.join".into(), vec![recv, args[0].clone()]),
                    "contains" => {
                        let eq = self.derive_eq(&e, line);
                        Term::Call("F.list.contains".into(), vec![tt, Term::TmplRef(eq), recv, args[0].clone()])
                    }
                    "index_of" => {
                        let eq = self.derive_eq(&e, line);
                        Term::Call("F.list.index_of".into(), vec![tt, Term::TmplRef(eq), recv, args[0].clone()])
                    }
                    "first" => Term::Call("F.list.first".into(), vec![ta, recv]),
                    "last" => Term::Call("F.list.last".into(), vec![ta, recv]),
                    "reverse" | "reversed" => Term::Call("F.list.reverse".into(), vec![ta, recv]),
                    "sort" | "sorted" => {
                        if args.is_empty() {
                            let lt = self.derive_lt(&e, line);
                            Term::Call("F.list.sort".into(), vec![tt, Term::TmplRef(lt), recv])
                        } else {
                            self.sort_by_key(ctx, recv, &e, arg_exprs[0], line)
                        }
                    }
                    "push" => {
                        let mut acc = recv;
                        for a in args {
                            acc = Term::Call("F.list.push".into(), vec![ta.clone(), acc, a]);
                        }
                        acc
                    }
                    "pop" => {
                        // handled by the statement lowering as a mutation; as a value: the last element
                        let call = Term::Call("F.list.last_or_abort".into(), vec![ta, recv]);
                        self.adapt_call(ctx, call, Mode::Result, ebt, line)
                    }
                    "drop_last" => Term::Call("F.list.drop_last".into(), vec![ta, recv]),
                    "take" => Term::Call("F.list.take".into(), vec![ta, recv, args[0].clone()]),
                    "drop" => Term::Call("F.list.drop".into(), vec![ta, recv, args[0].clone()]),
                    "to_list" => recv,
                    "is_empty" => Term::Call("F.list.is_empty".into(), vec![ta, recv]),
                    "flatten" => {
                        let inner = match self.store.resolve(&e) {
                            Type::List(i) => self.ty(&i, &[], line),
                            _ => Ty::Unit,
                        };
                        Term::Call("F.list.flatten".into(), vec![Term::TyArg(inner), recv])
                    }
                    "enumerate" => {
                        self.ensure_record_type(crate::sigs::PAIR_REC);
                        Term::Call("F.list.enumerate".into(), vec![ta, recv])
                    }
                    "zip" => {
                        self.ensure_record_type(crate::sigs::PAIR_REC);
                        let obt = match self.store.resolve(&arg_exprs[0].ty) {
                            Type::List(o) => self.ty(&o, &[], line),
                            _ => Ty::Unit,
                        };
                        Term::Call("F.list.zip".into(), vec![ta, Term::TyArg(obt), recv, args[0].clone()])
                    }
                    _ => {
                        self.error(line, format!("unsupported list method .{}()", name));
                        recv
                    }
                }
            }
            Type::Range => {
                let list = Term::Call("F.range.list".into(), vec![recv.clone()]);
                match name {
                    "to_list" | "reversed" | "reverse" => {
                        if name == "to_list" { list } else { Term::Call("F.list.reverse".into(), vec![Term::TyArg(Ty::U32), list]) }
                    }
                    "length" => Term::Call("F.range.len".into(), vec![recv]),
                    "contains" => Term::Call("F.range.contains".into(), vec![recv, args[0].clone()]),
                    "first" => Term::Call("F.range.start".into(), vec![recv]),
                    "last" => Term::op(Term::Call("F.range.end".into(), vec![recv]), "-", Term::U32(1), Ty::U32),
                    _ => {
                        // delegate to the list method
                        let list_ty = Type::list(Type::Int);
                        self.lower_builtin_method(ctx, &list_ty, name, list, args, arg_tys, arg_exprs, ret, line)
                    }
                }
            }
            Type::Stream(_) => {
                // take / first / drop on a stream: a pull loop
                self.lower_stream_consumer(ctx, name, arg_exprs, args, ret, line)
            }
            Type::Map(v) => {
                let vbt = self.ty(v, &[], line);
                let ta = Term::TyArg(vbt.clone());
                let q = Term::TyArg(Ty::Param("&2".into()));
                match name {
                    "keys" => Term::Call("Map.keys".into(), vec![q, ta, recv]),
                    "values" => Term::Call("Map.values".into(), vec![q, ta, recv]),
                    "entries" => {
                        self.ensure_record_type(crate::sigs::PAIR_REC);
                        Term::Call("F.map.entries".into(), vec![ta, recv])
                    }
                    "has" => Term::Call("F.map.has".into(), vec![ta, recv, args[0].clone()]),
                    "length" | "size" => Term::Call("F.map.size".into(), vec![ta, recv]),
                    "get" => Term::Call("F.map.lookup".into(), vec![ta, recv, args[0].clone()]),
                    "set" => Term::Call("Map.set".into(), vec![q, ta, recv, args[0].clone(), args[1].clone()]),
                    "remove" | "delete" => Term::Call("Map.del".into(), vec![q, ta, recv, args[0].clone()]),
                    _ => {
                        self.error(line, format!("unsupported dictionary method .{}()", name));
                        recv
                    }
                }
            }
            other => {
                self.error(line, format!("no method .{}() on {:?}", name, other));
                recv
            }
        }
    }

    /// `.take(n)` / `.first()` / `.drop(n)` on a lazy stream: a bounded pull loop.
    fn lower_stream_consumer(&mut self, ctx: &mut FnCtx, name: &str, arg_exprs: &[&TExpr], _args: Vec<Term>, ret: &Type, line: usize) -> Term {
        let _ = (arg_exprs, name, ret);
        self.error(line, "stream consumers are lowered through the receiver expression");
        let _ = ctx;
        Term::unit()
    }

    /// Builtin methods on records used as dictionaries (keys/values/entries/has).
    #[allow(clippy::too_many_arguments)]
    pub fn lower_record_builtin(&mut self, ctx: &mut FnCtx, rec: RecId, rt: &Type, name: &str, recv: Term, args: &[TExpr], _ret: &Type, line: usize) -> Term {
        let fields: Vec<(String, bool)> = self.tp.records[rec].fields.iter().map(|f| (f.name.clone(), f.public)).collect();
        let public: Vec<(usize, String)> = fields.iter().enumerate().filter(|(_, (n, p))| *p && n != "__parent").map(|(i, (n, _))| (i, n.clone())).collect();
        match name {
            "keys" => Term::List(public.iter().map(|(_, n)| Term::Str(n.clone())).collect()),
            "values" | "entries" => {
                let rbt = self.ty(rt, &[], line);
                let tmp = self.temp(ctx, recv, rbt, false);
                let mut items = Vec::new();
                for (i, n) in &public {
                    let get = self.field_get(rec, *i, rt, tmp.clone(), line);
                    if name == "values" {
                        items.push(get);
                    } else {
                        self.ensure_record_type(crate::sigs::PAIR_REC);
                        items.push(Term::Ctor(self.record_ctor_name(crate::sigs::PAIR_REC), vec![Term::Str(n.clone()), get]));
                    }
                }
                Term::List(items)
            }
            "has" => {
                let k = self.lower_expr(ctx, &args[0]);
                let names = Term::List(public.iter().map(|(_, n)| Term::Str(n.clone())).collect());
                Term::Call("F.list.contains".into(), vec![Term::TmplTy(Ty::Str), Term::TmplRef("String.eq".into()), names, k])
            }
            _ => {
                self.error(line, format!("{} has no method {}()", self.tp.records[rec].name, name));
                recv
            }
        }
    }

    /// `member_code` for use from expr.rs.
    pub fn member_code_pub(&mut self, d: DefId, params: &[Type], ret: &Type, line: usize) -> (String, Ty) {
        self.member_code(d, params, ret, line)
    }
}
