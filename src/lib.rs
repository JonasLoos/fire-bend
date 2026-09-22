// src/lib.rs
// Fire: parse a program (grammar/fire.pest → ast.rs), infer types and
// effects (infer/), lower to Bend IR (lower/) and print it (ir.rs).
// See docs/compiler.md.

use pest::Parser;
use pest_derive::Parser;

pub mod ast;
pub mod check;
pub mod core;
pub mod ir;
pub mod lower;
pub mod prune;
pub mod testgen;
pub mod types;

/// A diagnostic: a source line (0 when unknown) and a message.
#[derive(Debug, Clone)]
pub struct Diag {
    pub line: usize,
    pub message: String,
}

impl std::fmt::Display for Diag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.line > 0 {
            write!(f, "line {}: {}", self.line, self.message)
        } else {
            write!(f, "{}", self.message)
        }
    }
}

#[derive(Parser)]
#[grammar = "grammar/fire.pest"] // relative to src/
pub struct FireParser;

/// Parses a Fire source string into a Pest result.
pub fn parse_source(source: &str) -> Result<pest::iterators::Pairs<'_, Rule>, Box<pest::error::Error<Rule>>> {
    // pest's generated parser recurses through the whole precedence tower per
    // nesting level with no stack guard of its own (so no chance to grow
    // mid-parse); run it on a dedicated large stack segment up front.
    #[cfg(not(target_arch = "wasm32"))]
    let parsed = stacker::grow(32 * 1024 * 1024, || {
        FireParser::parse(Rule::program, source).map_err(Box::new)
    })
    .map_err(|e| *e);
    #[cfg(target_arch = "wasm32")]
    let parsed = FireParser::parse(Rule::program, source);
    parsed.map_err(|e| Box::new(humanize_parse_error(source, e)))
}

/// What a grammar rule means to someone reading an error message. Many rules
/// collapse onto the same phrase on purpose: "expected an expression" beats
/// pest's raw dump of every alternative that can start one.
fn rule_description(rule: Rule) -> String {
    use Rule::*;
    let text = match rule {
        EOI => "end of input",
        nl | nls | block_nl => "a newline",
        indentation => "matching indentation",
        block | do_or_block => "'do' or an indented block",
        statement | statement_raw => "a statement",
        expression_big | expression_small | atom | paren_expr
        | pipeline_expr | pipeline_expr_simple | lambda_expr | loop_expr | if_expr
        | assignment_expr | logic_or | logic_or_simple | logic_and | logic_and_simple
        | logic_not | comparison | comparison_simple | type_or | type_or_simple
        | xor | xor_simple | type_and | type_and_simple | range | shift | shift_simple
        | additive | additive_simple
        | multiplicative | multiplicative_simple | unary
        | power | typecheck | call_or_access | call_or_access_simple => "an expression",
        pipeline_block | pipeline_block_line | logic_or_block | logic_or_block_line
        | logic_and_block | logic_and_block_line | comparison_block | comparison_block_line
        | type_or_block | type_or_block_line | xor_block | xor_block_line
        | type_and_block | type_and_block_line | shift_block | shift_block_line
        | additive_block | additive_block_line | multiplicative_block
        | multiplicative_block_line | access_block | access_block_line
        | bracket_block | list_block | object_block | call_block | call_line
            => "a continuation line starting with an operator",
        function_call_args => "call arguments '(...)'",
        list_access_args => "an index '[...]'",
        call_arg_list | call_arg | named_arg => "an argument",
        pipeline_op => "a pipeline operator ('|>', '*>', '?>', '!>')",
        lambda_op => "'=>'",
        assignment_op => "an assignment operator",
        comparison_op => "a comparison operator",
        add_op | mul_op | power_op => "an arithmetic operator",
        xor_op | shift_op => "a bitwise operator",
        unary_op => "'-' or 'not'",
        range_op => "'..'",
        typecheck_op => "':' (type annotation)",
        member_access_op => "'.'",
        type_or_op => "'|'",
        type_and_op => "'&'",
        identifier | id_chars => "a name",
        number | hex_number | bin_number | scientific_number
        | decimal_number => "a number",
        string | fstring | tstring => "a string",
        fstring_interp | fstring_formatted => "an interpolation '{...}'",
        format_spec => "a format spec",
        fstring_escape | fstring_text => "string text",
        boolean | kw_true | kw_false => "'true' or 'false'",
        nothing_lit | kw_nothing => "'nothing'",
        list | list_entries | list_entry => "a list",
        object | object_entries | object_entry => "an object entry",
        ellipsis => "'...'",
        previous_result => "'$'",
        import => "a '$module' import",
        comment | documentation => "a comment",
        variable_declaration | kw_var => "'var'",
        assignment_stmt => "an assignment",
        return_stmt | kw_return => "'return'",
        break_stmt | kw_break => "'break'",
        continue_stmt | kw_continue => "'continue'",
        while_stmt | kw_while => "'while'",
        for_stmt | kw_for => "'for'",
        if_stmt | kw_if => "'if'",
        r#else | kw_else => "'else'",
        kw_elif => "'elif'",
        match_stmt | kw_match => "'match'",
        guarded_arm => "a match arm",
        method_stmt | method_args => "a method call",
        loop_clause => "'for' or 'while'",
        kw_def => "'def'",
        kw_public => "'public'",
        kw_in => "'in'",
        kw_not => "'not'",
        kw_and => "'and'",
        kw_or => "'or'",
        kw_do => "'do'",
        type_stmt | kw_type => "'type'",
        law_stmt | law_for | kw_law => "'law'",
        kw_unsafe => "'unsafe'",
        keyword => "a keyword",
        w => "whitespace",
        other => return format!("{:?}", other),
    };
    text.to_string()
}

/// Rewrite a pest parse error into plain language: rule names become
/// descriptions, duplicates collapse, the offending character is shown, and
/// a couple of common habits from other languages get a hint.
fn humanize_parse_error(source: &str, e: pest::error::Error<Rule>) -> pest::error::Error<Rule> {
    use pest::error::{ErrorVariant, InputLocation};
    let ErrorVariant::ParsingError { positives, .. } = &e.variant else {
        return e;
    };
    let pos = match e.location {
        InputLocation::Pos(p) => p,
        InputLocation::Span((start, _)) => start,
    };

    // an operator-position rule: one of many ways to continue an expression.
    // When several are possible at once, listing them all drowns the message.
    fn continues_expression(rule: Rule) -> bool {
        use Rule::*;
        matches!(rule,
            pipeline_op | lambda_op | assignment_op | comparison_op | add_op | mul_op
            | power_op | range_op | typecheck_op | member_access_op | type_or_op
            | type_and_op | xor_op | shift_op | function_call_args | list_access_args
            | pipeline_block | pipeline_block_line | logic_or_block | logic_or_block_line
            | logic_and_block | logic_and_block_line | comparison_block
            | comparison_block_line | type_or_block | type_or_block_line
            | xor_block | xor_block_line | shift_block | shift_block_line
            | type_and_block | type_and_block_line | additive_block | additive_block_line
            | multiplicative_block | multiplicative_block_line | access_block
            | access_block_line | bracket_block | list_block | object_block | call_block | call_line)
    }

    let collapse = positives.iter().filter(|r| continues_expression(**r)).count() >= 4;
    let mut expected: Vec<String> = Vec::new();
    for rule in positives {
        let description = if collapse && continues_expression(*rule) {
            "an operator continuing the expression".to_string()
        } else {
            rule_description(*rule)
        };
        if !expected.contains(&description) {
            expected.push(description);
        }
    }

    let rest = &source[pos.min(source.len())..];
    let found = match rest.chars().next() {
        None => "end of input".to_string(),
        Some('\n') => "end of line".to_string(),
        Some(c) => format!("'{}'", c),
    };
    let mut message = match expected.split_last() {
        None => format!("unexpected {}", found),
        Some((only, [])) => format!("unexpected {}; expected {}", found, only),
        Some((last, init)) => format!(
            "unexpected {}; expected {} or {}", found, init.join(", "), last),
    };

    let at_colon = rest.starts_with(':')
        && matches!(rest[1..].trim_start_matches(' ').chars().next(), None | Some('\n') | Some('#'));
    let after_colon = source[..pos].ends_with(':')
        && matches!(rest.chars().next(), None | Some('\n') | Some('#'));
    if at_colon || after_colon {
        message.push_str("\n  hint: Fire blocks are introduced by indentation alone — no ':' after if/for/while/def");
    }
    let prev_is_name = pos > 0
        && source[..pos].chars().next_back().is_some_and(|c| c.is_alphanumeric() || c == '_');
    if (rest.starts_with('"') || rest.starts_with('\'')) && prev_is_name {
        message.push_str("\n  hint: Fire strings interpolate {name} automatically — no 'f' prefix needed");
    }
    if collapse && (rest.starts_with("for ") || rest.starts_with("for\t")) {
        message.push_str("\n  hint: Fire comprehensions put the loop first — `[for x in xs do x * 2]`, not `[x * 2 for x in xs]`");
    }
    if rest.starts_with('/') && source[..pos].ends_with('/') {
        message.push_str("\n  hint: '//' isn't Fire — comments start with '#', floor division is (a / b).floor()");
    }

    let variant = ErrorVariant::<Rule>::CustomError { message };
    let rebuilt = match e.location {
        InputLocation::Pos(p) => pest::Position::new(source, p)
            .map(|p| pest::error::Error::new_from_pos(variant, p)),
        InputLocation::Span((start, end)) => pest::Span::new(source, start, end)
            .map(|s| pest::error::Error::new_from_span(variant, s)),
    };
    rebuilt.unwrap_or(e)
}

/// Parses pest pairs into an AST.
pub fn parse_to_ast(pairs: pest::iterators::Pairs<'_, Rule>) -> Result<ast::Program, Box<dyn std::error::Error>> {
    ast::from_pest_pairs(pairs)
}

/// Parse a source string all the way to an AST.
pub fn parse_program(source: &str) -> Result<ast::Program, Box<dyn std::error::Error>> {
    let pairs = parse_source(source)?;
    parse_to_ast(pairs)
}

fn parse_diag(source: &str) -> Result<ast::Program, Vec<Diag>> {
    parse_program(source).map_err(|e| vec![Diag { line: 0, message: format!("{}", e) }])
}

/// Compile a Fire program to Bend source: a runnable image, carrying the
/// laws the compiler proves (a false one fails Bend's check).
pub fn compile(source: &str) -> Result<String, Vec<Diag>> {
    let program = parse_diag(source)?;
    let core = check::check_program(&program)?;
    if std::env::var("FIRE_DUMP_CORE").is_ok() {
        eprintln!("{:#?}", core.defs);
    }
    let ir = lower::lower_program(&core, lower::Laws::Proven)?;
    Ok(ir.render())
}

/// What `fire --check` reports besides Bend's verdict.
#[derive(Debug, Clone, Default)]
pub struct Report {
    /// Every law: name, line, and how it is proven.
    pub laws: Vec<(String, usize, core::Proof)>,
    /// Defs declared `unsafe def`, with their lines.
    pub unsafe_defs: Vec<(String, usize)>,
    /// Defs that are not unsafe themselves but call unsafe code.
    pub relying: Vec<(String, usize)>,
}

/// The image `fire --check` hands to Bend (every law, the open ones as
/// claims), and the report of laws and unsafe code.
pub fn compile_for_check(source: &str) -> Result<(String, Report), Vec<Diag>> {
    let program = parse_diag(source)?;
    let core = check::check_program(&program)?;
    let ir = lower::lower_program(&core, lower::Laws::All)?;
    let mut report = Report::default();
    for l in &core.laws {
        report.laws.push((l.name.clone(), l.line, l.proof.clone()));
    }
    for d in &core.defs {
        if matches!(d.kind, core::DefKind::Lambda | core::DefKind::Law) {
            continue;
        }
        let name = if matches!(d.kind, core::DefKind::Main) { "the program's top level".to_string() } else { d.name.clone() };
        if d.unsafe_ {
            report.unsafe_defs.push((name, d.line));
        } else if d.relies_on_unsafe {
            report.relying.push((name, d.line));
        }
    }
    Ok((ir.render(), report))
}

/// The property-test image of a program (`fire --test`): its definitions
/// and bindings, and every law checked on generated instances.
pub fn compile_tests(source: &str) -> Result<String, Vec<Diag>> {
    let program = parse_diag(source)?;
    let core = check::check_program(&program)?;
    let tests = testgen::test_program(&program, &core)?;
    let core2 = check::check_program(&tests)?;
    let ir = lower::lower_program(&core2, lower::Laws::Proven)?;
    Ok(ir.render())
}

/// Parse and check a program, returning one line per def with its resolved
/// type, effect and descent, then one per data type (`fire --types`).
pub fn describe_types(source: &str) -> Result<String, Vec<Diag>> {
    let program = parse_program(source).map_err(|e| vec![Diag { line: 0, message: format!("{}", e) }])?;
    let core = check::check_program(&program)?;
    let names = |id: types::TypeId| core.types[id].name.clone();
    let mut out = String::new();
    for d in &core.defs {
        if matches!(d.kind, core::DefKind::Lambda | core::DefKind::Law) || d.name.starts_with("__") {
            continue;
        }
        let mut shown: Vec<&types::Type> = vec![&d.scheme.ty];
        for c in &d.scheme.dicts {
            shown.push(&core.store.constraints[*c].subject);
        }
        let vars = types::var_names(&core.store, &shown);
        let ty = types::TypeDisplay { store: &core.store, ty: &d.scheme.ty, names: &names, vars: &vars };
        let mut tags: Vec<String> = vec![d.effect.to_string()];
        if d.relies_on_unsafe {
            tags.push("unsafe".into());
        }
        let descent = match &d.descent {
            core::Descent::None => String::new(),
            core::Descent::Structural(order) => {
                let names: Vec<&str> = order.iter().map(|i| d.params.get(*i).map(|p| p.name.as_str()).unwrap_or("?")).collect();
                format!(" descends on {}", names.join(", then "))
            }
            core::Descent::Fuel(i) => format!(" counts down {}", d.params.get(*i).map(|p| p.name.as_str()).unwrap_or("?")),
            core::Descent::Unsafe => String::new(),
        };
        let dicts = if d.scheme.dicts.is_empty() {
            String::new()
        } else {
            let ds: Vec<String> = d.scheme.dicts.iter().map(|c| {
                let cc = &core.store.constraints[*c];
                let subject = types::TypeDisplay { store: &core.store, ty: &cc.subject, names: &names, vars: &vars };
                format!("{} on {}", check::describe_class(&cc.class), subject)
            }).collect();
            format!(" needs {}", ds.join(", "))
        };
        let caps: Vec<&str> = d.captures.iter().map(|(n, _)| n.as_str()).collect();
        let captures = if caps.is_empty() { String::new() } else { format!(" captures {}", caps.join(", ")) };
        out.push_str(&format!("{} : {} [{}]{}{}{}\n", d.name, ty, tags.join(", "), descent, dicts, captures));
    }
    for t in core.types.iter().skip(types::BUILTIN_TYPES) {
        let params: Vec<types::Type> = t.params.iter().map(|v| types::Type::Var(*v)).collect();
        let vars = types::var_names(&core.store, &params.iter().collect::<Vec<_>>());
        let ctors: Vec<String> = t.ctors.iter().map(|c| {
            let fields: Vec<String> = c.fields.iter().map(|f| {
                let ty = types::TypeDisplay { store: &core.store, ty: &f.ty, names: &names, vars: &vars };
                format!("{}{}: {}", if f.public { "" } else { "~" }, f.name, ty)
            }).collect();
            if fields.is_empty() { c.name.clone() } else { format!("{}({})", c.name, fields.join(", ")) }
        }).collect();
        let kind = match t.kind {
            core::DataKind::Class { .. } => "class",
            core::DataKind::Record { .. } => "record",
            _ => "type",
        };
        out.push_str(&format!("{} {} = {}\n", kind, t.name, ctors.join(" | ")));
    }
    for l in &core.laws {
        out.push_str(&format!("law {} [{:?}]\n", l.name, l.proof));
    }
    Ok(out)
}

/// How a Bend program is built and run: a native binary (default) or the
/// JavaScript lane (`BEND_LANE=js`, or automatically when Bend's native code
/// generator crashes on a program its checker accepted).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lane {
    Native,
    Js,
}

impl Lane {
    pub fn from_env() -> Lane {
        if std::env::var("BEND_LANE").map(|v| v == "js").unwrap_or(false) { Lane::Js } else { Lane::Native }
    }
}

/// Build `src` with the `bend` binary into `out` (a native binary, or a
/// `.js` file on the JavaScript lane). Returns the lane actually used.
pub fn build_with_bend(src: &std::path::Path, out: &std::path::Path, lane: Lane) -> Result<Lane, String> {
    use std::process::Command;
    let bend = |out: &std::path::Path| {
        Command::new("bend")
            .arg(src)
            .arg("-o")
            .arg(out)
            .env("BEND_NO_TELEMETRY", "1")
            .output()
            .map_err(|e| format!("cannot run `bend` ({}); is it installed and on PATH?", e))
    };
    let mut lane = lane;
    let mut target = lane_output(out, lane);
    let mut build = bend(&target)?;
    if !build.status.success() && lane == Lane::Native && native_codegen_crashed(&build) {
        lane = Lane::Js;
        target = lane_output(out, lane);
        build = bend(&target)?;
    }
    if !build.status.success() {
        return Err(format!(
            "bend failed on {}:\n{}{}",
            src.display(),
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr)
        ));
    }
    Ok(lane)
}

/// The output path for a lane: `.js` is appended on the JavaScript lane.
pub fn lane_output(out: &std::path::Path, lane: Lane) -> std::path::PathBuf {
    match lane {
        Lane::Native => out.to_path_buf(),
        Lane::Js => {
            if out.extension().is_some_and(|e| e == "js") { out.to_path_buf() } else { out.with_extension("js") }
        }
    }
}

/// Run a program built by [`build_with_bend`], inheriting stdio.
pub fn run_built(out: &std::path::Path, lane: Lane) -> Result<i32, String> {
    use std::process::Command;
    let target = lane_output(out, lane);
    let status = match lane {
        Lane::Native => Command::new(&target).status(),
        Lane::Js => Command::new("node").arg(&target).status(),
    }
    .map_err(|e| format!("cannot run {}: {}", target.display(), e))?;
    Ok(status.code().unwrap_or(1))
}

/// Write the Bend source to a temporary directory, build it, run it, and
/// stream its output. Returns the program's exit status.
pub fn run_with_bend(bend_source: &str, origin: &str) -> Result<i32, String> {
    let stem = std::path::Path::new(origin).file_stem().and_then(|s| s.to_str()).unwrap_or("program").to_string();
    let dir = std::env::temp_dir().join(format!("fire-{}-{}", stem, std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot create {}: {}", dir.display(), e))?;
    let src = dir.join(format!("{}.bend", stem));
    std::fs::write(&src, bend_source).map_err(|e| format!("cannot write {}: {}", src.display(), e))?;
    let out = dir.join(&stem);
    let lane = build_with_bend(&src, &out, Lane::from_env())?;
    run_built(&out, lane)
}

/// A build that passed Bend's checker but died inside its native code
/// generator (an internal `TypeError`), as opposed to a rejected program.
pub fn native_codegen_crashed(build: &std::process::Output) -> bool {
    let text = format!("{}{}", String::from_utf8_lossy(&build.stdout), String::from_utf8_lossy(&build.stderr));
    text.contains("All terms check") && text.contains("TypeError")
}
