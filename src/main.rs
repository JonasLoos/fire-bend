// src/main.rs — the `fire` command line.
use clap::Parser;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

/// Compile a Fire program to Bend 2 and run it.
#[derive(Parser)]
#[command(name = "fire", version, about, arg_required_else_help = true)]
struct Cli {
    /// The program to compile
    file: String,
    /// Where to write instead of running: a `.bend` file gets the generated
    /// source; anything else is built by `bend` (a native binary, or
    /// JavaScript for a `.js` name)
    #[arg(short, long, value_name = "PATH")]
    output: Option<PathBuf>,
    /// Print the inferred type, effects and termination argument of every def
    #[arg(long)]
    types: bool,
    /// Run Bend's checker on the program and its laws, and report which
    /// laws are proven, which are open claims, and which code is unsafe
    #[arg(long)]
    check: bool,
    /// Check every law on generated instances (a property test)
    #[arg(long)]
    test: bool,
    /// Reject the program if any of it is `unsafe` (unchecked termination)
    #[arg(long)]
    total: bool,
}

fn main() {
    let cli = Cli::parse();
    let source = match std::fs::read_to_string(&cli.file) {
        Ok(s) => s,
        Err(e) => fail(&format!("cannot read {}: {}", cli.file, e)),
    };
    if cli.types {
        match fire_bend::describe_types(&source) {
            Ok(text) => print!("{}", text),
            Err(diags) => report(&cli.file, &diags),
        }
        return;
    }
    if cli.total || cli.check {
        let (image, rep) = match fire_bend::compile_for_check(&source) {
            Ok(x) => x,
            Err(diags) => report(&cli.file, &diags),
        };
        if cli.total && !rep.unsafe_defs.is_empty() {
            for (name, line) in &rep.unsafe_defs {
                eprintln!("{}: line {}: {} is `unsafe def`; --total accepts only code whose termination is checked", cli.file, line, name);
            }
            process::exit(1);
        }
        if cli.check {
            process::exit(check(&cli.file, image, &rep));
        }
    }
    if cli.test {
        let image = match fire_bend::compile_tests(&source) {
            Ok(s) => s,
            Err(diags) => report(&cli.file, &diags),
        };
        match fire_bend::run_with_bend(&image, &cli.file) {
            Ok(status) => process::exit(status),
            Err(e) => fail(&e),
        }
    }
    let bend_source = match fire_bend::compile(&source) {
        Ok(s) => s,
        Err(diags) => report(&cli.file, &diags),
    };
    match cli.output {
        None => match fire_bend::run_with_bend(&bend_source, &cli.file) {
            Ok(status) => process::exit(status),
            Err(e) => build_failed(&cli.file, &source, &e),
        },
        Some(out) if out.extension().is_some_and(|e| e == "bend") => {
            if let Err(e) = std::fs::write(&out, &bend_source) {
                fail(&format!("cannot write {}: {}", out.display(), e));
            }
        }
        Some(out) => {
            let src = out.with_extension("bend");
            if let Err(e) = std::fs::write(&src, &bend_source) {
                fail(&format!("cannot write {}: {}", src.display(), e));
            }
            let lane = if out.extension().is_some_and(|e| e == "js") { fire_bend::Lane::Js } else { fire_bend::Lane::from_env() };
            match fire_bend::build_with_bend(&src, &out, lane) {
                Ok(_) => {
                    let _ = std::fs::remove_file(&src);
                }
                Err(e) => build_failed(&cli.file, &source, &e),
            }
        }
    }
}

/// `fire --check`: Bend's checker over the image with every law (and the
/// proofs of `<name>.proof.bend`, when it exists), then the report.
fn check(file: &str, image: String, rep: &fire_bend::Report) -> i32 {
    use fire_bend::core::Proof;
    let path = Path::new(file);
    let proof_path = path.with_extension("proof.bend");
    let proofs = std::fs::read_to_string(&proof_path).ok();
    let proven_by_file: Vec<String> = match &proofs {
        Some(text) => rep.laws.iter().filter(|(n, _, p)| *p == Proof::Open && defines(text, n)).map(|(n, _, _)| n.clone()).collect(),
        None => vec![],
    };
    let mut full = image;
    if let Some(text) = &proofs {
        full.push_str("\n# ---- ");
        full.push_str(&proof_path.display().to_string());
        full.push('\n');
        full.push_str(text);
    }
    let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("program");
    let dir = std::env::temp_dir().join(format!("fire-check-{}-{}", stem, process::id()));
    if let Err(e) = std::fs::create_dir_all(&dir) {
        fail(&format!("cannot create {}: {}", dir.display(), e));
    }
    let src = dir.join(format!("{}.bend", stem));
    if let Err(e) = std::fs::write(&src, &full) {
        fail(&format!("cannot write {}: {}", src.display(), e));
    }
    let out = match Command::new("bend").arg(&src).arg("--check-only").env("BEND_NO_TELEMETRY", "1").output() {
        Ok(o) => o,
        Err(e) => fail(&format!("cannot run `bend` ({}); is it installed and on PATH?", e)),
    };
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
    let open: Vec<&(String, usize, Proof)> = rep.laws.iter().filter(|(n, _, p)| *p == Proof::Open && !proven_by_file.contains(n)).collect();
    // open laws are Bend's TODOs; anything else is a real rejection
    let todo_only = text.contains(" found.") && text.contains("TODO") && !text.contains("- expected");
    let mut status = 0;
    let mut failed: Option<String> = None;
    if !out.status.success() && !todo_only {
        status = 1;
        match explain(&text, &rep.laws.iter().map(|(n, l, _)| (n.clone(), *l)).collect::<Vec<_>>()) {
            // a failing def named after a law proven in the file is that proof
            Some((name, _)) if proven_by_file.contains(&name) => {
                let line = rep.laws.iter().find(|(n, _, _)| *n == name).map(|(_, l, _)| *l).unwrap_or(0);
                let (lhs, rhs) = (field(&text, "- expected :"), field(&text, "- observed :"));
                eprintln!("{}: line {}: the proof of law {} in {} does not check: expected {}, found {}", file, line, name, proof_path.display(), lhs.unwrap_or("?".into()), rhs.unwrap_or("?".into()));
                failed = Some(name);
            }
            Some((name, message)) => {
                eprintln!("{}: {}", file, message);
                failed = Some(name);
            }
            None => eprintln!("{}: Bend rejected the program:\n{}", file, text.trim_end()),
        }
    }
    if !rep.laws.is_empty() {
        println!("laws:");
        let width = rep.laws.iter().map(|(n, _, _)| n.len()).max().unwrap_or(0);
        for (name, _, proof) in &rep.laws {
            let how = match proof {
                _ if failed.as_deref() == Some(name.as_str()) && proven_by_file.contains(name) => "its proof does not check".to_string(),
                _ if failed.as_deref() == Some(name.as_str()) => "does NOT hold".to_string(),
                // Bend stopped at a rejection: nothing it would certify is known
                Proof::Open if status != 0 && !proven_by_file.contains(name) => "open: a claim".to_string(),
                _ if status != 0 => "not checked: Bend rejected the program".to_string(),
                _ if proven_by_file.contains(name) => format!("proven in {}", proof_path.display()),
                Proof::Closed => "proven: Bend computed both sides".to_string(),
                Proof::Finite => "proven: every case of its finite types".to_string(),
                Proof::Open => "open: a claim (fire --test samples it; a proof in the .proof.bend file settles it)".to_string(),
            };
            println!("  {:width$}  {}", name, how, width = width);
        }
    }
    if rep.unsafe_defs.is_empty() {
        if status == 0 && rep.partial_matches.is_empty() {
            println!("every def terminates and every match is covered (checked by Bend)");
        } else if status == 0 {
            println!("every def terminates (checked by Bend)");
        }
    } else {
        println!("unsafe (termination not checked):");
        for (name, line) in &rep.unsafe_defs {
            println!("  {} (line {})", name, line);
        }
        let callers: Vec<&str> = rep.relying.iter().map(|(n, _)| n.as_str()).collect();
        if !callers.is_empty() {
            println!("  and what calls it: {}", callers.join(", "));
        }
    }
    if !rep.partial_matches.is_empty() {
        println!("matches that cover only some values, and abort on the rest:");
        for (line, missed) in &rep.partial_matches {
            println!("  line {}: no arm accepts {}", line, missed);
        }
    }
    if status == 0 && !open.is_empty() {
        println!("{} open law(s)", open.len());
    }
    status
}

/// A Bend rejection that points at a law: the law and a message about it.
fn explain(text: &str, laws: &[(String, usize)]) -> Option<(String, String)> {
    let loc = location(text)?;
    let (name, line) = laws.iter().find(|(n, _)| *n == loc)?;
    let (lhs, rhs) = (field(text, "- expected :"), field(text, "- observed :"));
    Some((name.clone(), format!("line {}: law {} does not hold: one side is {} and the other {}", line, name, lhs.unwrap_or("?".into()), rhs.unwrap_or("?".into()))))
}

/// The laws of a source by name and line (`law name` at the start of a line).
fn laws_of(source: &str) -> Vec<(String, usize)> {
    source.lines().enumerate().filter_map(|(i, l)| {
        let rest = l.strip_prefix("law ")?;
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        if name.is_empty() { None } else { Some((name, i + 1)) }
    }).collect()
}

/// A failed build: explained when a law does not hold, verbatim otherwise.
fn build_failed(file: &str, source: &str, message: &str) -> ! {
    match explain(message, &laws_of(source)) {
        Some((_, m)) => fail(&format!("{}: {}", file, m)),
        None => fail(message),
    }
}

/// Whether a Bend source defines a def of this name.
fn defines(text: &str, name: &str) -> bool {
    text.lines().any(|l| l.starts_with(&format!("def {}(", name)))
}

/// The def Bend's error points at (`Location: name`).
fn location(text: &str) -> Option<String> {
    text.lines().find_map(|l| l.strip_prefix("Location: ")).map(|s| s.trim().to_string())
}

fn field(text: &str, key: &str) -> Option<String> {
    text.lines().find_map(|l| l.strip_prefix(key)).map(|s| s.trim().to_string())
}

fn report(path: &str, diags: &[fire_bend::Diag]) -> ! {
    for d in diags {
        eprintln!("{}: {}", Path::new(path).display(), d);
    }
    process::exit(1)
}

fn fail(message: &str) -> ! {
    eprintln!("{}", message);
    process::exit(1)
}
