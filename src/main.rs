// src/main.rs — the `fire` command line.
use clap::Parser;
use std::path::{Path, PathBuf};
use std::process;

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
    /// Print the inferred type and effect of every def instead
    #[arg(long)]
    types: bool,
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
    let bend_source = match fire_bend::compile(&source) {
        Ok(s) => s,
        Err(diags) => report(&cli.file, &diags),
    };
    match cli.output {
        None => match fire_bend::run_with_bend(&bend_source, &cli.file) {
            Ok(status) => process::exit(status),
            Err(e) => fail(&e),
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
                Err(e) => fail(&e),
            }
        }
    }
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
