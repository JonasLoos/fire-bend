// tests/programs.rs
// Every program under examples/ and tests/cases/ compiles to Bend. When a
// `bend` binary is on PATH the program is also built and run, and its output
// must match the `<name>.out` golden next to it.
//
// BEND_TESTS=skip checks compilation only; BEND_TESTS=require fails (instead
// of skipping the run) when `bend` is missing.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn bend_available() -> bool {
    Command::new("bend").arg("version").output().map(|o| o.status.success()).unwrap_or(false)
}

fn programs(dir: &str) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = walkdir::WalkDir::new(repo().join(dir))
        .into_iter()
        .map(|e| e.unwrap().into_path())
        .filter(|p| p.extension().is_some_and(|e| e == "fire"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no programs under {}", dir);
    paths
}

/// Compile, and run through bend if possible. Returns the program's output.
fn compile_and_run(path: &Path) -> Option<String> {
    let source = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {}: {}", path.display(), e));
    let bend_source = match fire_bend::compile(&source) {
        Ok(s) => s,
        Err(diags) => {
            let msgs: Vec<String> = diags.iter().map(|d| d.to_string()).collect();
            panic!("{}: compilation failed:\n{}", path.display(), msgs.join("\n"));
        }
    };
    let mode = std::env::var("BEND_TESTS").unwrap_or_default();
    if mode == "skip" {
        return None;
    }
    if !bend_available() {
        assert!(mode != "require", "bend is not on PATH");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("fire-tests-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let stem = path.file_stem().unwrap().to_str().unwrap();
    let src = dir.join(format!("{}.bend", stem));
    std::fs::write(&src, &bend_source).unwrap();
    let bin = dir.join(stem);
    let lane = fire_bend::build_with_bend(&src, &bin, fire_bend::Lane::from_env())
        .unwrap_or_else(|e| panic!("{}: bend rejected the generated program:\n{}", path.display(), e));
    let target = fire_bend::lane_output(&bin, lane);
    let run = match lane {
        fire_bend::Lane::Native => Command::new(&target).output(),
        fire_bend::Lane::Js => Command::new("node").arg(&target).output(),
    }
    .expect("run the compiled program");
    let mut out = String::from_utf8_lossy(&run.stdout).to_string();
    if !run.status.success() {
        out.push_str(&String::from_utf8_lossy(&run.stderr));
    }
    Some(out)
}

fn check(path: &Path) {
    let golden = std::fs::read_to_string(path.with_extension("out"))
        .unwrap_or_else(|_| panic!("{}: missing golden", path.display()));
    if let Some(got) = compile_and_run(path) {
        assert_eq!(got, golden, "{}: output differs from the golden", path.display());
    }
}

#[test]
fn examples() {
    for p in programs("examples") {
        check(&p);
    }
}

#[test]
fn cases() {
    for p in programs("tests/cases") {
        check(&p);
    }
}

#[test]
fn unsupported_programs_are_rejected_with_a_message() {
    let cases: &[(&str, &str)] = &[
        ("x = 1\nx = 'a'\n", "reassign"),
        ("xs = [1, 'a']\n", "expected int, found str"),
        ("def f()\n    return async 1\n", "async"),
        ("\"{h}:{m}\" = \"1:2\"\n", "f-string"),
        // a helper a method uses is a method: it cannot run before the members exist
        ("def G\n    def h(x)\n        x\n    x = h(1)\n    public p = () => h(x)\nprint(G().p())\n", "before member x exists"),
        ("x = 1.5 & 2.5\n", "not defined on float"),
        ("xs: [int, str] = [1]\n", "one element type"),
    ];
    for (src, fragment) in cases {
        match fire_bend::compile(src) {
            Ok(_) => panic!("expected a diagnostic containing {:?} for:\n{}", fragment, src),
            Err(diags) => {
                let text: Vec<String> = diags.iter().map(|d| d.to_string()).collect();
                assert!(text.iter().any(|t| t.contains(fragment)), "expected {:?} in {:?}", fragment, text);
            }
        }
    }
}

#[test]
fn generated_source_is_deterministic() {
    let source = std::fs::read_to_string(repo().join("examples/word_stats.fire")).unwrap();
    let a = fire_bend::compile(&source).unwrap();
    let b = fire_bend::compile(&source).unwrap();
    assert_eq!(a, b);
    assert!(a.starts_with("import Base\n"));
    assert!(a.contains("def main() -> IO(Unit):"));
}
