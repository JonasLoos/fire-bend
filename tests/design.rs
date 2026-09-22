// tests/design.rs
// The Bend programs under docs/design/ are the evidence behind
// docs/design.md: each shows one shape the compiler is to emit and is kept
// honest by running it through `bend`. A `<name>.out` is the expected
// output of `bend <name>.bend`; a `<name>.check` is text that
// `bend <name>.bend --check-only` must print (an open law reports a TODO).
//
// Like tests/programs.rs: BEND_TESTS=skip does nothing here, BEND_TESTS=require
// fails when `bend` is missing, and otherwise the test is skipped without it.

use std::path::PathBuf;
use std::process::Command;

fn images() -> Vec<PathBuf> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/design");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {}", dir.display(), e))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "bend"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no images under {}", dir.display());
    paths
}

fn bend(args: &[&str]) -> Option<std::process::Output> {
    Command::new("bend").args(args).env("BEND_NO_TELEMETRY", "1").output().ok()
}

#[test]
fn design_images_check_under_bend() {
    let mode = std::env::var("BEND_TESTS").unwrap_or_default();
    if mode == "skip" {
        return;
    }
    let available = bend(&["version"]).is_some_and(|o| o.status.success());
    if !available {
        assert!(mode != "require", "bend is not on PATH");
        return;
    }
    for path in images() {
        let name = path.display().to_string();
        let check = path.with_extension("check");
        if let Ok(expected) = std::fs::read_to_string(&check) {
            let out = bend(&[&name, "--check-only"]).expect("run bend");
            let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
            assert!(text.contains(expected.trim()), "{}: expected {:?} in bend's report:\n{}", name, expected.trim(), text);
            continue;
        }
        let golden = std::fs::read_to_string(path.with_extension("out"))
            .unwrap_or_else(|_| panic!("{}: missing .out (or .check)", name));
        let out = bend(&[&name]).expect("run bend");
        let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert_eq!(text, golden, "{}: output differs from the golden", name);
    }
}
