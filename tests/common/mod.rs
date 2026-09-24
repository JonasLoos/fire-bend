// Shared by the integration tests: whether to run `bend`, and how.
//
// BEND_TESTS=skip never runs it; BEND_TESTS=require always does and fails
// when it is missing; otherwise it runs when `bend` is on PATH.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

pub fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Whether this run checks programs with `bend`.
pub fn use_bend() -> bool {
    let mode = std::env::var("BEND_TESTS").unwrap_or_default();
    if mode == "skip" {
        return false;
    }
    let available = Command::new("bend").arg("version").output().is_ok_and(|o| o.status.success());
    assert!(available || mode != "require", "bend is not on PATH");
    available
}

/// Run `bend` with these arguments.
pub fn bend<S: AsRef<std::ffi::OsStr>>(args: &[S]) -> Output {
    Command::new("bend").args(args).env("BEND_NO_TELEMETRY", "1").output().expect("run bend")
}

/// Stdout and stderr together.
pub fn text(out: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// A fresh scratch directory for one test.
pub fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("fire-{}-{}", name, std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The files with this extension under a directory of the repository, sorted.
pub fn files(dir: &str, ext: &str) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = walkdir::WalkDir::new(repo().join(dir))
        .into_iter()
        .map(|e| e.unwrap().into_path())
        .filter(|p: &PathBuf| p.extension().is_some_and(|e| e == ext))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .{} files under {}", ext, dir);
    paths
}

/// Write `source` to `<dir>/<name>` and return the path.
pub fn write(dir: &Path, name: &str, source: &str) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, source).unwrap();
    path
}
