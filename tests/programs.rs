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
        ("\"{h}:{m}\" = \"1:2\"\n", "invalid assignment target"),
        // a helper a method uses is a method: it cannot run before the object exists
        ("def G\n    def h(x)\n        x\n    x = h(1)\n    public p = () => h(x)\nprint(G().p())\n", "while the object is being built"),
        ("x = 1.5 & 2.5\n", "expected int, found float"),
        ("def f(n: int)\n    n + 0.5\n", "convert with `float(x)`"),
        // habits from Python get a hint
        ("xs = [1]\nprint(2 in xs)\n", "`xs.contains(x)`"),
        ("xs = [1]\nif 2 not in xs do print(1)\n", "`not xs.contains(x)`"),
        ("xs: [int, str] = [1]\n", "one element type"),
        // totality: every def must be seen to end, or say `unsafe def`
        ("var n = 0\nwhile n < 3 do n += 1\n", "may not terminate"),
        ("def f(n)\n    f(n + 1)\n", "cannot show that 'f' terminates"),
        ("def f(n)\n    if n == 0 do 0 else f(n - 1)\n", "cannot show that 'f' terminates"),
        ("def even(n)\n    if n <= 0 do true else odd(n - 1)\ndef odd(n)\n    if n <= 0 do false else even(n - 1)\nprint(even(4))\n", "mutual recursion"),
        ("for i in 0..\n    print(i)\n", "never ends"),
        ("def g(xs)\n    for x in xs\n        g(xs)\n    0\n", "calls itself inside a loop body"),
        // recursion through a function value has no image Bend can check
        ("type R\n    N(v: int, kids: [R])\ndef t(r)\n    match r\n        N(v, kids) => v + (kids *> t |> sum)\nprint(t(N(1, [])))\n", "passed as a function inside its own body"),
        // laws speak about pure, total defs and types
        ("def say(x)\n    print(x)\n    x\nlaw bad\n    say(1) == 1\n", "performs IO"),
        ("unsafe def spin(n)\n    spin(n + 1)\nlaw bad\n    spin(1) == 1\n", "relies on unsafe code"),
        ("limit = 3\nlaw uses_value\n    limit == 3\n", "a law speaks about defs and types"),
        // a lambda cannot change what it captured; the change would be lost
        ("def C()\n    public var n = 0\n    public bump = k =>\n        n += k\n        {ok: n}\nvar c = C()\nr = {ok: 1} |> x => c.bump(x)\n", "a lambda or nested def captures it by value"),
        ("def C()\n    public var n = 0\n    public bump = k => n += k\nvar c = C()\nxs = [1] *> c.bump($)\n", "a lambda or nested def captures it by value"),
        // a `return` cannot leave a match whose value is bound
        ("def g(xs: [int])\n    y = match xs\n        [] => 0\n        [a, ...rest] =>\n            if a > 5 do return 1\n            a\n    y\n", "`return` cannot leave"),
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

#[test]
fn laws_are_classified_and_property_tested() {
    use fire_bend::core::Proof;
    let source = std::fs::read_to_string(repo().join("tests/cases/laws_in_a_program.fire")).unwrap();
    let (image, report) = fire_bend::compile_for_check(&source).unwrap();
    let proof = |name: &str| report.laws.iter().find(|(n, _, _)| n == name).map(|(_, _, p)| p.clone()).unwrap();
    assert_eq!(proof("cycle_of_three"), Proof::Finite);
    assert_eq!(proof("twice_small"), Proof::Closed);
    assert_eq!(proof("twice_length"), Proof::Open);
    assert_eq!(proof("cents_text"), Proof::Open);
    // the check image carries every law; the runnable one only the proven ones
    assert!(image.contains("law twice_length:"));
    assert!(!fire_bend::compile(&source).unwrap().contains("law twice_length:"));
    assert!(report.unsafe_defs.is_empty());
    // the property-test image compiles, and under Bend every law holds
    let tests = fire_bend::compile_tests(&source).unwrap();
    if std::env::var("BEND_TESTS").unwrap_or_default() == "skip" || !bend_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("fire-law-tests-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("laws.bend");
    std::fs::write(&src, &tests).unwrap();
    let run = Command::new("bend").arg(&src).env("BEND_NO_TELEMETRY", "1").output().unwrap();
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{}", out);
    for law in ["cycle_of_three", "twice_small", "twice_length", "cents_text"] {
        assert!(out.contains(&format!("law {}: holds", law)), "{}", out);
    }
}

/// A law over a generic type is stated for ints, as `fire --test` samples
/// it: over `Unit` every value is equal, and a false law could be proven.
#[test]
fn laws_over_generic_types_are_stated_for_ints() {
    let src = "type Tree\n    Leaf\n    Node(left: Tree, value, right: Tree)\ndef rot(t)\n    match t\n        Node(Node(ll, x, lr), v, r) => Node(Node(ll, v, lr), x, r)\n        other => other\nlaw rot_is_identity\n    for t: Tree\n    rot(t) == t\n";
    let (image, _) = fire_bend::compile_for_check(src).unwrap();
    assert!(image.contains("for +t: Tree<U32>"), "{}", image);
}

/// `fire --check` reports a law proven in the `.proof.bend` file only when
/// Bend accepts the whole image; a failing proof is the proof's fault.
#[test]
fn check_reports_proofs_from_the_proof_file() {
    if std::env::var("BEND_TESTS").unwrap_or_default() == "skip" || !bend_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("fire-proof-tests-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let prog = dir.join("app.fire");
    std::fs::write(&prog, "def app(xs, ys)\n    match xs\n        [] => ys\n        [h, ...t] => [h] + app(t, ys)\nlaw app_nil_left\n    for xs: [int]\n    app([], xs) == xs\nlaw app_small\n    app([1], [2]) == [1, 2]\nlaw app_nil\n    for xs: [int]\n    app(xs, []) == xs\nprint(app([1], [2]))\n").unwrap();
    let run = |proof: &str| {
        std::fs::write(dir.join("app.proof.bend"), proof).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_fire")).arg(&prog).arg("--check").output().unwrap();
        (out.status.success(), format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)))
    };
    // a proof that checks
    let (ok, text) = run("def app_nil_left(xs):\n  {==}\n");
    assert!(ok && text.contains("app_nil_left  proven in") && text.contains("app_nil       open"), "{}", text);
    // a proof that does not: the law is not reported proven, nor are the others
    let (ok, text) = run("def app_nil_left(xs):\n  {==}\n\ndef app_nil(xs):\n  {==}\n");
    assert!(!ok && text.contains("app_nil       its proof does not check") && text.contains("app_small     not checked"), "{}", text);
    // a proof file Bend rejects before any law
    let (ok, text) = run("def app_nil_left(xs):\n  match xs:\n    case Nil{}:\n      match xs:\n        case Nil{}:\n          {==}\n");
    assert!(!ok && !text.contains("proven"), "{}", text);
}

#[test]
fn property_tests_build() {
    // a constructor over another declared type, a binding completed by a
    // loop the test program drops, and lists that repeat an element
    let sources = [
        "type O\n    A\n    B\ntype E\n    N(v: int)\n    Bn(o: O, l: E, r: E)\ndef size(e)\n    match e\n        N(_) => 1\n        Bn(_, l, r) => 1 + size(l) + size(r)\nlaw size_positive\n    for e: E\n    size(e) >= 1\n",
        "var xs = []\nfor i in [1, 2]\n    xs.push({size: i})\nprint(sum(xs *> $.size))\ndef twice(n)\n    n * 2\nlaw twice_even\n    for n: int\n    twice(n) % 2 == 0\n",
    ];
    for src in sources {
        fire_bend::compile_tests(src).unwrap_or_else(|d| panic!("{:?}", d));
    }
    // a false law that only a repeated element breaks is caught
    let src = "def increasing(xs: [int])\n    for i in 1..len(xs)\n        if xs[i - 1] >= xs[i] do return false\n    true\nlaw sorted_is_strict\n    for xs: [int]\n    increasing(sorted(xs))\n";
    let tests = fire_bend::compile_tests(src).unwrap();
    if std::env::var("BEND_TESTS").unwrap_or_default() == "skip" || !bend_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("fire-dup-tests-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("dups.bend");
    std::fs::write(&file, &tests).unwrap();
    let run = Command::new("bend").arg(&file).env("BEND_NO_TELEMETRY", "1").output().unwrap();
    let out = String::from_utf8_lossy(&run.stdout);
    assert!(out.contains("law sorted_is_strict: FAILS"), "{}", out);
}

#[test]
fn check_lists_partial_matches() {
    let source = std::fs::read_to_string(repo().join("tests/cases/match_coverage_through_maybe.fire")).unwrap();
    let (_, report) = fire_bend::compile_for_check(&source).unwrap();
    // `partial` leaves out `Minus`; `name` covers every case
    assert_eq!(report.partial_matches, vec![(18, "Minus".to_string())]);
    // each partial match comes with a value no arm accepts
    let src = "type Tree\n    Leaf\n    Node(left: Tree, value: int, right: Tree)\ndef t(x)\n    match x\n        Leaf => 0\n        Node(Leaf, v, Leaf) => v\ndef n(k)\n    match k\n        0 => 1\n        1 => 2\ndef l(xs: [int])\n    match xs\n        [] => 0\n        [a, b, ...r] => a\ndef r(p)\n    match p\n        {x: 0, y} => y\n        {x, y: 0} => x\n";
    let (_, report) = fire_bend::compile_for_check(src).unwrap();
    let missed: Vec<&str> = report.partial_matches.iter().map(|(_, m)| m.as_str()).collect();
    assert_eq!(missed, vec!["Node(Node(_, _, _), _, _)", "2", "[_]", "{x: 1, y: 1}"]);
}
