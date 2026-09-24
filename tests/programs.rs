// tests/programs.rs
// Every program under examples/ and tests/cases/ compiles to Bend and, when
// `bend` runs (see tests/common), builds, runs and prints its `<name>.out`.
// The other tests cover diagnostics, laws and `fire --check`.

mod common;

use std::path::Path;
use std::process::Command;

/// Compile, and when `bend` runs, build and run: the program's output.
fn compile_and_run(path: &Path) -> Option<String> {
    let source = std::fs::read_to_string(path).unwrap();
    let bend_source = fire_bend::compile(&source).unwrap_or_else(|diags| {
        let msgs: Vec<String> = diags.iter().map(|d| d.to_string()).collect();
        panic!("{}: compilation failed:\n{}", path.display(), msgs.join("\n"))
    });
    if !common::use_bend() {
        return None;
    }
    let dir = common::scratch("programs");
    let stem = path.file_stem().unwrap().to_str().unwrap();
    let src = common::write(&dir, &format!("{}.bend", stem), &bend_source);
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

fn check_goldens(dir: &str) {
    for path in common::files(dir, "fire") {
        let golden = std::fs::read_to_string(path.with_extension("out"))
            .unwrap_or_else(|_| panic!("{}: missing golden", path.display()));
        if let Some(got) = compile_and_run(&path) {
            assert_eq!(got, golden, "{}: output differs from the golden", path.display());
        }
    }
}

#[test]
fn examples() {
    check_goldens("examples");
}

#[test]
fn cases() {
    check_goldens("tests/cases");
}

#[test]
fn unsupported_programs_are_rejected_with_a_message() {
    let cases: &[(&str, &str)] = &[
        ("x = 1\nx = 'a'\n", "reassign"),
        ("xs = [1, 'a']\n", "mixes int and str"),
        ("\"{h}:{m}\" = \"1:2\"\n", "invalid assignment target"),
        // a helper a method uses is a method: it cannot run before the object exists
        ("def G\n    def h(x)\n        x\n    x = h(1)\n    public p = () => h(x)\nprint(G().p())\n", "while the object is being built"),
        ("x = 1.5 & 2.5\n", "expected int, found float"),
        ("def f(n: int)\n    n + 0.5\n", "convert with `float(x)`"),
        // habits from Python get a hint
        ("xs = [1]\nprint(2 in xs)\n", "`xs.contains(x)`"),
        ("xs = [1]\nif 2 not in xs do print(1)\n", "`not xs.contains(x)`"),
        ("xs: [int, str] = [1]\n", "one element type"),
        // entries are {key, value} records, and a comma in `for` means lockstep
        ("d = {}\nd['a'] = 1\nfor k, v in d\n    print(k)\n", "a comma in `for` goes through several iterables in lockstep"),
        ("d = {}\nd['a'] = 1\nfor [k, v] in d.entries()\n    print(k)\n", "take it apart with `{key, value}`"),
        ("d = {}\nd['a'] = 1\nprint(sorted(d.entries(), ([k, v]) => v))\n", "take it apart with `{key, value}`"),
        ("d = {}\nd['a'] = 1\nprint(d.entries()[0][1])\n", "read its fields, `.key` and `.value`"),
        ("print([1, 2].zip([3, 4]))\n", "`for x, y in xs, ys`"),
        ("print([1, 2].enumerate())\n", "`for i, x in 0.., xs`"),
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
        // a change nothing reads: values are copied, so it reaches nothing
        ("def P(public var x = 0)\n    public var y = 0\nvar ps = [P(1)]\nfor p in ps\n    p.x = 10\nprint(ps)\n", "the loop's copy of an element"),
        ("def P(public var x = 0)\n    public var y = 0\ndef bump(q)\n    q.x += 1\nvar r = P()\nbump(r)\nprint(r)\n", "a copy of what the caller passed"),
        ("def fill(xs)\n    xs.push(1)\nprint(fill([]))\n", "a copy of what the caller passed"),
        ("var a = [1]\nb = a\nb.push(2)\nprint(a)\n", "nothing reads 'b' afterwards"),
        // a change in the right side of `or` runs only when that side does,
        // which needs to know whether `or` is logical or a default
        ("def pick(a, xs)\n    var ys = xs\n    r = a or ys.pop()\n    {r, ys}\nprint(pick(true, [false]))\n", "a call that changes `ys` cannot sit in the right side of `or`"),
        // a `while` condition runs on every pass, not once before the loop
        ("unsafe def f()\n    var xs = [1, 2]\n    while len(xs) > 0 and xs.pop() > 0 do print(xs)\nf()\n", "a call that changes `xs` cannot sit in a `while` condition"),
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
    let source = std::fs::read_to_string(common::repo().join("examples/basics.fire")).unwrap();
    let a = fire_bend::compile(&source).unwrap();
    let b = fire_bend::compile(&source).unwrap();
    assert_eq!(a, b);
    assert!(a.starts_with("import Base\n"));
    assert!(a.contains("def main() -> IO(Unit):"));
}

#[test]
fn branches_and_self_calls_take_their_fast_forms() {
    let image = |path: &str| fire_bend::compile(&std::fs::read_to_string(common::repo().join(path)).unwrap()).unwrap();
    let def = |src: &str, name: &str| -> String {
        let at = src.find(&format!("\ndef {}(", name)).unwrap_or_else(|| panic!("no def {}", name));
        src[at + 1..].split("\n\n").next().unwrap().to_string()
    };
    // an opening branch on parameters is a match on a condition parameter
    let s = image("tests/cases/branch_on_parameters_in_int_recursion.fire");
    for f in ["fib", "fib2", "steps", "both", "via_call", "rep", "nested_arg", "pick", "countdown"] {
        let go = def(&s, &format!("{}.F.go", f));
        assert!(go.contains("match __c:"), "{}.F.go:\n{}", f, go);
        assert!(def(&s, f).contains(&format!("{}.F.go(", f)), "{} forwards to its worker", f);
    }
    // with one branch, no thunk is left (a later branch, like the guard of
    // `steps`, keeps its own form)
    for f in ["fib", "fib2", "both", "rep", "pick", "countdown"] {
        let go = def(&s, &format!("{}.F.go", f));
        assert!(!go.contains("Bool.pick(Unit ->"), "{}.F.go:\n{}", f, go);
    }
    assert!(!s.contains("not_head.F.go"), "a condition on a local stays a branch");
    // independent self-calls of a pure def run in parallel
    let s = image("tests/cases/parallel_self_calls.fire");
    for f in ["size", "total", "mirror", "depth", "show", "spread", "dependent", "rebind", "build.F.go", "mk.F.go"] {
        assert!(def(&s, f).contains("__par2"), "{} runs its self-calls in parallel:\n{}", f, def(&s, f));
    }
    assert!(def(&s, "total").contains("__par3"), "three calls at once");
    for f in ["all_pos", "lookup"] {
        assert!(!def(&s, f).contains("__par"), "{} stays sequential:\n{}", f, def(&s, f));
    }
}

#[test]
fn laws_are_classified_and_property_tested() {
    use fire_bend::core::Proof;
    let source = std::fs::read_to_string(common::repo().join("tests/cases/laws_in_a_program.fire")).unwrap();
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
    if !common::use_bend() {
        return;
    }
    let src = common::write(&common::scratch("law-tests"), "laws.bend", &tests);
    let run = common::bend(&[&src]);
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
    if !common::use_bend() {
        return;
    }
    let dir = common::scratch("proof-tests");
    let prog = common::write(&dir, "app.fire", "def app(xs, ys)\n    match xs\n        [] => ys\n        [h, ...t] => [h] + app(t, ys)\nlaw app_nil_left\n    for xs: [int]\n    app([], xs) == xs\nlaw app_small\n    app([1], [2]) == [1, 2]\nlaw app_nil\n    for xs: [int]\n    app(xs, []) == xs\nprint(app([1], [2]))\n");
    let run = |proof: &str| {
        common::write(&dir, "app.proof.bend", proof);
        let out = Command::new(env!("CARGO_BIN_EXE_fire")).arg(&prog).arg("--check").output().unwrap();
        (out.status.success(), common::text(&out))
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
    if !common::use_bend() {
        return;
    }
    let file = common::write(&common::scratch("dup-tests"), "dups.bend", &tests);
    let out = common::text(&common::bend(&[&file]));
    assert!(out.contains("law sorted_is_strict: FAILS"), "{}", out);
}

#[test]
fn check_lists_partial_matches() {
    let source = std::fs::read_to_string(common::repo().join("tests/cases/match_coverage_through_maybe.fire")).unwrap();
    let (_, report) = fire_bend::compile_for_check(&source).unwrap();
    // `partial` leaves out `Minus`; `name` covers every case
    assert_eq!(report.partial_matches, vec![(18, "Minus".to_string())]);
    // each partial match comes with a value no arm accepts
    let src = "type Tree\n    Leaf\n    Node(left: Tree, value: int, right: Tree)\ndef t(x)\n    match x\n        Leaf => 0\n        Node(Leaf, v, Leaf) => v\ndef n(k)\n    match k\n        0 => 1\n        1 => 2\ndef l(xs: [int])\n    match xs\n        [] => 0\n        [a, b, ...r] => a\ndef r(p)\n    match p\n        {x: 0, y} => y\n        {x, y: 0} => x\n";
    let (_, report) = fire_bend::compile_for_check(src).unwrap();
    let missed: Vec<&str> = report.partial_matches.iter().map(|(_, m)| m.as_str()).collect();
    assert_eq!(missed, vec!["Node(Node(_, _, _), _, _)", "2", "[_]", "{x: 1, y: 1}"]);
}
