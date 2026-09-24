// tests/shapes.rs
// The Bend programs under docs/shapes/ back docs/compiler.md: each shows one
// shape the compiler emits and is kept honest by running it through `bend`.
// A `<name>.out` is the expected output of `bend <name>.bend`; a
// `<name>.check` is text that `bend <name>.bend --check-only` must print
// (an open law reports a TODO).

mod common;

#[test]
fn shapes_check_under_bend() {
    if !common::use_bend() {
        return;
    }
    for path in common::files("docs/shapes", "bend") {
        let name = path.display().to_string();
        if let Ok(expected) = std::fs::read_to_string(path.with_extension("check")) {
            let text = common::text(&common::bend(&[name.as_str(), "--check-only"]));
            assert!(text.contains(expected.trim()), "{}: expected {:?} in bend's report:\n{}", name, expected.trim(), text);
            continue;
        }
        let golden = std::fs::read_to_string(path.with_extension("out"))
            .unwrap_or_else(|_| panic!("{}: missing .out (or .check)", name));
        assert_eq!(common::text(&common::bend(&[&name])), golden, "{}: output differs from the golden", name);
    }
}
