// src/prune.rs
// Keep only the prelude items a program reaches. The prelude is ~1500 lines
// and Bend checks (and clang compiles) all of it on every build; a typical
// program uses a few dozen of its defs.

use std::collections::{HashMap, HashSet};

/// One top-level item of the prelude: a `def` or `type` with the comment
/// lines above it (and its `@unsafe` marker).
struct Block {
    /// Line range in the prelude.
    lines: std::ops::Range<usize>,
    /// The names it declares: the def, or the type and its constructors.
    provides: Vec<String>,
    /// The names its body mentions.
    refs: HashSet<String>,
}

/// The prelude reduced to the blocks `program` (the generated Bend source
/// after the prelude) uses, directly or through other prelude blocks.
pub fn prune_prelude(prelude: &str, program: &str) -> String {
    let lines: Vec<&str> = prelude.lines().collect();
    let blocks = split_blocks(&lines);
    let mut owner: HashMap<&str, usize> = HashMap::new();
    for (i, b) in blocks.iter().enumerate() {
        for name in &b.provides {
            owner.insert(name.as_str(), i);
        }
    }
    // reachability from the program's own text
    let mut keep = vec![false; blocks.len()];
    let mut work: Vec<usize> = Vec::new();
    for tok in tokens(program) {
        if let Some(&i) = owner.get(tok)
            && !keep[i] {
                keep[i] = true;
                work.push(i);
            }
    }
    while let Some(i) = work.pop() {
        for r in &blocks[i].refs {
            if let Some(&j) = owner.get(r.as_str())
                && !keep[j] {
                    keep[j] = true;
                    work.push(j);
                }
        }
    }
    let header_end = blocks.first().map(|b| b.lines.start).unwrap_or(lines.len());
    let mut out = String::new();
    for l in &lines[..header_end] {
        out.push_str(l);
        out.push('\n');
    }
    for (i, b) in blocks.iter().enumerate() {
        if keep[i] {
            for l in &lines[b.lines.clone()] {
                out.push_str(l);
                out.push('\n');
            }
        }
    }
    out
}

fn is_start(line: &str) -> bool {
    line.starts_with("def ") || line.starts_with("type ") || line.starts_with("@unsafe")
}

/// The blocks of the prelude in order. A block starts at the first comment
/// line above its `def`/`type`/`@unsafe` line and runs to the next block.
fn split_blocks(lines: &[&str]) -> Vec<Block> {
    let mut starts: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if is_start(lines[i]) {
            // the comments (and blank lines) above belong to this block
            let mut s = i;
            while s > 0 && (lines[s - 1].is_empty() || lines[s - 1].starts_with('#')) {
                s -= 1;
            }
            if let Some(&prev) = starts.last() {
                s = s.max(prev + 1);
            }
            starts.push(s);
            if lines[i].starts_with("@unsafe") {
                i += 1; // the def line is part of this block
            }
        }
        i += 1;
    }
    // the file header (comments before the first item) is not a block
    let mut blocks = Vec::new();
    for (k, &s) in starts.iter().enumerate() {
        let end = starts.get(k + 1).copied().unwrap_or(lines.len());
        let body = &lines[s..end];
        let head = body.iter().find(|l| l.starts_with("def ") || l.starts_with("type ")).copied().unwrap_or("");
        let name = head
            .trim_start_matches("def ")
            .trim_start_matches("type ")
            .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
            .next()
            .unwrap_or("")
            .to_string();
        let mut provides = vec![name.clone()];
        let mut refs = HashSet::new();
        for l in body {
            if l.trim_start().starts_with('#') {
                continue;
            }
            for t in tokens(l) {
                if head.starts_with("type ") && t.starts_with(&format!("{}.", name)) {
                    provides.push(t.to_string());
                }
                refs.insert(t.to_string());
            }
        }
        blocks.push(Block { lines: s..end, provides, refs });
    }
    blocks
}

/// The identifier-like tokens of some Bend source (`F.list.push`,
/// `U32`, `xs`), skipping comment lines.
fn tokens(text: &str) -> impl Iterator<Item = &str> {
    text.lines().filter(|l| !l.trim_start().starts_with('#')).flat_map(|l| {
        l.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
            .filter(|t| t.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_'))
            .map(|t| t.trim_end_matches('.'))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRELUDE: &str = "# header\n\ntype F.Pair<-A: Data> is Data:\n  F.Pair.mk{key: A}\n\ndef F.fst(p: F.Pair<U32>) -> U32:\n  match p:\n    case F.Pair.mk{key}:\n      key\n\n# a helper nobody calls\ndef F.unused() -> U32:\n  F.fst(F.Pair.mk{key: 1})\n\n@unsafe\ndef F.loop(n: U32) -> U32:\n  F.loop(n)\n";

    #[test]
    fn keeps_what_the_program_reaches() {
        let out = prune_prelude(PRELUDE, "def main() -> U32:\n  F.fst(F.Pair.mk{key: 2})\n");
        assert!(out.starts_with("# header\n"));
        assert!(out.contains("type F.Pair"));
        assert!(out.contains("def F.fst"));
        assert!(!out.contains("F.unused"));
        assert!(!out.contains("F.loop"));
    }

    #[test]
    fn a_constructor_pulls_in_its_type() {
        let out = prune_prelude(PRELUDE, "x = F.Pair.mk{key: 1}\n");
        assert!(out.contains("type F.Pair"));
        assert!(!out.contains("def F.fst"));
    }

    #[test]
    fn unsafe_marker_stays_with_its_def() {
        let out = prune_prelude(PRELUDE, "F.loop(1)\n");
        assert!(out.contains("@unsafe\ndef F.loop"));
    }
}
