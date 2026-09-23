# How the compiler works

Pipeline: parse (`grammar/fire.pest` → `src/ast.rs`) → check (`src/check/`,
producing Core, `src/core.rs`) → lower (`src/lower/`, producing Bend IR,
`src/ir.rs`) → print, with the part of the runtime prelude
(`src/prelude.bend`) the program reaches (`src/prune.rs`). The output
starts with `import Base`, then the prelude, then one Bend def per Fire
def, the laws, and `main`. `docs/design.md` says why the image has the
shape it has; this file says how the code produces it.

## What Bend enforces

Bend 2 is a typed, affine, total language, and the lowering has to respect
rules a tree-walking interpreter never sees. Each is backed by a program
under `docs/design/` or found by experiment with Bend 2.0.25:

1. A `match` only inspects a parameter or a variable bound by a pattern,
   and only at the head of a def body (no `let` before it). A match on a
   computed value goes through an eliminator def.
2. Definitions precede their uses; there is no mutual recursion.
3. Termination: a self-call must pass its arguments unchanged, left to
   right, until one is a piece of its parameter. `@unsafe` opts a def out.
4. Variables are affine. `+x` makes a Data value reusable; a variable
   handed to a `+` binder (a lambda parameter, a `let`) is itself used
   twice, and a variable used in two thunks of a `Bool.pick` is too.
5. Template (`~f`) arguments must be closed terms; a def with `+`
   parameters is not accepted where a template expects plain ones, so
   prelude operations are passed eta-expanded (`~(x => F.i32.show(x))`).
6. In a `do` block every let is annotated (`x : T = v`); a reusable one is
   a bind through `pure` (`+x : T <- IO.pure(T, v)`); a bare statement must
   be a unit action.
7. Literals: no negative or infinite float literals (`F32.neg(0.5)`,
   `(1.0 / 0.0 : F32)`), and a predecessor pattern is `1n+p` or `1n++p`.
8. `List<&1, T>` and `List<&2, T>` are different types; the compiler uses
   `List<&2, T>` throughout.

## Checking (`src/check/`)

**Names.** Top-level and block-level defs are hoisted (declared before
their block runs, inferred on first use). Declared types and their
constructors are global. A class's members and methods are prescanned so
that methods may refer to each other in any order.

**Inference** is Hindley-Milner with levels (`types.rs`) and qualified
types. An operation whose meaning depends on a type not known yet raises a
*constraint* (`Class`: equality, ordering, show, one arithmetic operator,
`or`, length, iteration, indexing, index assignment, a field, a method, a
conversion, the zero of a sum). A constraint is solved when its subject's
type is known: concretely (a builtin operation, with sub-constraints for
the parts: showing a list needs showing its elements), by a class method
(recording the method's instantiation: type arguments and dictionaries),
or by a field path (through adopted parents). At generalization, an
unsolved constraint on a quantified variable becomes a *dictionary* of the
def's scheme; two for the same operation on the same subject merge. At the
end, a variable nothing fixed gets the first default (int, list, str,
float) that satisfies every constraint on it.

**Desugaring** happens here, so Core has no sugar: pipelines and `$`,
keyword arguments and defaults, f-strings (with numbers aligned right),
`x or d`, mutating methods (a call rebinds its receiver path; the method
returns the rebuilt object, and its value when it has one), `self` and
members as locals, adoption, destructuring, and returns: the values a body
returns are joined, and `nothing` on some paths lifts the others into
`T | nothing`. A bound value with a branch that leaves (`n = match x` with
`{err} => return e`, or `continue`) becomes a statement `match` whose other
branches bind `n` (`lift_exits`); the lowering moves the rest of the block
into them, as for any branch that leaves.

**Effects** (IO, abort) are a fixpoint over calls, closure sets and
constraints solved to methods, each constraint attributed to the def whose
body performs it. A dictionary of a fallible class (indexing, a method, a
conversion) makes the def fallible, since its implementation may abort.

**Descent** (`descent.rs`) finds, for every def that calls itself, a
termination argument:

* *structural*: a sequence of parameters such that every self-call passes
  a prefix unchanged and the next one smaller (a variable bound by a match
  on it, at any depth);
* *fuel*: an int parameter every self-call decreases by a literal (`n - k`,
  or `n / k` with k ≥ 2), under facts from guards (`if n <= 1 do return`)
  that keep it at least the decrement;
* otherwise an error naming the rule, unless the def is `unsafe def`.

A self-call inside a loop body is an error (the body is a def of its own),
as is a def passing itself as a function value (`kids *> depth` inside
`depth`), and a cycle of calls between defs. `while` outside an unsafe def
is an error, and so is a `for` over an open range alone.

**Coverage** (`core.rs`) is the usefulness check over a matrix of pattern
rows: a list pattern is nil and cons cells, `bool` and `nothing` are
constructors, other literals never cover their type, and an arm with a
guard may always decline. A match that misses a value makes its def
fallible, and the check names a value it misses for `fire --check`.

**Lost changes** (`lost.rs`). A statement whose only effect is to change a
binding (`p.x = v`, `xs[i] = v`, `xs.push(v)`, a method answering nothing)
is noted where it rebinds the binding. A backward liveness walk over each
body (loops to a fixpoint, their variables new each turn) reports such a
change when nothing reads the binding afterwards: a loop's copy of an
element, a parameter, or any other copy.

**Laws** are checked in a frame of their own inside the program's scope:
the variables are declared with their annotated types, the hypothesis and
the claim are checked as expressions. A law is *closed* (no variables),
*finite* (every variable of `bool` or of a type with only nullary
constructors, no hypothesis) or *open*. After effects are known, a law
that mentions an IO def or unsafe code is rejected, and so is one that
reads a top-level value.

## Core (`src/core.rs`)

Every def with its kind (plain, lambda, constructor, method, main, law),
the unit whose type parameters it shares (itself for a top-level def),
parameters, captures, scheme, effect, descent and a body of statements;
every expression typed; method calls, builtins and operators resolved to
calls, dictionaries (`Dict`), fields or builtins; data types (declared,
records, classes, and the builtins `T | nothing`, results, pairs, ranges).

## Lowering (`src/lower/`)

`mod.rs` holds the driver, names, types, def images, closures, derived defs
and dictionaries; `body.rs` statements, branches, matches and loops;
`expr.rs` expressions and builtins; `laws.rs` laws.

**Images.** Each def gets an image: its Bend name, its type parameters
(erased `-A` when nothing needs them at compile time, template `~A`
otherwise: a unit whose lowered image still passes an erased one as a
template argument, a loop driver's state type say, is lowered again with
template parameters, and so are its callers when that reaches them), its
dictionary parameters (`~lt_0: A -> A -> Bool`), how each
function-typed parameter is passed (code as a template `~f` plus an
environment value, when the body only calls it or passes it on; a closure
value otherwise), an environment record parameter for a def with
captures, a leading `fuel: Nat` for a fuel def, the parameter order (the
structural ones first), and its mode (pure, `Result`, `IO`). Lambdas and
nested defs forward their unit's template parameters.

**Names.** User names are verbatim; a clash with Base gets `_`.
Generated members live under an `F` segment of their owner:
`Tree.F.show`, `Tree.F.case`, `Stack.F.get_items`, `Stack.F.new`,
`insert.F.if3`, `main.F.loop5`. Lambdas are `outer.fn2`.

**Types.** `int` is `U32` (signed arithmetic in the prelude), `float` is
`F32`, lists, maps, `T | nothing` and results are Base's. A declared type
or class is a Bend `Data` type over its *effective* parameters (the
variables its fields actually mention). A record shape is `F.Rec.<fields>`.
A function type is its closure representation: the environment record of
the one lambda that can flow there, or a sum `F.FnN` over several with a
`.call` def that dispatches.

**Branches.** An expression `if` with cheap operands is an eager
`Bool.pick`. A statement branch without a self-call becomes a helper def
matching its condition and answering the branch's live-out variables
(packed into `F.OutN`). A branch under a self-call, or inside a term, is
`Bool.pick` over thunks. A branch with `return`, `break` or `continue`
takes the rest of the block into the branches that fall through.

**Matches.** A match on a parameter (or a piece of one) in a structural def
is a real Bend match; any other goes through a helper def that takes the
subject as a parameter, or, inside a term, through eliminators
(`F.list.case`, `F.maybe.case`, `Tree.F.case`) with a thunk per
constructor. Rows of patterns compile column by column: constructors
(including list shapes, `T | nothing` and results) split on the
constructor, literals become a chain of equality picks with every row that
accepts the literal, guards are tested at the leaf with the remaining rows
as the fallback. An empty set of rows aborts in a fallible def (with the
match's line); in a pure def the checker proved it unreachable, and any
value of the type fills it.

**Failures.** Where an operation can fail by itself (an index, a
conversion, an unwrap, `assert`, `error`), its failure is wrapped by
`F.at("line N: ", r)` or its message is prefixed, so the message names the
line it happened at. A failure passing through calls is not wrapped again.

**Loops.** The body of a `for` becomes a def
`E -> S -> A -> F.Ctl<S, R>`: the environment (what it reads), the state
(what it assigns), the element; it answers `F.Next{s}`, `F.Break{s}` or
`F.Return{r}` with `r` the def's own result, whatever the nesting. A
driver folds it: `F.for_list` over a list, `F.for_range` counting a `Nat`
down over a range, the `_res` and `_io` variants in effectful defs, and
`F.loop` (`@unsafe`) for `while` in unsafe defs. Zipped iterables are
zipped into pairs first; an open range becomes `enumerate_from`.

**Fuel.** A fuel def matches `fuel` first: `0n` answers a value of the
result type (built in place; a generic part comes from a parameter of that
type), `1n+fuel_` runs the body, whose self-calls pass `fuel_`. Outside
callers pass `F.i32.fuel(n)`, which is `n + 1`. Used as a value (`xs *>
fact`, stored in a list), a fuel def is called through a forwarder
`fact.F.value(n)` that starts the fuel: a template's code is inlined where
it is called, so it may use each argument only once.

**Dictionaries.** At a call, each dictionary of the callee is a closed
term: the caller's own dictionary parameter when the subject stayed
generic, a derived operation (`Tree.F.show` applied to its parameters'
operations, `F.list.eq`, a prelude primitive), a class method, or a field
accessor path. Strings inside containers show quoted (`['a']`,
`Full('gift')`); `T | nothing` shows as its value.

**Laws** are printed as Bend laws (`for` parameters, hypotheses as
equality parameters, the claim as an equation), with `def name(): {==}` for
a closed law and a case split for a finite one. A type parameter a law
leaves open is `int` (`for t: Tree` is `Tree<U32>`), as `fire --test`
samples it. A runnable image carries only these; `fire --check`'s image
also carries the open ones.

**Affinity.** After lowering, every def is marked: parameters, lets, binds,
pattern fields and lambda parameters used more than once get `+`,
counting a use in each thunk and each argument handed to a `+` binder.

## The command line (`src/main.rs`)

| command | what it does |
|---|---|
| `fire p.fire` | compile, build with `bend`, run |
| `fire p.fire -o out.bend` / `-o bin` / `-o out.js` | write the source, or build |
| `fire p.fire --types` | every def's type, effects, termination argument and needs |
| `fire p.fire --check` | run `bend --check-only` on the image with every law (and `p.proof.bend` appended when it exists); report proven, open and false laws, unsafe code, and matches that cover only some values |
| `fire p.fire --test` | compile the property-test image (`src/testgen.rs`): the program's types, defs and bindings, one predicate def per law, loops over generated instances; run it |
| `fire p.fire --total` | reject a program with any `unsafe def` (combines with the others) |

A law Bend rejects is reported as the law, with the two sides Bend
computed; a failing def of the proof file is reported as that law's proof.
Once Bend rejects the image, no law is reported proven.

## Testing

`tests/programs.rs` compiles every program under `examples/` and
`tests/cases/` and, when `bend` is on `PATH`, builds and runs it against its
`.out` golden; it also checks that unsupported programs are rejected with
the right message and that laws are classified and property-tested.
`tests/design.rs` checks the images under `docs/design/`. Unit tests cover
the type store, the IR printer and prelude pruning.
