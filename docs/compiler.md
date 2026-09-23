# How Fire compiles to Bend

Bend 2 is a total, affine, dependently typed language whose checker proves
termination, exhaustiveness, effect discipline and user-stated laws. Fire
compiles to Bend so that a Fire program keeps those guarantees, and the
compiler follows one rule:

> **The Bend program is the program.** Every lowering step produces a form
> Bend's checker can see through. Fire does inference and sugar; Bend does
> the checking. Fire reports what Bend will find and never certifies
> anything on its own.

Three consequences shape everything below:

1. **Every construct has a total image.** The language keeps only
   constructs that have one. What is inherently partial (`while`, recursion
   with nothing to descend on) is written in an `unsafe def`, and only
   those carry Bend's `@unsafe`.
2. **Polymorphism is emitted, not expanded.** A generic def is one Bend
   def, and Bend makes the copies. Every Fire def has a stable Bend name
   that a proof can refer to.
3. **Laws are part of the language.** A `law` is stated in Fire about Fire
   names. It is a property test, an open claim in the image, and a theorem
   once a Bend proof fills it; the mechanical cases the compiler proves
   itself.

The price is small: data with alternatives or recursion is declared with
`type`, as in any ML-family language, and a def whose termination is a
real theorem says `unsafe def`. Everything else stays inferred.

Each Bend form below is backed by a small program under
[`shapes/`](shapes), which the test suite runs through `bend`
(`tests/shapes.rs`). [`language.md`](language.md) is the language
reference.

## The pipeline

```
grammar/fire.pest, src/ast.rs   parse: source → AST
src/check/                      names, types, effects, termination, laws → Core
src/core.rs                     Core: the typed, resolved program
src/lower/                      Core → Bend IR in forms Bend can certify
src/ir.rs                       the IR, its printer and the affine marks
src/prelude.bend, src/prune.rs  the runtime, pruned to what the program uses
src/testgen.rs                  laws as property tests (`--test`)
src/main.rs                     the command line
```

The output starts with `import Base`, then the part of the prelude the
program reaches, then one Bend def per Fire def, the laws, and `main`.

The one structural decision is **Core**. The checker finishes everything
that needs types (method and builtin resolution, pipelines, `$`, keyword
arguments, defaults, changing methods as functional updates, `self`,
dictionaries at call sites), and the lowering does only what Bend's shape
demands (parameter order, branch forms, loop drivers, eliminators, closure
environments, `do` blocks and `+` marks). The lowering never re-infers
anything.

## What Bend enforces

Bend's rules are what a tree-walking interpreter never sees, and each one
explains part of the lowering:

1. A `match` inspects only a parameter or a pattern variable, and only at
   the head of a def body. A match on a computed value needs a helper def.
2. Definitions precede their uses, and there is no mutual recursion.
3. A self-call must pass its arguments unchanged, left to right, until one
   is a piece of its parameter. `@unsafe` opts a def out.
4. Variables are affine. `+x` makes a value reusable; a variable handed to
   a `+` binder (a lambda parameter, a `let`) is used twice, and so is one
   used in two thunks of a `Bool.pick`.
5. Template (`~f`) arguments must be closed terms, and a def with `+`
   parameters is not accepted where a template expects plain ones, so
   prelude operations are passed eta-expanded (`~(x => F.i32.show(x))`).
6. In a `do` block every let is annotated (`x : T = v`), a reusable one is
   bound through `pure` (`+x : T <- IO.pure(T, v)`), and a bare statement
   must be a unit action.
7. There are no negative or infinite float literals (`F32.neg(0.5)`,
   `(1.0 / 0.0 : F32)`), and a predecessor pattern is `1n+p`.
8. `List<&1, T>` and `List<&2, T>` are different types; Fire uses
   `List<&2, T>` throughout.

## Checking (`src/check/`)

**Names.** Top-level and block-level defs are hoisted: declared before
their block runs, inferred on first use. Declared types and their
constructors are global. A class's members are prescanned so its methods
may refer to each other in any order.

**Inference** is Hindley-Milner with levels (`types.rs`) and qualified
types. An operation whose meaning depends on a type not known yet raises a
*constraint*: equality, ordering, showing, an arithmetic operator, `or`,
length, iteration, indexing, index assignment, a field, a method, a
conversion. A constraint is solved once its subject's type is known: by a
builtin operation (with sub-constraints for the parts: showing a list needs
showing its elements), by a class method, or by a field path through
adopted parents. At generalization, a constraint left on a quantified
variable becomes a *dictionary* of the def's scheme. A variable nothing
fixed gets the first default (int, list, str, float) that satisfies its
constraints.

**Desugaring** happens here, so Core has no sugar: pipelines and `$`,
keyword arguments and defaults, interpolation, `x or d`, changing methods
(the call rebinds its receiver, and the method returns the rebuilt object
along with its value), `self` and members as locals, adoption,
destructuring, and returns (the values a body returns are joined, and
`nothing` on some paths lifts the others into `T | nothing`). A bound value
with a branch that leaves (`n = match x` with `{err} => return e`) becomes
a statement `match` whose other branches bind `n`.

**Effects** (IO, abort) are a fixpoint over calls, closure sets and
constraints solved to methods. A dictionary of a fallible operation
(indexing, a method, a conversion) makes its def fallible.

**Termination** (`descent.rs`) finds an argument for every def that calls
itself:

* *structural*: a sequence of parameters such that every self-call passes
  a prefix unchanged and the next one smaller (a variable bound by a match
  on it, at any depth);
* *fuel*: an int parameter that every self-call decreases by a literal,
  under guards that keep it at least the decrement;
* otherwise an error naming the rule, unless the def is `unsafe def`.

A self-call inside a loop body, a def passing itself as a value, a cycle of
calls between defs, `while` outside an unsafe def and a `for` over an open
range alone are errors.

**Coverage** (`core.rs`) is the usefulness check over a matrix of pattern
rows: a list pattern is nil and cons cells, `bool` and `nothing` are
constructors, other literals never cover their type, and a guarded arm may
always decline. A match that misses a value makes its def fallible, and
`fire --check` reports a value it misses.

**Lost changes** (`lost.rs`). A statement whose only effect is to change a
binding (`p.x = v`, `xs.push(v)`, a changing method) is an error when a
backward liveness walk finds that nothing reads the binding afterwards.

**Laws** (`laws.rs`) are checked in a frame of their own: the variables are
declared with their types, then the hypothesis and the claim are checked
as expressions. A law is *closed* (no variables), *finite* (every variable
of `bool` or of a type of nullary constructors, and no hypothesis) or
*open*. A law that reaches an IO def, unsafe code or a top-level value is
rejected.

## Core (`src/core.rs`)

Every def with its kind (plain, lambda, class, method, main, law), the unit
whose type parameters it shares (itself for a top-level def), parameters,
captures, scheme, effect, termination argument and a body of statements.
Every expression is typed; method calls, builtins and operators are
resolved to calls, dictionaries, fields or builtins. The data types are the
declared ones, records, classes, and the builtins (`T | nothing`, results,
dictionary entries, ranges).

## The Bend image (`src/lower/`)

`mod.rs` holds the driver, names, types, def images, closures, derived
defs and dictionaries; `body.rs` statements, branches, matches and loops;
`expr.rs` expressions and builtins; `laws.rs` laws.

### Names

User names are emitted verbatim: the Fire def `insert` is the Bend def
`insert`, `type Tree` is `Tree`, a method `push` of a class `Stack` is
`Stack.push`. A name that collides with Base gets a trailing underscore.
The compiler's own defs live under `F.` (the prelude) or an `F` segment of
their owner (`insert.F.if3`, `Tree.F.show`, `Stack.F.new`,
`main.F.loop5`). No Fire name contains a dot, so a proof can say `insert`
and mean it. A lambda is `outer.fn2`, a nested def `outer.inner`.

### Types

`int` is `U32` with signed arithmetic in the prelude, `float` is `F32`, and
lists, maps, `T | nothing` and results are Base's. A declared type is `type
Tree<-A: Data> is Data:` with a line per constructor
([`01`](shapes/01_data_and_recursion.bend)); a class is a `Data` type with
one constructor and a def per method taking the object first; a record
shape is a generated type named after its fields (`F.Rec.memo_value`). A
type's parameters are the variables its fields actually mention.

### Defs and generics

A Fire def is one Bend def, and its type parameters are emitted:

* a type the body leaves free is an erased argument (`def size(-A: Data,
  t: Tree<A>)`, [`01`](shapes/01_data_and_recursion.bend));
* an operation the body needs on a generic type (comparing, showing,
  adding, indexing) is a template parameter (`def insert(~A: Data, ~lt: A
  -> A -> Bool, +x: A, t: Tree<A>)`, [`02`](shapes/02_generic_interfaces.bend)).
  A call site passes the operation for its type (`~U32.is_lt`,
  `~Point.lt`); a generic caller forwards its own.

This is dictionary passing with Bend templates as the dictionaries. At a
call, each dictionary is a closed term: the caller's own dictionary
parameter, a derived operation (`Tree.F.show` applied to its parameters'
operations, `F.list.eq`), a prelude primitive, a class method, or a field
accessor path.

A function-typed parameter that the body only calls or passes on is also a
template: the function's code (`~f: E -> A -> B`) plus its environment as
data (`+env: E`). That is how the prelude's `map` and every loop driver
work.

**Parameter order.** Bend reads a self-call's arguments left to right, so
the parameters a structural def descends on come first, in the order the
termination argument found (`merge(xs, b)` shrinks `a`, `merge(a, ys)`
keeps `a` and shrinks `b`; [`09`](shapes/09_open_law.bend)).

### Closures

A lambda is a top-level def taking its environment record first. A
function value is its environment, or, when several lambdas can flow to
the same place, a sum `F.FnN` over their environments with a `.call` def
that dispatches. Bend closures are affine, so this defunctionalization is
what makes a Fire function callable any number of times.

### Branches

Bend has no `if`, and a `match` may inspect only a parameter. Four forms
cover every branch, chosen by what it contains:

| branch | form | shape |
|---|---|---|
| an expression `if` with cheap, pure operands | `Bool.pick(T, c, a, b)`, eager | [`04`](shapes/04_loops_io.bend) |
| no self-call and no early exit | a helper def that matches the condition and answers the branch's value, or its live-out variables in an `F.OutN` record | [`07`](shapes/07_statement_branches.bend) |
| a self-call, or inside a term | `Bool.pick` over thunks, applied to `Unit{}` | [`01`](shapes/01_data_and_recursion.bend), [`05`](shapes/05_branches_in_effects.bend) |
| `return`, `break` or `continue` | the rest of the block moves into the branches that fall through | [`05`](shapes/05_branches_in_effects.bend) |

The helper def keeps a body straight-line and cheap; thunks keep a
recursive def structural, since no helper has to call back into it. A
thunk costs about 20 ns per branch (see below), which is why it is used
only where a helper cannot be.

### Matches

A match on a parameter, or a piece of one, in a structural def is a real
Bend `match`, which is what the termination checker reads. Any other match
goes through a helper def that takes the subject as a parameter, or,
inside a term, through a case eliminator per type (`F.list.case`,
`F.maybe.case`, `Tree.F.case`) with a thunk per constructor
([`06`](shapes/06_match_on_computed.bend)).

Rows of patterns compile column by column: constructors (including list
shapes, `T | nothing` and results) split on the constructor, literals
become a chain of equality tests, and guards are tested at the leaf with
the remaining rows as the fallback. An empty set of rows aborts in a
fallible def; in a pure def coverage proved it unreachable, and any value
of the type fills it.

### Loops

A `for` over finite data is a fold with early exit
([`03`](shapes/03_loops.bend)). The body becomes a def `E -> S -> A ->
F.Ctl<S, R>` over the environment it reads, the state it assigns and the
element, answering `F.Next{s}`, `F.Break{s}` or `F.Return{r}`. A driver
folds it: `F.for_list` recurses on the list, `F.for_range` counts a `Nat`
down, and their `_res` and `_io` variants do the same inside a `do` block
([`04`](shapes/04_loops_io.bend)). Iterables in lockstep are zipped first.

`while` has nothing to descend on. Its driver, `F.loop`, checks the
condition inside the body so that the loop is one def, and that def is
`@unsafe` ([`10`](shapes/10_while_loop.bend)). Bend's own report then
lists exactly the unsafe defs and their callers.

### Int recursion

Fire's `int` is a `U32`, which has no structure to recurse on. A def that
counts an int down gets a leading `fuel: Nat` parameter. Outside callers
start it at `n + 1` (`F.i32.fuel(n)`), and every self-call passes the
predecessor. The fuel always outlasts the int, so the `0n` case is dead;
Bend still needs a value there, and the compiler builds one of the result
type. Used as a value (`xs *> fib`), such a def goes through a forwarder
`fib.F.value` that starts the fuel.

### Effects and failures

An IO def's body is a `do IO<T>` block, a fallible def's a `do
Result<&2, &2, String, T>` block ([`05`](shapes/05_branches_in_effects.bend)).
The abort is unwrapped once, at the IO boundary. Where an operation fails
by itself (an index, a conversion, an unwrap, `assert`, `error`), its
message is prefixed with its line (`F.at("line N: ", r)`).

### Laws

A law compiles to a Bend `law`:

```python
law insert_keeps_sorted:
  for +x: U32
  for xs: List<&2, U32>
  for h: {sorted(xs) == True{} : Bool}
  {sorted(insert(x, xs)) == True{} : Bool}
```

A hypothesis is an extra parameter of equality type; `where` would make the
variable a dependent pair that the claim would have to project
([`09`](shapes/09_open_law.bend)). A type parameter the law leaves open is
`U32`: over `Unit` every value is equal, and a proof would say nothing.

A closed law gets `def name(): {==}`, which Bend proves by computing both
sides; a finite law gets a case split closed with `{==}` in each case
([`08`](shapes/08_finite_law.bend)). Both are in every image, so a false
one fails the build. An open law is emitted without a proof, and only in
the image `fire --check` hands to `bend --check-only`, which reports it as
a TODO; a runnable image leaves it out. A proof lives in
`<program>.proof.bend` as a def named after the law, and `fire --check`
appends that file.

### Affinity

After lowering, every def is marked: parameters, lets, binds, pattern
fields and lambda parameters used more than once get `+`, counting a use
in each thunk and each argument handed to a `+` binder.

## The prelude (`src/prelude.bend`)

The runtime is plain Bend: loop drivers, eliminators, signed arithmetic,
number formatting and parsing, strings, lists and maps. Bend has no forward
references, so its defs are ordered callee first;
`tools/prelude_sort.py` restores that order after an edit. `prune.rs`
keeps only the items a program reaches.

## The command line (`src/main.rs`)

| command | what it does |
|---|---|
| `fire p.fire` | compile, build with `bend`, run |
| `fire p.fire -o out.bend` | write the Bend source |
| `fire p.fire -o p` / `-o p.js` | build a native binary, or JavaScript for node |
| `fire p.fire --types` | every def's type, effects, termination argument and needs |
| `fire p.fire --check` | run `bend --check-only` on the image with every law (and `p.proof.bend`); report laws, unsafe code, and matches that miss values |
| `fire p.fire --test` | build and run the property-test image (`testgen.rs`) |
| `fire p.fire --total` | reject a program with any `unsafe def` |

A law Bend rejects is reported as the law, with the two sides Bend
computed; a failing def of the proof file is reported as that law's proof.
Once Bend rejects the image, no law is reported proven.

## Measurements

Native binaries, one run each; the loop bodies are a xorshift step so clang
cannot turn the loop into a formula.

| what | time |
|---|---|
| 100 M iterations, `Nat` countdown (total) | 0.205 s |
| 100 M iterations, `@unsafe` U32 loop | 0.204 s |
| 100 M iterations with a branch as a helper def | 0.35 s |
| 100 M iterations with a branch as `Bool.pick` thunks | 2.3 s |
| `bend --check-only` on a closed law sorting 60 elements | 0.28 s |

A `Nat` counter is free, which makes `for` over a range total at no cost; a
thunk branch costs about 20 ns; closed laws are cheap enough to check on
every build.

## Limits

* **Mutual recursion** is unsupported: Bend has none, and a dispatcher
  encoding would be unsafe by construction. Merging the defs into one keeps
  them total.
* **Real theorems need `unsafe def`**: `quicksort` on filtered lists,
  `gcd`, Newton's iteration. `--total` turns the opt-out into an error.
* **Proofs beyond the mechanical cases are written in Bend.** Fire does not
  have dependent types and is not a prover.
* **Compile time** grows with the program: closed laws are computed on every
  build, and Bend copies templates per instantiation.

Directions worth taking: attempting the obvious structural induction
before reporting a law open; turning an `assert` over parameters into a law
whose proof erases the check; and a lint for expensive implicit copies.
