# Fire: the Bend image is the program

This is the design of Fire and the reasons for it. Fire is a Python-shaped
language where types and effects are inferred; its compiler emits programs
Bend's checker can *certify*, not merely accept. Every claim about Bend
below is backed by a program under `docs/design/`, checked by `bend` 2.0.25
in the test suite (`tests/design.rs`). `docs/language.md` is the language
reference and `docs/compiler.md` the implementation guide.

## 1. The principle

Bend 2 is a total, affine, dependently typed language with a checker that
proves termination, exhaustiveness, effect discipline and user-stated laws.
An earlier Fire compiled to Bend and inherited none of that, and not
because Fire's type system was weaker: its lowering discarded the structure
the checker needs (every loop and recursive function emitted `@unsafe`,
generic defs copied per call site, branches of recursive functions merged
into an `@unsafe` dispatcher, no way to state a law). Bend checked the
image and found nothing to certify.

The design has one rule:

> **The Bend image is the program.** Every lowering step produces a form
> Bend's checker can see through. Fire does inference and sugar; Bend does
> the checking; Fire reports what Bend will find, and never certifies
> anything on its own.

Three consequences follow, and they are the whole design:

1. **Every construct has a total image**, and the language keeps only
   constructs that have one. What is inherently partial (`while`,
   recursion with no structure to descend on) must be written inside an
   `unsafe def`, and only those carry `@unsafe`.
2. **Polymorphism is emitted, not expanded.** A generic def is one Bend
   def; Bend makes the copies. That gives every Fire def a stable Bend name
   a proof can unfold.
3. **Laws are a language feature.** `law` states a claim in Fire syntax
   about Fire names. It is a property test, an open claim in the image,
   and a theorem once a Bend proof fills it. The mechanical cases (closed
   claims, finite domains) are proven by the compiler.

What Fire gives up: `type` declarations are necessary for sum types and
recursive data. Everything else stays inferred, including generics with
constraints (§4.2). "Types are never required" became "types are required
to declare data with alternatives or recursion", which is the same trade
every ML-family language makes. Fire also gave up lazy streams, namespaces
on defs, type aliases and list spread: each was either a second evaluation
model with no total image (streams) or sugar that the rest of the language
already covers.

## 2. What Bend guarantees, and what Fire gets

| Guarantee | Bend | Fire |
|---|---|---|
| Termination | structural recursion, `@unsafe` opts out | total by construction; `unsafe def` is the one visible opt-out |
| Exhaustive matching | `match` over declared types | declared types; a non-exhaustive match is fallible (`Abort`) |
| Effects in types | `IO`, `Result` | inferred, never written |
| No hidden copying | affine variables, `+` explicit | the compiler inserts `+` |
| Laws | `law` + proof term | `law` statement; closed and finite laws proven by the compiler; the rest proven in Bend against the image |

The first two rows are what §4 delivers. The last row is where Fire stops
on purpose: proofs that need induction are written in Bend, in a
`<program>.proof.bend` beside the program, against the generated image. Fire's
contribution is that the law is written in the language the human is using
and that the image is stable enough for `insert` to mean the same def in
the program, the claim and the proof.

## 3. The language: what the guarantees ask of the surface

`docs/language.md` is the reference; this section says why the surface is
the way it is.

### 3.1 Declared data types

```fire
type Shape
    Circle(radius)
    Square(side)

type Tree
    Leaf
    Node(left: Tree, value, right: Tree)

type Player
    X
    O
```

* A `type` has one or more constructors; a constructor has zero or more
  fields. A field without a type is a type parameter of its own; the
  type's parameters are its untyped fields in order (`Tree` above is
  `Tree<A>`, and `Tree` inside its own declaration means the type being
  declared with the same parameters). Fields may be typed with any Fire
  type.
* Constructors are functions (`Node(Leaf, 3, Leaf)`) and positional
  patterns (`Node(l, v, r) =>`). A nullary constructor is a value (`X`).
* `match` over a declared type is exhaustive when every constructor has an
  arm or there is a catch-all; otherwise the match is fallible.
* `T | nothing` and results keep their syntax and become instances of the
  same machinery (Bend's `Maybe` and `Result`).
* Classes (`def` with `public` members) are unchanged: a class is a
  product type with methods, and it stays inferred.

A `type` is needed only for alternatives and recursion. Records, tuples,
lists, dictionaries, classes and functions stay inferred.

### 3.2 Laws

```fire
law insert_keeps_sorted
    for x: int, t: Tree if sorted(t)
    sorted(insert(x, t))

law other_twice
    for p: Player
    other(other(p)) == p

law sort_small
    sorted([3, 1, 2]) == [1, 2, 3]
```

* `for` names the quantified variables with their types. This is the one
  place a type is written for a value, since a law ranges over a type,
  not over data. `if` adds a hypothesis. The body is an equation
  (`a == b`, compared structurally at the type of `a`) or a boolean
  expression (the claim that it holds).
* A law may mention pure and fallible defs. It may not mention an IO def
  (Bend cannot state it) or a def that may diverge (the checker would
  hang; measured, not guessed).

One statement, three strengths:

| | what happens | reported as |
|---|---|---|
| test | `fire --test` runs the law as a property check with generated instances (ints, floats, strings, bools, lists, and every declared type) | *tested* |
| claim | the compiler emits a Bend `law` beside the def; `fire --check` runs Bend's checker and lists the open claims | *open* |
| theorem | a `<program>.proof.bend` next to the program fills the law with a def of the same name; `fire --check` appends it to the image | *proven* |

The compiler proves what is mechanical:

* a **closed** law (no `for`) is proven by `{==}`: Bend normalizes both
  sides. This is a unit test the checker runs at compile time, and a real
  proof of that instance (`docs/design/01`, `02`, `09`).
* a law whose variables all range over **finite** types (declared types
  with only nullary constructors, `bool`) and has no hypothesis is proven
  by a generated case split closed with `{==}` in each case
  (`docs/design/08`).
* everything else is open. The report says so plainly, and the proof is
  written in Bend against the image (§4.8).

Inline `assert` stays a runtime check with the `Abort` effect. An assert
that mentions only parameters and pure calls, and is not under a loop, can
later be hoisted into a law whose hypotheses are the branch conditions
leading to it; once that law is proven the check is erased and the def
loses `Abort`. That is a refinement on top of `law`, not part of this
design's first phases.

### 3.3 Termination: `unsafe def`

A first version of this design made divergence an inferred effect,
`Diverge`, reported but never written. Fire instead makes totality strict:
a def the compiler cannot see terminate is an error, unless the def says
`unsafe def`. The reasons:

* An inferred effect propagates silently: one `while` deep in a helper
  makes `main` diverge-capable, and the author learns it from a report.
  A keyword puts the claim where the reasoning is, at the def whose
  termination is a theorem beyond the checker (Euclid's `gcd`, Newton's
  square root, Collatz).
* Bend itself works this way: `@unsafe` is written, per def.
* The diagnostic is better as an error. When `f(n - 1)` is rejected under
  `if n == 0`, the message says which rule the recursion misses (here: `n`
  may be negative; guard with `n <= 0`), and most programs are fixed by
  following it, not by opting out.

`while` is the unbounded loop, so it is allowed only in an `unsafe def`; a
bounded search is a `for` over a range with `break`. Open ranges survive
only zipped with a finite iterable (`for i, x in 0.., xs`), where the
finite one ends the loop. `fire --types` tags defs that are or call unsafe
code, `fire --check` lists them, and `fire --total` rejects a program that
has any.

The rule keeps a familiar cost honest. `quicksort` written as "filter the
rest, recurse on both halves" recurses on lists that are not parts of its
argument, so Bend cannot see that it ends, and the def must say `unsafe`.
The same sort written bottom-up as merges of runs is total
(`examples/sorting.fire` has both). Recursion on an int (`fib(n - 1)`) is
not structural either; §4.4 says how the common shape of it is made total.

### 3.4 Partial builtins

Nothing changes. `xs[i]` is `Abort` and has been visible as such all along;
the total forms are patterns (`[first, ...rest]`), `xs[i] or default`, and
`xs.first()`. The documentation stops presenting indexing as the default.

## 4. The image

Each subsection names the program under `docs/design/` that proves the
form is accepted.

### 4.1 Names

User names are emitted verbatim: a Fire def `insert` is the Bend def
`insert`, a `type Tree` is `Tree`, a constructor `Node` is `Node`, a method
`push` of a class `Stack` is `Stack.push`. A name that collides with Base
gets a trailing underscore (a constructor `Zero` is `Zero_`). The
compiler's own defs live under `F.` (the runtime prelude) and under an `F`
segment of what they belong to: `insert.F.if1` for a branch helper,
`Tree.F.show` for a derived operation, `Stack.F.new` for a constructor. No
Fire name contains a dot, so none of these can collide with a user name,
and a proof can say `insert` and mean it. A lambda is `insert.fn2`, a
nested def `outer.inner`.

### 4.2 Functions and polymorphism

A Fire def is one Bend def. Its type parameters are emitted, not
instantiated:

* a parameter the body leaves free is an erased type argument
  (`def size(-A: Data, t: Tree<A>)`, `01`);
* a parameter the body constrains (compares, shows, adds, indexes) makes
  the def a template, and the operations it needs are template parameters
  (`def insert(~A: Data, ~lt: A -> A -> Bool, +x: A, t: Tree<A>)`, `02`).
  A call site passes the derived operation for the concrete type
  (`~U32.is_lt`, `~Point.lt`); a generic caller forwards its own. This is
  dictionary passing with Bend templates as the dictionaries, and Bend
  makes one copy per instantiation, as it does for `List.map`.

Inference knows which parameters are constrained, so no annotation is
needed. The constraints are a qualified type scheme (`Ord A`, `Show A`,
`Num A`); the derived operations per type (`eq`, `lt`, `show`) are
top-level defs or closed lambdas, which is what a template argument must be.

Function-typed parameters follow the same rule: a def that takes a function
becomes a template taking the function's code (`~f: E -> A -> B`) and its
environment as data (`+env: E`). That is how the prelude's `map` works
and how every loop driver below works. A function value stored in data (a
list of functions, a record field) is a closure-set sum with one `call`
def (§4.5).

**Parameter order.** Bend's termination checker reads the arguments of a
self-call left to right: each must be passed unchanged until one is a
smaller part of its parameter. The checker finds a lexicographic order of
parameters that every self-call respects (`merge(xs, b)` shrinks `a`;
`merge(a, ys)` keeps `a` and shrinks `b`), and the lowering puts those
parameters first in that order (`09`, where `sorted.go(t, h)` must put the
list before the pivot). Fire's parameter order is unchanged; the image's is
the compiler's to choose.

### 4.3 Branches

Bend has no `if`, and a `match` may inspect only a parameter or a pattern
variable. Four forms cover every branch, chosen by what the branch
contains:

| branch | form | proof |
|---|---|---|
| an expression `if` whose operands are cheap, pure and total | `Bool.pick(T, c, a, b)`, eager | `04` |
| a statement or expression branch with no self-call and no early return | a helper def that matches its condition parameter and returns the branch's value or its live-out variables (a `Data` record read back through projection defs) | `07` |
| a branch containing a self-call | `Bool.pick(Unit -> T, c, _ => .., _ => ..)(Unit{})`: thunks, so no helper has to call back into the def being defined, and the recursion stays structural | `01`, `02`, `05`, `06` |
| a branch containing `return`, `break` or `continue` | the rest of the block moves into the branches that fall through, and the branch is a pick of terms | `05` |

The second form keeps the enclosing body straight-line and readable,
instead of a chain of continuation defs. The third keeps a recursive def
with a branch inside checkable, instead of an `@unsafe` dispatcher over a
frame type. The thunk form costs about 20 ns per branch (§5), which is why
it is used only where a helper def cannot be.

A `match` on a parameter stays a real Bend `match`; that is what the
termination checker reads. A `match` on a computed value goes through a
generated case eliminator, one def per declared type (`F.maybe.case`,
`Tree.F.case`), with a thunk per arm (`06`). Literal, list and record
patterns and guards compile to nested picks and eliminators; a
non-exhaustive match ends in the abort.

### 4.4 Loops

A `for` over finite data is a fold with early exit, and it is total:

* the body becomes a template `E -> S -> A -> Ctl<S>` over the loop's
  environment, state and element, answering `Next{s}`, `Break{s}` or
  `Return{v}`;
* `for x in xs` calls `F.for_list`, which recurses on the list and on the
  control value together in one `match xs c:` (`03`);
* `for i in a..b` calls `F.for_range`, which counts a `Nat` down and
  carries `i` along (`03`). A `Nat` counter costs nothing (§5);
* `for k, v in dict.entries()` folds the entry list;
* an IO or fallible body uses the `do` variant of the driver, whose
  recursive call sits inside the block (`04`).

`while` has nothing to descend on. Its driver (`F.loop`) checks the
condition inside the body so that the loop is one def, and that def is
`@unsafe`; `while` is allowed only in an `unsafe def` (`10`). Bend's own
report lists exactly the unsafe defs and their callers ("2 defs rely on
unsafe or foreign code").

**Int recursion.** Fire's `int` is a 32-bit signed number over Bend's
`U32`, which has no structure to recurse on. A def that recurses on an int
parameter decreased by literals (`n - 1`, or `n / 2`) under a guard that
keeps it at least the decrement (`if n <= 1 do return ...` before
`fib(n - 1) + fib(n - 2)`) gets a leading `fuel: Nat` parameter, started
at `n + 1` by every outside caller and counted down (`1n+fuel_`) by every
self-call. The fuel always outlasts the int, so the `0n` case is dead; Bend
still needs a value there, and the compiler builds one of the result type
(a generic part of it is taken from a parameter of that type, or the def
is rejected with a message).

### 4.5 Closures

A lambda is a top-level def taking its environment record first; a
function-typed value is its environment, or a sum over the environments of
every lambda that can flow into it. Bend closures are affine (callable
once), so this defunctionalization is what makes Fire functions callable
any number of times. A higher-order def is emitted once, as a template
over the function's code (§4.2).

### 4.6 Effects

An IO def's body is a `do IO<T>` block, a fallible def's is
`do Result<&2, &2, String, T>`, and a value used twice inside a block is
marked `+`. Branches inside blocks use the forms of §4.3 (`05`). The abort
is unwrapped once, at the IO boundary (`F.io_unwrap`).

### 4.7 Data

* A `type` is `type Tree<-A: Data> is Data:` with one line per
  constructor, fields typed by the Fire types (`01`).
* A class is a `Data` type with one constructor and a def per method
  taking `self` first; a mutating method returns the rebuilt record.
* A record literal's shape is a generated nominal type keyed by its field
  names (`F.Rec.memo_value`).
* Dictionaries are Base's `Map` (string keys); sorting is Base's
  `List.sort` with a `~le` template. The prelude keeps the signed 32-bit
  arithmetic, string formatting and parsing that Base does not have.

### 4.8 Laws and proofs

A Fire law compiles to a Bend `law` beside the def it is about:

```python
law insert_keeps_sorted:
  for +x: U32
  for xs: List<&2, U32>
  for h: {sorted(xs) == True{} : Bool}
  {sorted(insert(x, xs)) == True{} : Bool}
```

A hypothesis is an extra parameter of equality type, not a `where` clause
(`where` makes the variable a dependent pair, which the claim would then
have to project; `09`). A boolean body is `{e == True{} : Bool}`; an
equation is `{a == b : T}`.

A closed law gets `def name(): {==}` emitted after it (`01`, `02`, `09`); a
finite-domain law gets its case split (`08`). Both are in every image, so a
false one fails the build with Bend's two sides. An open law is emitted
without a def only in the image `fire --check` hands to `bend --check-only`,
which reports it as a TODO, and `fire --check` shows it as *open* (`09`); a
runnable image leaves it out, since a TODO would stop the program. A proof
lives in `<program>.proof.bend` and fills the law with `def name(..)`;
`fire --check` appends that file to the image when it exists.

## 5. Measurements

Native binaries, this machine, `bend` 2.0.25, one run each; the loop bodies
are a xorshift step so that clang cannot close the loop into a formula.

| what | time |
|---|---|
| 100 M iterations, `Nat` countdown (total) | 0.205 s |
| 100 M iterations, `@unsafe` U32 loop | 0.204 s |
| 100 M iterations with a branch as a helper def | 0.35 s |
| 100 M iterations with a branch as `Bool.pick` thunks | 2.3 s |
| `bend --check-only` on a closed law sorting 60 elements | 0.28 s |

So: a `Nat` loop counter is free, which is what makes `for` over a range
total at no cost; a thunk branch costs about 20 ns, which is why §4.3
reserves it for branches under a self-call; and closed laws are cheap
enough to run on every compile.

## 6. The compiler

```
grammar/fire.pest, src/ast.rs    parse: source -> AST (with type, law, unsafe def)
src/check/                       resolve names; infer types, constraints,
                                 closure sets, effects and the descent
                                 order; desugar -> Core
src/core.rs                      Core: explicitly typed, fully resolved
src/lower/                       Core -> Bend IR (§4): templates, branches,
                                 loops, eliminators, closures, do-blocks, fuel
src/ir.rs, src/prune.rs          IR, printer, affine marks; prelude pruning
src/prelude.bend                 the runtime: drivers, eliminators, numbers,
                                 strings, lists, maps
src/testgen.rs                   laws as property tests (`--test`)
src/main.rs                      run, -o, --types, --check, --test, --total
```

The one structural decision is **Core**. `check` finishes everything that
needs types: method and builtin resolution, pipelines, `$`, keyword
arguments, defaults, mutating methods as functional updates, `self`,
constraint dictionaries at call sites. `lower` then does only what Bend's
shape demands: parameter order, branch forms, loop drivers, eliminators,
closure environments, `do` blocks and `+` marks. `docs/compiler.md` walks
through both.

## 7. Status

Everything above is implemented; every program under `examples/` and
`tests/cases/` compiles to an image Bend's checker accepts, runs to its
golden output, and carries `@unsafe` only in defs written `unsafe def` and
their callers. What remains open, in order of value:

* **Assert hoisting.** An `assert` that mentions only parameters and pure
  calls could become a law whose hypotheses are the branch conditions
  leading to it; once that law is proven the check is erased.
* **An affinity lint.** The compiler inserts `+` where a value is used
  twice; a lint could report the copies that are expensive (a large list
  captured by a closure that runs per element).
* **The obvious induction.** An open law over a list or a declared type
  whose proof is structural induction closed by `{==}` in each case could
  be attempted before it is reported open.

## 8. Costs and limits

* **Declarations.** Sum types and recursive data must be declared. Nothing
  else.
* **`unsafe def` is needed for real theorems.** Recursion that is neither
  structural nor an int counted down under a guard must opt out:
  `quicksort` on filtered lists, `gcd`, Newton's iteration. The examples
  show each next to a total alternative where one exists. `--total` makes
  the opt-out an error.
* **Thunk branches.** A self-call under a branch costs about 20 ns per
  branch. Tree insertion pays it once per level; it does not appear in
  loops, which use helper defs.
* **Compile time.** Closed laws are normalized by the checker on every
  compile; Bend copies templates per instantiation as it did for the
  prelude's templates. Both are measured small (§5) and both grow with
  the program.
* **Mutual recursion** between defs is unsupported. Bend has none, and a
  frame-dispatcher encoding would be unsafe by construction. Merging the
  defs into one, dispatching on a parameter, keeps them total.
* **Bend's own limits** shape the image: no `if`, a match only on
  parameters, definitions before uses, affine pairs, templates closed.
  Every form in §4 exists because of one of them, and each has a program
  showing Bend accepts it.

## 9. Non-goals

* **Dependent types in Fire.** That would make Fire a re-syntaxed Bend
  and end inference. Proofs beyond the mechanical cases are written in
  Bend.
* **A prover.** The compiler proves closed and finite laws and may later
  *attempt* the one obvious induction; anything more is research.
* **Contracts compiled to Bend propositions.** Bend is a proof assistant,
  not an SMT-backed verifier: every obligation needs a proof term, so this
  is the previous point with a translation in the way.
* **An affine surface language.** Copies stay implicit and cheap to reason
  about; where they are expensive, a lint says so.
