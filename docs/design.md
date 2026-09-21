# Fire 2: the Bend image is the program

This is the design for the next Fire. It keeps what Fire is for, a
Python-shaped language where types and effects are inferred, and changes
what the compiler is: from a translator that gets programs *through* Bend's
checker to one that emits programs Bend's checker can *certify*. Every
claim about Bend below is backed by a program under `docs/design/`, checked
by `bend` 2.0.25 in the test suite (`tests/design.rs`).

## 1. The principle

Bend 2 is a total, affine, dependently typed language with a checker that
proves termination, exhaustiveness, effect discipline and user-stated laws.
Fire compiles to Bend but inherits none of that, and not because Fire's
type system is weaker. The lowering discards the structure the checker
needs: every loop and every recursive function is emitted `@unsafe`,
generic defs become one copy per call site, branches inside a recursive
function are merged into an `@unsafe` dispatcher, and there is no way to
state a law about the result. Bend checks the image and finds nothing to
certify.

The redesign has one rule:

> **The Bend image is the program.** Every lowering step produces a form
> Bend's checker can see through. Fire does inference and sugar; Bend does
> the checking; Fire reports what Bend will find, and never certifies
> anything on its own.

Three consequences follow, and they are the whole design:

1. **Every construct has a total image**, except the ones that are
   inherently partial (`while`, open ranges, recursion with no structure to
   descend on). Those get an inferred, visible effect, `Diverge`, and only
   they carry `@unsafe`.
2. **Polymorphism is emitted, not expanded.** A generic def is one Bend
   def; Bend makes the copies. That gives every Fire def a stable Bend name
   a proof can unfold.
3. **Laws are a language feature.** `law` states a claim in Fire syntax
   about Fire names. It is a property test, an open claim in the image,
   and a theorem once a Bend proof fills it. The mechanical cases (closed
   claims, finite domains) are proven by the compiler.

What Fire gives up: `type` declarations become necessary for sum types and
recursive data. Everything else stays inferred, including generics with
constraints (§4.2). "Types are never required" becomes "types are required
to declare data with alternatives or recursion", which is the same trade
every ML-family language makes.

## 2. What Bend guarantees, and what Fire gets

| Guarantee | Bend | Fire today | Fire 2 |
|---|---|---|---|
| Termination | structural recursion, `@unsafe` opts out | every loop and recursion `@unsafe` | total by construction; `Diverge` effect marks the rest |
| Exhaustive matching | `match` over declared types | only for `nothing` and results | declared types; a non-exhaustive match is `Abort`, as now |
| Effects in types | `IO`, `Result` | inferred, sound | unchanged, plus `Diverge` |
| No hidden copying | affine variables, `+` explicit | compiler inserts `+` | unchanged (a lint later) |
| Laws | `law` + proof term | nothing | `law` statement; closed and finite laws proven by the compiler; the rest proven in Bend against the image |

The first two rows are what §4 delivers. The last row is where Fire stops
on purpose: proofs that need induction are written in Bend, in a
`PROOF.bend` beside the program, importing the generated module. Fire's
contribution is that the law is written in the language the human is using
and that the image is stable enough for `insert` to mean the same def in
the program, the claim and the proof.

## 3. The language: what changes at the surface

Everything in `docs/language.md` stays unless listed here.

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
* Constructors are functions (`Node(Leaf, 3, Leaf)`) and patterns, either
  positional (`Node(l, v, r) =>`) or by name (`Node{value} =>`). A
  nullary constructor is a value (`X`).
* `match` over a declared type is exhaustive when every constructor has an
  arm or there is a catch-all; otherwise the match is fallible, as today.
* `T | nothing` and results keep their syntax and become instances of the
  same machinery (Bend's `Maybe` and `Result`).
* Classes (`def` with `public` members) are unchanged: a class is a
  product type with methods, and it stays inferred.

A `type` is needed only for alternatives and recursion. Records, tuples,
lists, dictionaries, classes and functions stay inferred, as now.

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
| test | `fire --test` runs the law as a property check with generated instances (ints, strings, lists, and every declared type has a generator) | *tested* |
| claim | the compiler emits a Bend `law` beside the def; `fire --check` runs Bend's checker and lists the open claims | *open* |
| theorem | a `PROOF.bend` next to the program imports the generated module and fills the law with a def of the same name | *proven* |

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

### 3.3 Effects: `Diverge`

Effects stay inferred and unwritten. There is one more of them:

| effect | source | image |
|---|---|---|
| `Abort` | `error`, `assert`, `xs[i]`, a failing `{ok} =`, a non-exhaustive match | `do Result` |
| `IO` | `print`, `$io` | `do IO` |
| `Diverge` | `while`; `for` over an open range or a stream; a recursion the descent rule (§4.2) does not accept; a call to a def with `Diverge` | `@unsafe` |

`fire --types` shows the effect set (`[IO, Diverge]`). `fire --check`
lists the defs that may diverge, since they are the ones Bend excludes from
its guarantees. `fire --total` makes any of them an error. There is no
`unsafe` keyword: an effect is inferred and reported, never written, and
that includes this one.

The rule keeps a familiar cost honest. `quicksort` written as "filter the
rest, recurse on both halves" recurses on lists that are not parts of its
argument, so it may diverge as far as Bend can tell, and Fire says so. The
same function written as a fold, or as insertion into a sorted structure,
is total. Recursion on an int (`fib(n - 1)`) is not structural either;
§4.4 says how the common shape of it is made total.

### 3.4 Partial builtins

Nothing changes. `xs[i]` is `Abort` and has been visible as such all along;
the total forms are patterns (`[first, ...rest]`), `xs[i] or default`, and
`xs.first()`. The documentation stops presenting indexing as the default.

## 4. The image

Each subsection names the program under `docs/design/` that proves the
form is accepted.

### 4.1 Names

User names are emitted verbatim: a Fire def `insert` is the Bend def
`insert`, a `type Tree` is `Tree`, a constructor `Node` is `Node`. A name
that collides with Base gets a trailing underscore. The compiler's own
defs live under `F.` (the runtime prelude) and under the def they belong to
(`insert.if1`, `insert.body`, `insert.fn2` for a lambda). A proof can then
say `insert` and mean it.

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

Inference already knows which parameters are constrained; it is what
triggers template copies today. So no annotation is needed, and the
"re-infer a copy per argument type" mechanism goes away. The constraints
are a qualified type scheme (`Ord A`, `Show A`, `Num A`), and the derived
operations per type (`eq`, `lt`, `show`) are top-level defs, which is what
a template argument must be.

Function-typed parameters follow the same rule: a def that takes a function
becomes a template taking the function's code (`~f: E -> A -> B`) and its
environment as data (`+env: E`). That is how the prelude's `map` works
today and how every loop driver below works. A function value stored in
data (a list of functions, a record field) is the closure-set sum the
current compiler builds, with one `apply` def; that representation is
kept.

**Parameter order.** Bend's termination checker reads the arguments of a
self-call left to right: each must be passed unchanged until one is a
smaller part of its parameter. The lowering orders the image's parameters
so that the descending one comes first (`09`, where `sorted.go(t, h)` must
put the list before the pivot), searching permutations when several calls
descend on different parameters. Fire's parameter order is unchanged; the
image's is the compiler's to choose.

### 4.3 Branches

Bend has no `if`, and a `match` may inspect only a parameter or a pattern
variable. Four forms cover every branch, chosen by what the branch
contains:

| branch | form | proof |
|---|---|---|
| an expression `if` whose operands are cheap, pure and total | `Bool.pick(T, c, a, b)`, eager | `04` |
| a statement or expression branch with no self-call and no early return | a helper def that matches its condition parameter and returns the branch's value or its live-out variables (a `Data` record read back through projection defs) | `07` |
| a branch containing a self-call | `Bool.pick(Unit -> T, c, _ => .., _ => ..)(Unit{})`: thunks, so no helper has to call back into the def being defined, and the recursion stays structural | `01`, `02`, `05`, `06` |
| a branch containing `return` | the rest of the block becomes the else branch (a continuation def), as today | |

The second form replaces today's continuation chains (`main.k9` calling
`main.k10` calling `main.k11`): the enclosing body stays straight-line and
readable. The third form replaces `merge.rs`: a recursive def with a branch
inside no longer becomes an `@unsafe` dispatcher over a frame type. The
thunk form costs about 20 ns per branch (§5), which is why it is used only
where a helper def cannot be.

A `match` on a parameter stays a real Bend `match`; that is what the
termination checker reads. A `match` on a computed value goes through a
generated case eliminator, one def per declared type (`F.Maybe.case`,
`Tree.case`), with a thunk per arm (`06`). Literal, list and record
patterns and guards compile to nested picks and eliminators; a
non-exhaustive match ends in the abort, as today.

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

`while`, `for` over an open range, and stream consumers (`take`, `first`,
a `for` over `1..` with `break`) have nothing to descend on. Their driver
computes the next condition at the call site so that it is one def, and
that def is `@unsafe`; the enclosing def gets `Diverge` (`10`). Bend's own
report lists exactly those defs ("2 defs rely on unsafe or foreign code").

**Int recursion.** Fire's `int` is a 32-bit signed number over Bend's
`U32`, which has no structure to recurse on. A def that recurses on an int
parameter decreased by literals under a base case compared with a literal
(`fib`, `factorial`, `countdown`) is lowered to a `Nat` descent: the
wrapper converts, the worker matches `1n+p`. This is a recognizer for one
shape, planned for phase 6; until then such defs report `Diverge`.

### 4.5 Closures

Unchanged in representation: a lambda is a top-level def taking its
environment record first; a function-typed value is its environment,
or a sum over the environments of every lambda that can flow into it.
Bend closures are affine (callable once), so this defunctionalization is
what makes Fire functions callable any number of times. What changes is
that a higher-order def is emitted once as a template (§4.2) instead of
once per closure set.

### 4.6 Effects

Unchanged: an IO def's body is a `do IO<T>` block, a fallible def's is
`do Result<&2, &2, String, T>`, and a value used twice inside a block is
marked `+`. Branches inside blocks use the forms of §4.3 (`05`). The abort
is unwrapped once, at the IO boundary (`F.unwrap`).

### 4.7 Data

* A `type` is `type Tree<-A: Data> is Data:` with one line per
  constructor, fields typed by the Fire types (`01`).
* A class is a `Data` type with one constructor and a def per method
  taking `self` first; a mutating method returns the rebuilt record.
  Unchanged.
* A record literal's shape is a generated nominal type keyed by its field
  names. Unchanged.
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
finite-domain law gets its case split (`08`); an open law is emitted
without a def and `bend --check-only` reports it as a TODO, which
`fire --check` shows as *open* (`09`). A proof lives in `PROOF.bend`,
imports the generated module, and fills the law as `def M.name(..)`; that
file is what `fire --check` runs when it exists, following Bend's own
`LAWS.bend` / `PROOF.bend` convention.

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

### 6.1 Phases

```
grammar/fire.pest, src/syntax/   parse: source -> AST (+ type, law)
src/check/                       resolve names; infer types, constraints,
                                 closure sets, effects (with Diverge) and
                                 the descent order; desugar -> Core
src/core.rs                      Core: explicitly typed, fully resolved
src/lower/                       Core -> Bend IR (§4): templates, branches,
                                 loops, eliminators, closures, do-blocks, +
src/bend/                        IR, printer, prelude, pruning, laws, proofs
src/main.rs                      run, -o, --types, --check, --test, --total
```

The one structural change is **Core**. Today's typed AST still carries
unresolved nodes (`MethodCall`, `Builtin`, `Member`, `Pipe`, `Stage`) that
the lowering resolves from types, and the lowering re-infers template
copies and monomorphizes. That is two phases doing each other's work. In
Fire 2, `check` finishes everything that needs types: method and builtin
resolution, pipelines, `$`, keyword arguments, defaults, mutating methods
as functional updates, `self`, patterns as decision trees, constraint
dictionaries at call sites. `lower` then does only what Bend's shape
demands: parameter order, branch forms, loop drivers, eliminators, closure
environments, `do` blocks and `+` marks. Each phase can be tested alone.

### 6.2 What is deleted

* template copies: `TemplateSrc`, `template_of`, per-call re-inference,
  and the instance worklist that monomorphizes generic defs;
* `@unsafe` loop drivers, except the `while` family;
* `src/lower/merge.rs`: recursion merged into a frame dispatcher;
* continuation defs for plain `if` and `match` statements;
* the deferred-constraint leak from inference into lowering;
* the prelude's own sort and about half of its list and map helpers, in
  favour of Base.

### 6.3 What is kept

The grammar and AST builder (extended); `types.rs` with its unifier and
levels (extended with qualified schemes); the effect fixpoint; the
closure-set analysis; `ir.rs` and its printer; `prune.rs`; the number,
formatting and string parts of the prelude; the build and run driver with
its native and JavaScript lanes; the test harness and every golden output
under `examples/` and `tests/cases/`, which are the safety net for the
whole migration.

## 7. Migration

Each phase ends with every existing program producing its golden output,
and reports one number: how many defs in `examples/` carry `@unsafe`.

| phase | work | exit criterion |
|---|---|---|
| 0 | this document and `docs/design/` | the images check under `bend` in CI |
| 1 | Core: move resolution into `check`, shrink `lower` to shape work | no semantic change; suite green |
| 2 | totality: `for` drivers, branch forms of §4.3, `Diverge` effect, drop `merge.rs` | `@unsafe` only on `while`, streams and non-structural recursion; `--types` shows `Diverge` |
| 3 | polymorphic emission: erased and template parameters, constraint dictionaries, drop template copies | one Bend def per Fire def |
| 4 | `type` declarations, constructors, eliminators; `Maybe` and `Result` as instances | `docs/language.md` §3.1 |
| 5 | `law`: parsing, emission, closed and finite proofs, `--check`, `--test`, `PROOF.bend` | `docs/language.md` §3.2 |
| 6 | int-descent recognizer; assert hoisting; affinity lint | `fib` is total |

Phases 2 and 3 are the bulk of the work and can be done in either order;
2 first gives the visible result (the `@unsafe` count) sooner.

## 8. Costs and limits

* **Declarations.** Sum types and recursive data must be declared. Nothing
  else.
* **`Diverge` is common at first.** Any recursion that is not structural
  descent reports it: `quicksort` on filtered lists, `gcd`, `fib` until
  phase 6. The report is honest, and the effect propagates through calls,
  so a program with one `while` shows it in `main`. `--total` is a choice,
  not the default.
* **Thunk branches.** A self-call under a branch costs about 20 ns per
  branch. Tree insertion pays it once per level; it does not appear in
  loops, which use helper defs.
* **Compile time.** Closed laws are normalized by the checker on every
  compile; Bend copies templates per instantiation as it did for the
  prelude's templates. Both are measured small (§5) and both grow with
  the program.
* **Mutual recursion** between defs stays unsupported. Bend has none, and
  the frame-dispatcher encoding would be `Diverge` by construction. It
  can be offered later under that effect.
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
