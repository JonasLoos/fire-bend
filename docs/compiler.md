# How the compiler works

Pipeline: parse (`grammar/fire.pest` → `src/ast.rs`) → `infer/` (types,
effects, closure sets) → `lower/` (Bend IR) → `ir.rs` (printer). The
generated program starts with `import Base` and the runtime prelude
(`src/prelude.bend`), followed by one Bend def per Fire def, and `main`.

## What Bend enforces

Bend 2 is a typed, affine, total language, and the lowering has to respect
rules a tree-walking interpreter never sees. From experiments with Bend
2.0.x:

1. A `match` only inspects a parameter or a variable bound by a pattern,
   never a computed value, and no `let` may precede a match. Nested matches
   must follow parameter order.
2. Definitions must precede their uses. There is no mutual recursion, not
   even under `@unsafe`.
3. Variables are affine. `+x` makes a Data value reusable, but `+` on a
   parameter is part of the function's type, so a function passed as a
   template argument must have plain parameters and rebind (`+y = x`)
   inside.
4. Template (`~f`) arguments must be closed terms; closures are callable
   once and cannot live in Data.
5. In a `do` block, lets are affine and annotated, and destructuring is a
   match (so it needs a parameter).
6. `List<&1, T>` and `List<&2, T>` are different types; the compiler uses
   `List<&2, T>` everywhere and its own prelude for list operations.

## Inference (`src/infer/`)

Hindley-Milner with deferred constraints. Every binding, parameter and
expression gets one type (`types.rs`); constraints that need a type that
is not known yet (`x or default`, `xs[i] = v`, a method on a parameter)
are queued and resolved when it is. Defs are typed once from their body:
generalized where the body leaves a parameter free, otherwise re-inferred
as a *template copy* per argument type at each call. Recursive calls whose
argument types are not yet known are resolved when the enclosing def is
finished.

Effects (pure / fallible / IO) are inferred per def and composed through
calls. An exhaustive match cannot abort; an abort the analysis proves
unreachable compiles to `F.crash`.

Closure sets: a function-typed value carries the set of lambdas and defs
that can flow into it. One member means the value *is* that lambda's
environment record; several mean a sum type with an `apply` def. A set
whose environment holds a member of the same set has a recursive type,
which Bend cannot express, so it is rejected with a message.

The result is a typed AST (`tast.rs`) with the sugar removed: pipelines,
`$`, implicit self, keyword arguments, mutating methods.

## Lowering (`src/lower/`)

* **Every branch is a def.** An `if`, `match` or loop in statement position
  splits its block: the statements after it become a continuation def whose
  parameters are the live variables, and each branch ends by calling it. A
  `var` reassigned in a branch flows out as an argument.
* **Loops are drivers.** A loop becomes a control type
  (`Next{state} | Break{state} | Return{v}`), a body def that runs one
  iteration and answers a control value, and one `@unsafe` self-recursive
  driver def.
* **Lambdas are lifted.** Every lambda becomes a top-level def taking an
  environment record of its captures first. Pipeline stages and
  higher-order prelude functions are templates that thread the environment
  through (`map_env(~Env, ~A, ~B, ~stage, env, xs)`).
* **Classes are records plus defs.** `def Counter(...)` becomes `type
  F.Counter is Data` with one constructor, a constructor def, and one def
  per method taking `self` first. A mutating method returns the new record
  (`F.Ret{obj, value}` when it also answers a value) and the caller rebinds
  the receiver path.
* **Effects are do-blocks.** An IO function's body is a `do IO<T>` block, a
  fallible one's is `do Result<...>`. Because do-lets are affine, a value
  used twice inside a do-block is passed to a continuation def with `+`
  parameters.
* **Everything is monomorphized.** Generic defs are instantiated per
  concrete type, constrained ones copied per argument type, and derived
  `show`, `eq` and `lt` defs are generated per record type so `print`,
  `==` and `sorted` work on any value.
* **Recursion is merged.** A recursive function whose body was split into
  helper defs is merged with them into one `@unsafe` dispatcher def over a
  frame sum type (`F.K.<owner>`), since Bend has no mutual recursion.
* **Names are prefixed** (`f.` defs, `F.` types, `__` temporaries) so they
  never collide with Bend's Base or with user names, and defs are emitted
  in dependency order.

Every loop and every non-structural recursion carries Bend's `@unsafe`
marker, so `bend` reports "with N unsafe annotations". Termination proofs
are not a goal.

## Runtime

`fire file.fire` writes the Bend source to a temporary directory, builds a
native binary with `bend file.bend -o file` (clang), runs it and streams
its output. `BEND_LANE=js` builds `file.js` and runs it with `node`. When
Bend's native code generator crashes on a program its checker accepted (an
internal `TypeError`), the runner falls back to the JavaScript lane.

The prelude (`src/prelude.bend`) holds everything the generated code calls
that Base does not provide: list, string, map and float helpers, `show`
formatting, the pure crash, sorting. Only the items a program reaches are
emitted (`src/prune.rs` walks the references from the generated defs
through the prelude's `def` and `type` blocks), so a small program carries
a few dozen lines of it rather than all ~1500, and Bend checks that much
less. The prelude must stay in dependency order and free of mutual
recursion; after editing it run

```bash
python3 tools/prelude_sort.py src/prelude.bend
```

which reorders the defs, marks pattern binders used more than once with
`+`, and reports any cycle.

## Testing

`tests/programs.rs` compiles every program under `examples/` and
`tests/cases/` and, with `bend` on `PATH`, builds and runs it and compares
the output with the `.out` file next to it. `tests/cases/` holds one small
program per language rule or fixed bug; add one whenever semantics change.
