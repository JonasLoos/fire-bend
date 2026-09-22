# Fire

A small, indentation-based language where data flows left to right, compiled
to [Bend 2](https://bend-lang.com) and run on its runtime (native via clang,
or JavaScript).

```fire
result = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    ?> $ % 2 == 1     # filter: keep the odd ones
    *> $ * $          # map: square them
    |> sum            # apply: add them up

print("sum of odd squares: {result}")   # 165
```

Four ideas:

1. **Pipelines compose computation.** `|>` applies, `*>` maps, `?>` filters,
   `!>` handles errors, and `$` names the piped value.
2. **One construct, `def`, covers functions and classes.** A def that
   declares `public` members builds an object; methods are closures.
3. **Types and effects are inferred.** Every program is statically typed.
   A function that can fail returns a result, one that prints is an IO
   function, and the compiler works that out from the body. Only data with
   alternatives or recursion is declared (`type Tree`).
4. **Programs are total, and Bend checks it.** Every def is seen to
   terminate and every match to be covered, and the compiled program is one
   Bend's own checker certifies. Where termination is a theorem beyond the
   checker, the def says `unsafe def`. Laws state what the defs promise;
   the compiler proves the mechanical ones, tests the rest, and hands them
   to Bend as claims.

> [!WARNING]
> This is an experimental proof of concept, not production-ready software.

## Install and run

You need Rust, [Bend](https://bend-lang.com) (`curl -fsSL https://bend-lang.com/install.sh | sh`)
and clang; `node` for the JavaScript lane.

```bash
cargo install --path .

fire examples/word_stats.fire                # compile and run
fire examples/word_stats.fire -o out.bend    # write the Bend source
fire examples/word_stats.fire -o word_stats  # build a native binary with bend
fire examples/word_stats.fire -o out.js      # build for node
fire examples/word_stats.fire --types        # every def's type, effects and termination argument
fire examples/types_and_laws.fire --check    # Bend's checker: laws proven or open, unsafe code
fire examples/types_and_laws.fire --test     # every law checked on generated values
fire examples/sorting.fire --total           # reject a program with unsafe code
```

`BEND_LANE=js` runs through the JavaScript lane instead of a native binary.

## A tour

```fire
x = 42                                    # bindings are immutable
var y = 1                                 # unless declared var
y += 1

def fib(n)                                # functions; the last expression is the value
    if n <= 1 do 1 else fib(n - 1) + fib(n - 2)   # total: n counts down under the guard

double = n => n * 2                       # lambdas
greet = (name = "world") => "hi {name}"   # defaults, strings interpolate

def Counter(start = 0)                    # a def with public members is a class
    public var count = start
    public increment = () => count += 1   # methods see members as locals

var c = Counter()
c.increment()                             # objects are values: this rebinds c
print(c.count)                            # 1

def Dog(name)                             # inheritance: adopt a parent, override
    parent = Animal(name)
    self.{...} = parent
    public speak = () => parent.speak() + " Woof!"

match xs.first()                          # pattern matching, typed: T | nothing
    nothing => print("empty")
    n => print("starts with {n}")

[first, ...rest] = [1, 2, 3]              # destructuring
{name, age} = person
{sqrt, pi} = $math                        # modules are records

for i, word in 0.., ["a", "b", "c"]       # loops zip; the list ends the loop
    print("{i}: {word}")

port = read_config()                      # results ride the pipeline:
    |> $.parse_int()                      # skipped when the input is an err
    !> 8080                               # and this is the recovery

type Tree                                 # declared data: alternatives, recursion
    Leaf
    Node(left: Tree, value, right: Tree)  # an untyped field is a type parameter

def size(t)                               # recursion on a piece: always ends
    match t
        Leaf => 0
        Node(l, _, r) => size(l) + 1 + size(r)

law size_of_leaf                          # proven when the program is built
    size(Leaf) == 0

unsafe def gcd(a, b)                      # a theorem the checker cannot follow
    if b == 0 do a else gcd(b, a % b)
```

The full reference is [`docs/language.md`](docs/language.md); how the
compiler turns this into Bend is in [`docs/compiler.md`](docs/compiler.md).
Why it is built this way, with every claim about Bend backed by a checked
program, is [`docs/design.md`](docs/design.md).

## Layout

| Path | What it is |
|---|---|
| `grammar/fire.pest` | the grammar (pest, indentation-aware) |
| `src/ast.rs` | AST and its construction from parse trees |
| `src/check/` | names, type and effect inference, termination, laws; produces Core |
| `src/core.rs` | Core: the typed, resolved program |
| `src/lower/` | lowering to Bend IR in forms Bend's checker can certify |
| `src/ir.rs` | the IR and its printer |
| `src/prelude.bend` | runtime library; the part a program uses is emitted with it |
| `src/testgen.rs` | laws as property tests (`--test`) |
| `examples/` | programs with their expected output (`.out`) |
| `docs/design/` | the Bend shapes the compiler emits, each checked by `bend` in the tests |
| `tests/cases/` | one small program per language rule or fixed bug |

## Testing

```bash
cargo test
```

Every program under `examples/` and `tests/cases/` is compiled to Bend and,
when `bend` is on `PATH`, checked by Bend (including its laws), built, run
and compared with its `.out` file.
`BEND_TESTS=skip` only checks compilation; `BEND_TESTS=require` fails when
`bend` is missing (CI runs this way).
