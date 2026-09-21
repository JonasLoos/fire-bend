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

Three ideas:

1. **Pipelines compose computation.** `|>` applies, `*>` maps, `?>` filters,
   `!>` handles errors, and `$` names the piped value.
2. **One construct, `def`, covers functions, classes and modules.** A def that
   declares `public` members builds an object; methods are closures.
3. **Types and effects are inferred, never required.** Every program is
   statically typed. A function that can fail returns a result, one that
   prints is an IO function, and the compiler works that out from the body.

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
fire examples/word_stats.fire --types        # print every def's type and effect
```

`BEND_LANE=js` runs through the JavaScript lane instead of a native binary.

## A tour

```fire
x = 42                                    # bindings are immutable
var y = 1                                 # unless declared var
y += 1

def fib(n)                                # functions; the last expression is the value
    if n <= 1 do 1 else fib(n - 1) + fib(n - 2)

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

for i, word in 0.., ["a", "b", "c"]       # loops zip; an open range counts
    print("{i}: {word}")

port = read_config()                      # results ride the pipeline:
    |> $.parse_int()                      # skipped when the input is an err
    !> 8080                               # and this is the recovery

evens = 0.. ?> $ % 2 == 0                 # lazy streams over open ranges
print(evens.take(4))                      # [0, 2, 4, 6]
```

The full reference is [`docs/language.md`](docs/language.md); how the
compiler turns this into Bend is in [`docs/compiler.md`](docs/compiler.md).
Where the language is going, and why, is [`docs/design.md`](docs/design.md):
declared data types, laws, and a Bend image that Bend's own checker can
certify total.

## Layout

| Path | What it is |
|---|---|
| `grammar/fire.pest` | the grammar (pest, indentation-aware) |
| `src/ast.rs` | AST and its construction from parse trees |
| `src/infer/` | type and effect inference |
| `src/lower/` | lowering to Bend IR |
| `src/ir.rs` | the IR and its printer |
| `src/prelude.bend` | runtime library; the part a program uses is emitted with it |
| `examples/` | programs with their expected output (`.out`) |
| `docs/design/` | the Bend shapes the redesign emits, each checked by `bend` in the tests |
| `tests/cases/` | one small program per language rule or fixed bug |

## Testing

```bash
cargo test
```

Every program under `examples/` and `tests/cases/` is compiled to Bend and,
when `bend` is on `PATH`, built, run and compared with its `.out` file.
`BEND_TESTS=skip` only checks compilation; `BEND_TESTS=require` fails when
`bend` is missing (CI runs this way).
