# Fire

Fire is a lightweight frontend for Bend 2, a total, dependently typed language with proofs. It keeps Bend's guarantees and adds a simpler syntax, type and effect inference, pipelines, and checked mutability.

```fire
def grade(score)                     # inferred types
    if score >= 90 do "A" elif score >= 75 do "B" else "C"

law top_marks                        # laws are proven when the program is built
    grade(100) == "A"

["92", "78", "n/a", "85"]
    *> $.parse_int()                 # text to numbers; "n/a" becomes an error
    *> grade                         # errors skip the stages they can't run
    !> "absent"                      # and are recovered here
    |> print                         # ['A', 'B', 'absent', 'B']
```

* **Pipelines compose computation.** `|>` applies, `*>` maps, `?>` filters,
  `!>` recovers from an error, and `$` is the piped value.
* **Types and effects are inferred.** A function that can fail returns a
  result, one that prints is IO, and the compiler works that out. Only data
  with alternatives or recursion is declared (`type Tree`).
* **One `def` covers functions and classes.** A def with `public` members
  builds an object; objects are values, never shared.
* **Programs are total.** Every def is seen to end and every match to be
  covered, and Bend's checker confirms it. Where termination is a theorem
  beyond the checker, the def says `unsafe def`.
* **Laws state what defs promise.** The compiler proves the mechanical
  ones, property-tests the rest, and hands them to Bend as claims.

> [!WARNING]
> Fire is an experimental proof of concept.

## Install and run

Fire needs Rust, [Bend](https://bend-lang.com) and clang (`node` for the
JavaScript target):

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
cargo install --path .

fire examples/basics.fire                  # compile and run
fire examples/basics.fire -o basics.bend   # write the Bend source
fire examples/basics.fire -o basics        # build a native binary
fire examples/basics.fire -o basics.js     # build for node
fire examples/totality.fire --types        # each def's type, effects and termination argument
fire examples/types_and_laws.fire --check  # Bend's verdict on laws and unsafe code
fire examples/types_and_laws.fire --test   # check every law on generated values
fire examples/sorting.fire --total         # reject a program with unsafe code
```

`BEND_LANE=js` runs programs through node instead of a native binary.

## A tour

```fire
x = 42                                    # bindings are immutable
var y = 1                                 # unless declared var
y += 1

def fib(n)                                # the last expression is the value
    if n <= 1 do 1 else fib(n - 1) + fib(n - 2)

double = n => n * 2                       # lambdas
greet = (name = "world") => "hi {name}"   # defaults; strings interpolate

def Counter(start = 0)                    # a def with public members is a class
    public var count = start
    public increment = () => count += 1

var c = Counter()
c.increment()                             # rebinds c: objects are values
print(c.count)                            # 1

match xs.first()                          # T | nothing, matched
    nothing => print("empty")
    n => print("starts with {n}")

[first, ...rest] = [1, 2, 3]              # destructuring
{sqrt, pi} = $math                        # builtin modules are records

for i, word in 0.., ["a", "b", "c"]       # lockstep; the list ends the loop
    print("{i}: {word}")

port = read_config()                      # results ride the pipeline:
    |> $.parse_int()                      # skipped when the input is an err
    !> 8080                               # and this is the recovery

type Tree                                 # declared data
    Leaf
    Node(left: Tree, value, right: Tree)  # an untyped field is a type parameter

def size(t)                               # recursion on a piece always ends
    match t
        Leaf => 0
        Node(l, _, r) => size(l) + 1 + size(r)

law size_of_leaf                          # proven when the program is built
    size(Leaf) == 0

unsafe def gcd(a, b)                      # termination the checker cannot see
    if b == 0 do a else gcd(b, a % b)
```

## Examples

| program | shows |
|---|---|
| [`basics`](examples/basics.fire) | bindings, functions, pipelines, closures, records, dictionaries, strings |
| [`objects`](examples/objects.fire) | classes, value semantics, inheritance, custom operators |
| [`results`](examples/results.fire) | `T \| nothing`, results, `!>`, pattern matching |
| [`totality`](examples/totality.fire) | what terminates, and `unsafe def` |
| [`types_and_laws`](examples/types_and_laws.fire) | declared types and laws |
| [`slices`](examples/slices.fire) | indexing and slicing |
| [`sorting`](examples/sorting.fire), [`strings`](examples/strings.fire), [`numeric`](examples/numeric.fire) | classic algorithms |
| [`word_freq`](examples/word_freq.fire), [`csv_records`](examples/csv_records.fire), [`report`](examples/report.fire) | text processing and formatting |
| [`bank_ledger`](examples/bank_ledger.fire), [`money_utils`](examples/money_utils.fire), [`template`](examples/template.fire), [`dungeon_sim`](examples/dungeon_sim.fire) | larger programs built from objects |

Each program's output is in the `.out` file next to it.

## Documentation

* [`docs/language.md`](docs/language.md): the language reference.
* [`docs/compiler.md`](docs/compiler.md): how Fire compiles to Bend, and
  why, with each Bend form backed by a program under
  [`docs/shapes/`](docs/shapes).

## Testing

```bash
cargo test
```

Every program under `examples/` and `tests/cases/` (one small program per
language rule) is compiled and, when `bend` is on `PATH`, checked, built,
run and compared with its `.out` file. `BEND_TESTS=skip` only compiles;
`BEND_TESTS=require` fails when `bend` is missing, as CI does.
