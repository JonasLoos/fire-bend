# The Fire language

Fire is a small, indentation-based, expression-oriented language. Every
program is statically typed with full inference, values are immutable data,
effects are inferred, and every program is total: each def is seen to
terminate and each match to be covered. Fire compiles to Bend 2, whose
checker confirms those guarantees on the compiled program
([`compiler.md`](compiler.md)).

This is the reference. For a first look, read the
[README](../README.md) and the programs under [`examples/`](../examples).

1. [Lexical structure](#1-lexical-structure)
2. [Bindings](#2-bindings)
3. [Functions](#3-functions)
4. [Pipelines](#4-pipelines)
5. [Data](#5-data)
6. [Control flow](#6-control-flow)
7. [Objects](#7-objects)
8. [Types](#8-types)
9. [Effects and errors](#9-effects-and-errors)
10. [Totality](#10-totality)
11. [Laws](#11-laws)
12. [Modules and builtins](#12-modules-and-builtins)
13. [Operator precedence](#13-operator-precedence)
14. [Not supported](#14-not-supported)

## 1. Lexical structure

```fire
# a comment
## a documentation comment, attached to the definition that follows

x = 42            # int
y = 3.14          # float
z = 1.2e-3        # scientific
h = 0xFF          # hex
b = 0b1011        # binary
s = 'raw text'    # plain string: no interpolation, no escapes
f = "x is {x}"    # interpolating string: `{expr}`, and `\n` `\t` `\\` escapes
t = `verbatim`    # raw string, in backticks
ok = true         # bool
n = nothing       # the unit value
```

An interpolation may carry a format spec, `{value:[[fill]align][0][width][.precision][f|d]}`,
with align `<`, `>` or `^`. Numbers pad on the left and text on the right
by default; a `0` before the width pads a number with zeros after its sign,
and a precision fixes a number's decimals.

```fire
"{price:.2f} €"       # 3.50 €
"[{total:8.2f}]"      # [    3.50]
"{name:<8}|{n:>5}"    # columns
"{'ada':*^9}"         # ***ada***
"{h:02}:{m:02}"       # 09:05, and -5 is -05
"{cents / 100:>6}"    # any expression before the spec
```

**Blocks** are introduced by indentation, never by a colon; a comment may
end the header line (`def f(x)  # doubles`). A short body can follow `do`
on the same line (`if x > 0 do print(x)`).

**Continuation lines.** An expression continues on an indented line that
*starts* with an operator (`|>`, `.`, `+`, `and`, ...). List and record
literals and call arguments may span indented lines, with the commas
between lines optional.

**Names** are `[A-Za-z_][A-Za-z0-9_]*`. Reserved: `def return public var if
elif else for in while break continue match not and or do true false
nothing type law unsafe`.

## 2. Bindings

```fire
x = 1             # immutable
var y = 2         # mutable
y = 3
y += 1            # compound assignment needs a var
a = b = 5         # chained: evaluated once, binds both
x = 4             # error: x is immutable
```

Every binding has one static type, inferred from its uses; assigning a
value of another type to a `var` is an error. Annotations are checked,
never required:

```fire
age: int = 30
names: [str] = []                    # a list of str
counts: {} = {}                      # a dictionary
def area(w: float, h: float): float  # parameter and result types
    w * h
def greet(p: {name: str, age: int})  # a record type lists its fields
    "hi {p.name}"
```

Values are copied, never shared: changing one binding never changes
another that received the same value (§7.1).

## 3. Functions

```fire
double = x => x * 2
add = (a, b) => a + b
greet = (name = "world") => "hello {name}"

classify = x =>                     # a block body: the last expression is the value
    doubled = x * 2
    if doubled > 10 do 'big' else 'small'

def fib(n)
    if n <= 1 do 1 else fib(n - 1) + fib(n - 2)
```

A function's value is its last expression; `return` leaves early.
Parameters take defaults (`=`), annotations (`:`) and patterns
(`{age} => age + 1`). Functions are values: pass them, return them, store
them in lists and records.

**Keyword arguments** come after the positional ones, in any order. Defs and
lambdas take them; builtins are positional only.

```fire
def box(width = 1, height = 2, depth = 3)
    width * height * depth

box(depth = 10)          # 20
box(4, depth = 10)       # 80
```

**Lambda bodies in pipelines.** A lambda that is a pipeline stage ends
before the next pipeline operator: in `xs ?> n => n > 2 |> sum` the stage
is `n => n > 2`. A lambda that starts the chain takes the rest as its
body: `f = x => x |> g` is `x => (x |> g)`, and so is a match arm
(`n => n |> $ * 2`). Parentheses change either.

**Closures.** A lambda or nested def captures the *values* its free
variables have when it is created. Assigning to a captured variable from
inside a lambda is an error; state that changes lives in objects (§7) or in
the `var`s of the function that owns the loop.

**Generics.** A def is typed once from its body and is generic in whatever
the body leaves open. When the body needs an operation on a generic value
(comparing, indexing, showing, calling a method), each call site supplies
that operation for its own types, so `def head(xs): xs[0]` works on `[1,
2]`, on `["a"]` and on a string. `fire --types` shows what a def needs.
Lambdas and nested defs share the types of the def they live in.

## 4. Pipelines

```fire
value |> f            # apply:  f(value)
list  *> f            # map
list  ?> pred         # filter
result !> handler     # recover from an error (§9)
```

The right-hand side either *is a function*, called with the piped value, or
*mentions `$`*, evaluated with `$` bound to the piped value:

```fire
5 |> double                  # 10
5 |> $ * 2                   # 10
5 |> "{$} things"            # "5 things"
[1, 2, 3] *> $ + 1           # [2, 3, 4]
[1, 2, 3] ?> $ % 2 == 1      # [1, 3]
```

Pipelines chain, and continue on indented lines that start with the
operator; method chains continue the same way with `.`. `print` returns its
first argument, so it works as a probe: `[1, 2, 3] *> $ * $ |> print |> sum`.
A builtin that takes one value can be a stage (`xs |> max`, `*> round`).

## 5. Data

### 5.1 Lists

A list has one element type: `[1, 2, 3]`, `["a"]`, `[]`. Values of
different types travel together in a record, never in a list.

`xs[i]` indexes (negative from the end) and aborts when out of range;
`xs[1..3]`, `xs[..2]` and `xs[-2..]` slice and clamp to the bounds.
Strings and ranges index and slice the same way (`(5..10)[1..3]` is
`6..8`). `xs.push(v)`, `xs.pop()` and `xs[i] = v` change the list (§7.1).

### 5.2 Records

```fire
node = {op: '+', left: 1, right: 2}
pair = {x, y}                           # shorthand for {x: x, y: y}
node.op                                 # a field
node.op = '-'                           # rebinds `node` to the changed record
```

Two records with the same field names and types have the same type. A
record's fields are read with `.name`; `node["op"]` is a dictionary lookup
and is not allowed on a record.

### 5.3 Dictionaries

`{}` is an empty dictionary: string keys, one value type, kept in key
order.

```fire
counts = {}
for word in words
    counts[word] = (counts[word] or 0) + 1

counts["a"]                       # T | nothing: nothing when absent
counts.has("a")                   # bool
counts.keys()                     # ['a', 'b', ...]
counts.entries()                  # [{key: 'a', value: 1}, ...]
for {key, value} in counts        # a loop goes through the entries
    print("{key}: {value}")
```

`m[k] = v` creates or updates an entry. An entry is the record `{key,
value}`: `e.key`, `{key, value} = e`, and `{key: k, value: v}` builds one.
`keys()`, `values()`, `entries()`, loops and printing all follow key order.

### 5.4 Declared types

Data with alternatives, or data that contains itself, is declared with
`type`, one constructor per line:

```fire
type Shape
    Circle(radius: float)
    Rect(width: float, height: float)

type Tree
    Leaf
    Node(left: Tree, value, right: Tree)

type Light
    Red
    Amber
    Green
```

A field without a type is a type parameter, so one `Tree` holds ints or
strings (inside its own declaration, `Tree` means the same type with the
same parameters). Constructors build values (`Node(Leaf, 3, Leaf)`, `Red`)
and take them apart in a `match` (§6.3). Values print as their constructors
(`Node(Leaf, 3, Leaf)`), compare structurally, and order by constructor in
declaration order. Everything else (records, objects, lists, dictionaries)
is inferred and needs no declaration.

### 5.5 Destructuring

Lists and records can be taken apart on the left of `=`, in parameters, as
loop targets and as match patterns:

```fire
[a, b] = [1, 2]
[first, ...rest] = [1, 2, 3]
{name, age} = person
{name: n} = person                 # rename
{key: k, value: v} = entry
```

## 6. Control flow

### 6.1 Conditionals

```fire
if x > 0
    print("positive")
elif x == 0
    print("zero")
else
    print("negative")

sign = if x > 0 do 1 elif x == 0 do 0 else -1    # as a value
```

Conditions are bools. `and`, `or` and `not` short-circuit; `x or default`
on a `T | nothing` replaces `nothing` with the default. `==` is structural
on every type. An `if` used as a value needs every branch, and assignments
inside its branches stay local to the branch; use the statement form to
update `var`s.

### 6.2 Loops

```fire
for i in 0..5 do print(i)          # ranges exclude their end
for [a, b] in rows do print(a + b) # a pattern takes each item apart
for {key, value} in counts         # a dictionary's entries
    print("{key}: {value}")
for i, x in 0.., ['a', 'b']        # lockstep: the shortest iterable ends it
    print("{i}: {x}")
for _ in 0..100                    # a bounded search
    if found() do break
```

A `for` runs over a list, a string, a dictionary or a range, and always
ends. A comma means lockstep: one target per iterable, all advancing
together. That is how to count items (`for i, x in 0.., xs`) and how to walk
two lists side by side (`for a, b in xs, ys`). An open range (`0..`) never
ends by itself, so it may only run beside a finite iterable.

`break`, `continue` and `return` work in loops. Each iteration has a fresh
scope, so a closure created in a loop captures that iteration's values;
assigning to an outer `var` from the loop body works.

`while cond` is the unbounded loop and is allowed only in an `unsafe def`
(§10). A loop that needs a bound usually has one: `for _ in 0..len(xs)`
with a `break` states it.

### 6.3 `match`

The arms are tried in order; the first whose pattern accepts the value
runs:

```fire
description = match point
    [0, 0] => "origin"
    [x, 0] if x > 0 => "positive x axis"      # a guard
    [x, ...rest] => "starts with {x}"
    {x, y} => "at {x}, {y}"
    other => "something else"
```

Literals match by equality, records by field names, lists by shape, a name
always matches and binds, and a constructor matches positionally
(`Node(l, v, r) =>`, `Leaf =>`). On a `T | nothing` use a `nothing` arm
beside value arms (`n =>`, `n: int =>`, or any pattern for the value). On a
result use `{ok}` and `{err}` arms.

A match whose arms cover every value is exhaustive. One that does not is
fallible: it aborts on the values it misses (§9), and `fire --check` lists
it with such a value (`line 18: no arm accepts Node(Node(_, _, _), _, _)`).
Coverage looks into every constructor field and list cell.

In statement position the arms need not agree on a type. As a value, arms
answering `nothing` and arms answering a `T` make a `T | nothing`. An arm's
body may be, or end in, `return`, `break` or `continue`; in a bound match,
the arms that fall through give the value:

```fire
for s in lines
    n = match s.parse_int()
        {ok} => ok
        {err} => continue
    total += n
```

### 6.4 Comprehensions

`for ... do` in value position builds a list, and an `if` before `do`
filters:

```fire
squares = for i in 1..6 do i * i             # [1, 4, 9, 16, 25]
evens   = for i in 0..10 if i % 2 == 0 do i  # [0, 2, 4, 6, 8]
labeled = for i, x in 0.., xs do "{i}: {x}"
```

## 7. Objects

A def that declares a `public` member is a **class**: calling it builds an
object with those members.

```fire
def Counter(start = 0)
    public var count = start              # a data member
    public increment = () => count += 1   # a method: members are locals
    public get = () => count

var c = Counter()
c.increment()
print(c.count)    # 1
print(c)          # Counter{count: 1}
```

* Everything not `public` is private: visible to the methods, nothing else.
  A private function that a method calls is a method too, so the
  constructor body may call it only after every member is declared.
* `public` parameters are members: `def Todo(public title, public var done
  = false)` is a complete class.
* Methods call each other by bare name; `self.name(...)` means the same.
  A class returns its object; `return self` is allowed, `return x` is not.
* Printing an object shows its public data members in declaration order,
  and `==` compares them. Methods are neither printed nor compared.

### 7.1 Changing values

An object is a value. A method that assigns to a member returns the
rebuilt object, and calling it as a statement rebinds its receiver, which
must therefore be a `var` (or a binding the call creates). Nothing is
shared:

```fire
var a = Counter()
b = a               # a copy
a.increment()
print(a.count, b.count)    # 1 0
```

A changing method that also answers a value does both: `x = stack.pop()`
rebinds `stack` and binds `x`. A method that calls a changing method on
itself, a member or its parent is changing too. Lists and dictionaries work
the same way: `xs.push(v)`, `xs.pop()` and `m[k] = v` rebind the binding
they apply to, including a parameter or a member. Writes reach through
indexes and members: `rows[r][c] = v`, `d[k].push(v)`, `xs[i].name = v`.
Calling a changing method on a temporary (`Counter().increment()`) just
drops the result.

A change runs where its value is evaluated: on the right of `and`/`or` only
when the left side does not decide, in an `if` value only in the branch
taken, and in a comprehension on every pass. Two places are errors, since
they would run a change a different number of times than written: the
right side of an `or` whose left side has a generic type (it may be a
logical `or` or a default), and a `while` condition. Move the change into
its own statement.

**A change nothing reads is an error**: changing a loop's copy of an
element (`for p in pts` with `p.x = 0` in the body), a parameter the def
neither returns nor reads again, or any binding not read afterwards. Change
the list through its index (`pts[i].x = 0`), return the changed value, or
make the def a method.

### 7.2 Inheritance

`self.{...} = parent` adopts every public member of `parent`, into the
object and into scope:

```fire
def Animal(public name)
    public speak = () => "{name} makes a sound"

def Dog(name)
    parent = Animal(name)
    self.{...} = parent
    public speak = () => parent.speak() + " Woof!"

Dog("Rex").speak()    # Rex makes a sound Woof!
```

Overriding is declaring the name again after the adoption. The parent is an
ordinary value stored in the child: inherited members resolve through it,
an inherited changing method rebuilds the child, and printing and `==`
include the inherited data members.

### 7.3 Custom operators

A public member named after an arithmetic operator, in backticks, defines
it for the class. The left operand decides:

```fire
def Vec(public x = 0.0, public y = 0.0)
    public `+` = other => Vec(x + other.x, y + other.y)
    public `*` = k => Vec(x * k, y * k)

v = Vec(3.0, 4.0) + Vec(1.0, 2.0)    # Vec{x: 4.0, y: 6.0}
w = v * 2.0
```

The operators `+ - * / % **` can be defined; comparison, logic and pipeline
operators cannot.

## 8. Types

Types are inferred Hindley-Milner style; a program that mixes types in a
binding or a list is rejected.

| type | notes |
|---|---|
| `int` | 32-bit signed, wraps on overflow |
| `float` | 32-bit |
| `str` | text |
| `bool` | `true`, `false` |
| `nothing` | the unit value |
| `[T]` | list |
| `{}` | dictionary: `str` keys, one value type |
| record | named fields; an object is a record |
| `fn(A, B) -> R` | function |
| `T \| nothing` | a value that may be absent |
| result | `{ok: T}` or `{err: E}` (§9) |
| range | `a..b` |
| declared | `type Name` (§5.4) |

**Numbers.** Ints and floats do not mix: `n + 0.5` with `n` an int is an
error; convert with `float(x)` and `int(x)`. An int *literal* adapts to a
float context (`1 + 2.5` is `3.5`). Int `/` rounds toward negative
infinity, `%` is Euclidean (`-7 % 3` is `2`), and division by zero yields
`0`. `**` is a power on ints and on floats. Ints also have `& | ^`, the
shifts `<<`, `>>` (keeps the sign) and `>>>` (shifts in zeros), and the
matching compound assignments (`x ^= x << 13`). Between two values `|` is
bitwise or; between types it is a union.

**Absent values.** A lookup that can miss answers `T | nothing`: `m[k]`,
`xs.first()`, `xs.last()`, `xs.find(f)`, `xs.index_of(x)`,
`s.index_of(t)`, and any function, `if` or `match` that answers `nothing`
on one path and a value on another. Such a value must be matched or
defaulted (`x or default`) before it is used as a `T`. A list or
dictionary of `T | nothing` takes plain values and `nothing` alike
(`[nothing, 5]`, `parent[i] = j`).

**Conversions.** `str(x)`, `int(x)` and `float(x)` convert.
`"7".to_int()` aborts on bad text; `"7".parse_int()` answers a result.

## 9. Effects and errors

Effects are inferred; nothing is written differently at a call site.

* A function that prints or uses `$io` is **IO**.
* A function that can abort is **fallible**: `error(msg)`, `assert`,
  out-of-range indexing, `{ok} = r` on an err, `to_int` on bad text, a
  match that is not exhaustive, or a call to a fallible function.
* Everything else is **pure**.

An abort stops the program with a message that names its line (`line 4:
list index 2 out of range for length 2`).

Expected failures are **results**, `{ok: value}` or `{err: payload}`, and
pipelines carry them:

* `|>`, `*>` and `?>` unwrap an `ok` into the stage, and skip the stage for
  an `err`, passing it along.
* `!>` runs only for an `err` and rejoins the happy path. Its right-hand
  side follows the pipeline rule, or is a plain value (`!> 8080`); either
  way it answers the pipeline's ok type.
* Over a list of results, `*>` and `?>` work per element.

```fire
["1", "2", "oops", "4"]
    *> $.parse_int()     # [{ok: 1}, {ok: 2}, {err: ...}, {ok: 4}]
    *> $ * 10            # oks unwrap, errs pass
    !> -1                # [10, 20, -1, 40]

match "7".parse_int()
    {ok} => print("parsed {ok}")
    {err} => print("failed: {err}")

{ok} = must_work()       # unwrap, or abort
```

The builtins that answer results are `$io.read_file`, `$io.write_file`,
`str.parse_int` and `str.parse_float`.

## 10. Totality

Every def is seen to terminate, or is declared `unsafe def`. The compiler
accepts:

* **Loops**: `for` over a list, string, dictionary or range.
* **Structural recursion**: a self-call on a piece of a parameter bound by
  a `match` on it (`[h, ...t]` binds `t`; `Node(l, v, r)` binds `l` and
  `r`). Parameters may take turns, left to right: `merge(xs, b)` and
  `merge(a, ys)` descend on `a`, or keep `a` and descend on `b`.
* **Counting down an int**: a self-call on `n - k` (`k` a positive literal)
  or `n / k` (`k ≥ 2`) under a guard that keeps `n` at least `k` (`if n <=
  1 do return ...`). `fib(n - 1) + fib(n - 2)` under `if n <= 1` is
  accepted; `f(n - 1)` under `if n == 0` is not, since `n` may be negative.

Anything else is rejected with the rule it misses: recursion on a filtered
list, `gcd(b, a % b)`, a self-call inside a loop body, a def passing itself
as a function (`kids *> depth` inside `depth`), and mutual recursion (merge
the defs into one). A tree whose children are a list is walked by a def
over the list of trees:

```fire
type Rose
    Node(value: int, kids: [Rose])

def total(ts)
    match ts
        [] => 0
        [Node(v, kids), ...rest] => v + total(kids) + total(rest)
```

When termination is a theorem beyond these rules, the def says so:

```fire
unsafe def gcd(a, b)               # Euclid's remainders shrink, but not by a literal step
    if b == 0 do a else gcd(b, a % b)

unsafe def collatz_steps(n)        # nobody has proven this ends
    var steps = 0
    var v = n
    while v != 1
        v = if v % 2 == 0 do v / 2 else 3 * v + 1
        steps += 1
    steps
```

`unsafe def` skips the termination check for that def and allows `while`
in it. It stays visible: `fire --types` tags every def that is or calls
unsafe code, `fire --check` lists them, and `fire --total` rejects a
program that has any. A match that is not exhaustive is fallible, not
unsafe: it aborts with a message.

## 11. Laws

A law states a property of the program's defs, next to them:

```fire
law small_tree                              # closed: no variables
    to_list(from_list([3, 1, 2])) == [1, 2, 3]

law cycle_of_three                          # over a finite type
    for l: Light
    next_light(next_light(next_light(l))) == l

law insert_contains                         # over an infinite type
    for x: int, t: Tree
    contains(insert(x, t), x)

law insert_keeps_sorted                     # with a hypothesis
    for x: int, t: Tree if is_sorted(t)
    is_sorted(insert(x, t))
```

`for` names the variables with their types (the one place a value's type
is written, since a law ranges over a type) and `if` adds a hypothesis. A
type parameter left open is `int`: `for t: Tree` is a tree of ints. The
body is an equation (`a == b`, structural) or a bool. A law may use pure
and fallible defs, but no IO or unsafe ones and no top-level values.

| law | proven by | when |
|---|---|---|
| closed (no `for`) | Bend computes both sides | every build: a false law fails it |
| every variable of a finite type (`bool`, a type of nullary constructors), no hypothesis | a case split, each case computed | every build |
| anything else | an open claim | `fire --check` reports it; `fire --test` samples it |

`fire --test` checks every law on generated values (ints, floats, strings,
bools, lists, and every declared type up to a small depth) and reports the
first counterexample. An open law can be proven in Bend: `fire --check
prog.fire` appends `prog.proof.bend` when it exists, where a def named
after the law proves it against the compiled program (`def nil_append(xs):
{==}`).

## 12. Modules and builtins

A `$name` is a builtin module; use its members directly or destructure
them:

```fire
{sqrt, pi} = $math
print(sqrt(2.0) * pi)
text = $io.read_file("data.txt") !> ""
```

| module | members |
|---|---|
| `$math` | `pi e tau inf`, `sqrt sin cos tan asin acos atan atan2 exp log(x, base?) log2 log10 floor ceil abs pow min max` (floats) |
| `$strings` | `join(list, sep?) char_code(c) from_char_code(n)` |
| `$lists` | `flatten(xs) repeat(v, n)` |
| `$io` | `read_file(path) write_file(path, text)`, both answering results |
| `$time` | `now()` |

**Global functions**: `print(x, ...)` (answers its first argument), `len`,
`sum`, `min`, `max` (of a list, or of two values), `abs`, `round(x,
digits?)`, `sorted(xs, key?)`, `reversed`, `range(end)`, `range(start,
end)`, `error(msg)`, `assert(cond, msg?)`, `str`, `int`, `float`.

| on | methods |
|---|---|
| lists | `length map filter each reduce(f, seed?) any all find count sum min max join(sep) contains index_of first last reverse reversed sort(key?) sorted(key?) push(x, ...) pop drop_last take drop is_empty flatten to_list` |
| strings | `length upper lower trim trim_start trim_end split(sep?) lines replace(from, to) contains starts_with ends_with index_of chars repeat(n) reverse join(list) take drop is_empty to_int to_float parse_int parse_float char_code to_str` |
| numbers | `abs floor ceil round(digits?) sqrt to_str to_int to_float` |
| dictionaries | `keys values entries has(k) get(k) set(k, v) remove(k) length` |
| ranges | `to_list map filter each reduce sum min max length first last contains take drop reversed` |

`sorted` and `sort` order ints, floats, strings, lists, records (field by
field) and ranges. With a key they are stable, and the key may be fallible
or print.

## 13. Operator precedence

From loosest to tightest:

| level | operators |
|---|---|
| pipelines | `\|>` `*>` `?>` `!>` |
| lambda | `=>` (its body stops before a pipeline operator) |
| comprehension | `for … do`, inline `if … do … else` |
| logic | `or`, then `and`, then `not` |
| comparison | `==` `!=` `<` `<=` `>` `>=` |
| bits | `\|`, then `^`, then `&` |
| range | `..` |
| shifts | `<<` `>>` `>>>` |
| arithmetic | `+` `-`, then `*` `/` `%`, then unary `-`, then `**` |
| annotation | `:` |
| access | `.member` `f(args)` `xs[i]` |

## 14. Not supported

These are rejected with a message:

* importing other files;
* runtime type tests (`type(x)`, or `x: int` outside a `T | nothing`
  match), `?.`, and `[]` on a record;
* interpolating strings as patterns or assignment targets;
* list spread (`[...xs, 1]`; write `xs + [1]`) and type aliases;
* `while` outside an `unsafe def`, and a `for` over an open range alone;
* mutual recursion, a self-call inside a loop body, and a def passing
  itself as a function in its own body;
* a change nothing reads (§7.1);
* `return`, `break` or `continue` inside a larger expression (bind the
  value first);
* a `!>` handler whose value differs in type from the ok value;
* function values whose environment holds a function of the same kind
  (`compose(f, compose(g, h))`).
