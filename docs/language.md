# The Fire language

Fire is a small, expression-oriented, indentation-based language. Programs are
statically typed with full inference, values are immutable data, effects are
inferred, and everything compiles to Bend 2. This is the reference.

## 1. Lexical structure

```fire
# a comment
## a documentation comment (attaches to the following definition)

x = 42            # int
y = 3.14          # float
z = 1.2e-3        # scientific
h = 0xFF          # hex
b = 0b1011        # binary
s = 'raw text'    # plain string: no interpolation, no escapes
f = "x is {x}"    # f-string: `{expr}` interpolates, `\n` `\t` `\\` escape
t = `verbatim`    # raw string, backticks
ok = true         # bool
n = nothing       # the unit value
```

An interpolation takes an optional format spec: `{value:[fill][align][width][.precision f]}`
with align `<` `>` `^`. Numbers pad on the left, text on the right:

```fire
"{price:.2f} €"       # 3.50 €
"[{total:8.2f}]"      # [    3.50]
"{name:<8}|{n:>5}"    # columns
"{'ada':*^9}"         # ***ada***
```

Blocks are introduced by indentation, never by a colon; a comment may close
the header line (`def f(x)  # doubles`). A multi-line expression continues
on lines that *start* with an operator (`|>`, `.`, `+`, `and`, ...). List
and record literals and the arguments of a call may span indented lines;
commas are then optional.

Identifiers are `[A-Za-z_][A-Za-z0-9_]*`. Reserved: `def return public var
if elif else for in while break continue match not and or do true false
nothing async await`.

## 2. Bindings

```fire
x = 1             # immutable
var y = 2         # mutable
y = 3             # ok
y += 1            # compound assignment needs var
x = 4             # error: cannot reassign immutable binding
a = b = 5         # chained: evaluates once, binds both
```

A binding holds a value, and every binding has one static type, inferred
from its uses. Rebinding a `var` to a different type is an error. Type
annotations are checked, never required:

```fire
age: int = 30
def area(w: float, h: float): float
    w * h
names: [str] = []                    # a list type is [T]
counts: {} = {}                      # a dictionary
def greet(p: {name: str, age: int})  # a record type lists its fields
    "hi {p.name}"
```

Rebinding never affects another binding that received the same value:
values are copied, not shared (§4.2).

## 3. Functions

### Lambdas and defs

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

`return` exits a function early. Parameters take defaults (`=`),
annotations (`:`) and destructuring patterns (`{age} => age + 1`). A lambda
body stops before a pipeline operator: in `xs ?> n => n > 2 |> sum` the
lambda is `n => n > 2`; parenthesize to change that.

Calls take keyword arguments: positional first, then `name = value` in any
order. Only defs and lambdas take keywords; builtins are positional.

```fire
def box(width = 1, height = 2, depth = 3)
    width * height * depth

box(depth = 10)          # 20
box(4, depth = 10)       # 80
```

### Closures

A lambda or nested def captures the *values* its free variables have when it
is created. Assigning to a captured variable from inside a lambda is a
compile error; state that changes lives in objects (§4) or in `var`s of the
function that owns the loop.

### Polymorphism

A def is typed once from its body. Where the body does not constrain a
parameter, the def is generic; where it does (the parameter is indexed,
compared, or given to a method), the def is re-inferred as a copy for each
argument type it is called with, so `def head(xs): xs[0]` works on
`[1, 2]` and on `["a"]`. Lambdas are never generalized.

Functions are values: pass them, return them, store them in lists and
records, call them any number of times.

## 4. Objects: `def` with `public`

A def whose body (or parameter list) declares a `public` member is a
**constructor**: calling it builds an object with those members.

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

* Everything not `public` is private state, visible to the methods only. A
  private function that a method calls is a method too; like any method it
  sees the whole object, so the constructor body can only call it once every
  member is declared.
* `public` parameters declare members directly: `def Todo(public title,
  public var done = false)` is a complete constructor.
* Methods call their siblings by bare name (`fact(n - 1)`); `self.fact(...)`
  means the same. `self` is otherwise only needed for `self.{...}` (§4.3).
* A constructor returns its object; `return self` is allowed, `return x` is
  not.

### 4.1 Namespaces

Accessing a member on the def itself instantiates it once (its parameters
must all have defaults):

```fire
def Math
    public def fib(n)
        if n <= 1 do 1 else fib(n - 1) + fib(n - 2)

print(Math.fib(6))    # 13
```

### 4.2 Objects are values

An object is a record. A method that assigns to a member returns the
rebuilt object, and calling such a method in statement position rebinds its
receiver, so the receiver must be a `var` (or a fresh binding created by the
call). Nothing is shared: two bindings holding "the same" object are two
copies, and mutating one leaves the other alone.

```fire
var a = Counter()
b = a               # a copy
a.increment()
print(a.count, b.count)    # 1 0
```

A mutating method that also returns a value does both:
`x = stack.pop()` rebinds `stack` and binds `x`. A method that calls a
mutating method on `self`, on a member, or on its parent counts as mutating
too. Calling a mutating method on a temporary (`Counter().increment()`) is
allowed; the result is dropped. The same holds for lists and dictionaries:
`xs.push(v)`, `xs.pop()` and `m[k] = v` rebind the binding they are applied
to (any binding, `var` or not) and no other. That includes a parameter, a
member, and a lambda whose whole body is the mutation (`public add = v =>
items.push(v)`); a lambda that pushes onto its *own* parameter answers the
extended list instead, since nothing outside could see the rebinding.
Writes go through any chain of indexes and members: `rows[r][c] = v`,
`d[k].push(v)`, `xs[i].name = v`.

Printing an object shows its public data members in declaration order;
`==` compares them structurally. Methods are neither printed nor compared.

### 4.3 Inheritance

`self.{...} = parent` adopts all public members of `parent` into the object
being built, and into scope:

```fire
def Animal(public name)
    public speak = () => "{name} makes a sound"

def Dog(name)
    parent = Animal(name)
    self.{...} = parent
    public speak = () => parent.speak() + " Woof!"

Dog("Rex").speak()    # Rex makes a sound Woof!
```

Overriding is redeclaring the name after the adoption; the parent is an
ordinary value you keep a reference to. The parent object is stored inside
the child (the binding named in the statement), inherited members resolve
through it, and an inherited method that mutates rebuilds the child.
Printing and `==` include the inherited data members.

### 4.4 Custom operators

A public member named after an arithmetic operator, in backticks, overloads
it for instances of the def. The left operand decides:

```fire
def Vec(public x = 0.0, public y = 0.0)
    public `+` = other => Vec(x + other.x, y + other.y)
    public `*` = k => Vec(x * k, y * k)

v = Vec(3.0, 4.0) + Vec(1.0, 2.0)    # Vec{x: 4.0, y: 6.0}
w = v * 2.0
```

Overloadable: `+ - * / % **`. Comparison, logic and pipeline operators are
fixed.

### 4.5 Dictionaries

`{}` is an empty dictionary: string keys, one value type, ordered by key.

```fire
counts = {}
for word in words
    counts[word] = (counts[word] or 0) + 1

counts["a"]                       # T | nothing: nothing when absent
counts.has("a")                   # bool
counts.keys()                     # ['a', 'b', ...] in key order
for [k, v] in counts.entries()    # entries are [key, value] pairs
    print("{k}: {v}")
```

`m[k] = v` creates or updates an entry. `keys()`, `values()`, `entries()`,
iteration and printing follow key order, not insertion order.

### 4.6 Records

A record literal is an object with named fields; a bare name is shorthand
for `name: name`:

```fire
node = {op: '+', left: 1, right: 2}
{op, left} = node                       # destructure
pair = {x, y}                           # {x: x, y: y}
node.op                                 # field access
```

Two records with the same field names and types have the same type. Fields
are read with `.name` and assigned with `node.op = '-'` (the record is a
value, so the binding holding it rebinds); `node["op"]` is not allowed on a
record (it is the dictionary lookup).

## 5. Pipelines

```fire
value |> f            # apply:  f(value)
list  *> f            # map
list  ?> pred         # filter
```

The right-hand side either *is a function* (then it is called with the
piped value) or *mentions `$`* (then it is evaluated with `$` bound to it):

```fire
5 |> double                  # 10
5 |> $ * 2                   # 10
5 |> "{$} things"            # "5 things"
[1, 2, 3] *> $ + 1           # [2, 3, 4]
[1, 2, 3] ?> $ % 2 == 1      # [1, 3]
```

Pipelines chain, and continue on indented lines starting with the operator.
Method chains continue the same way with `.`.

`print` returns its argument, so it works as a probe inside a pipeline:
`[1, 2, 3] *> $ * $ |> print |> sum`.

**Streams.** An open range (`1..`) is an unbounded sequence; `*>` and `?>`
over one are lazy, and items are computed only when a finite prefix is
consumed: `.take(n)`, `.drop(n)`, `.first()`, indexing, or a `for` loop
that `break`s.

```fire
squares = 1.. *> $ * $ |> $.take(5)     # [1, 4, 9, 16, 25]
evens = 0.. ?> $ % 2 == 0
print(evens.drop(3).take(3))            # [6, 8, 10]
```

A stream must be consumed in the expression that builds it, or bound to a
name that is used once; it cannot be stored in a container or passed to a
function.

## 6. Destructuring

Lists and records can appear on the left of `=`, in parameters, as loop
targets and as match patterns:

```fire
[a, b] = [1, 2]
[first, ...rest] = [1, 2, 3]
{name, age} = person
{name: n} = person                 # rename
[k, v] = entry                     # a dictionary entry
```

## 7. Control flow

```fire
if x > 0
    print("positive")
elif x == 0
    print("zero")
else
    print("negative")

if x > 0 do print("positive")      # one-line body with `do`
sign = if x > 0 do 1 elif x == 0 do 0 else -1   # if as an expression

while x < 10
    x += 1

for i in 0..5 do print(i)          # ranges are end-exclusive
for [a, b] in pairs do print(a + b)
for k, v in counts.entries()       # comma targets destructure
    print("{k}: {v}")
for i, x in 0.., ['a', 'b']        # several iterables zip; an open range counts
    print("{i}: {x}")
for n in 1..                       # an open range iterates lazily
    if n * n > 50 do break
```

`break` and `continue` work in loops. Every iteration runs in a fresh
scope; a closure created inside a loop captures that iteration's values.
Reassigning an outer `var` from inside a loop works.

Conditions are bools. `and`, `or` and `not` work on bools and
short-circuit; `x or default` on a `T | nothing` (§8) replaces `nothing`
with the default. `==` is structural on everything.

An `if` used as an expression must produce a value in every branch, and
assignments inside its branches stay local to the branch; use the statement
form to update `var`s.

### `match`

Arms are lambdas; the first whose pattern accepts the value runs:

```fire
description = match point
    [0, 0] => "origin"
    [x, 0] if x > 0 => "positive x axis"      # a guard
    [x, ...rest] => "starts with {x}"
    {x, y} => "at {x}, {y}"
    other => "something else"
```

Literals match by equality, records by field names, lists by shape, an
identifier always matches and binds. A match on a `T | nothing` value uses
a `nothing` arm and a value arm (`n =>` or `n: int =>`); on a result it
uses `{ok}` and `{err}` arms. A match whose arms cover every case is
exhaustive and cannot fail; one that does not is fallible (§9). In
statement position the arms need not share a type.

### Comprehensions

`for x in xs do body` in expression position builds a list; an `if` without
`else` filters:

```fire
squares = for i in 1..6 do i * i             # [1, 4, 9, 16, 25]
evens   = for i in 0..10 if i % 2 == 0 do i  # [0, 2, 4, 6, 8]
labeled = for i, x in 0.., xs do "{i}: {x}"
```

## 8. Types

Every expression has one type, inferred Hindley-Milner style; a program
that mixes types in a binding or a list is rejected at compile time.

| type | notes |
|---|---|
| `int` | 32-bit, wraps on overflow |
| `float` | 32-bit |
| `str` | text |
| `bool` | `true` / `false` |
| `nothing` | the unit value |
| `[T]` | list, one element type |
| `{}` dictionary | `str` keys, one value type |
| record | named fields (§4.6); a class instance is a record |
| `fn(A, B) -> R` | functions |
| `T \| nothing` | a value that may be absent |
| result | `{ok: T}` or `{err: E}` (§9) |
| range, stream | `a..b`, and lazy `*>`/`?>` over an open range |

Ints and floats do not mix: `n + 0.5` with `n` an int is an error; convert
with `float(x)` and `int(x)`. Only an int *literal* adapts to a float
context (`1 + 2.5` is `3.5`). Int `/` rounds toward negative infinity and `%`
is Euclidean (`-7 % 3` is `2`); division by zero yields `0`. `**` on ints
is an int power; on floats the exponent must be an integer literal
(otherwise use `$math.pow`). Ints also have the bit operations `& | ^`,
the shifts `<< >>` (`>>` keeps the sign) and `>>>` (shifts in zeros), and
the matching compound assignments (`x ^= x << 13`). Between two values `|`
is bitwise or; between types (`int | nothing`) it is a union.

**Absent values.** `xs[i]` on a list aborts when out of range, but a
lookup that can miss has type `T | nothing`: `m[k]`, `xs.first()`,
`xs.last()`, `xs.find(f)`, `xs.index_of(x)`, `s.index_of(t)`, and a function
that returns `nothing` on one path and a value on another. Such a value
must be matched or defaulted (`x or default`) before it is used as a `T`;
`.member` on it is a type error.

`str(x)`, `int(x)`, `float(x)` convert; `"7".to_int()` aborts on bad text,
`"7".parse_int()` returns a result.

## 9. Effects and errors

Effects are inferred, and nothing is written differently at a call site.

* A function that prints or uses `$io` is an **IO** function.
* A function that can abort is **fallible**: `error(msg)`, `assert`,
  out-of-range indexing, `{ok} = ...` on an err, `to_int` on bad text, a
  non-exhaustive match, or a call to another fallible function.
* Everything else is **pure**.

An abort stops the program with a message. Expected failures are
**results**, `{ok: value}` or `{err: payload}`, and the pipeline carries
them:

* `|>`, `*>`, `?>` unwrap an `ok` into the stage and skip the stage
  entirely for an `err`, passing it along.
* `!>` runs only for an `err` and rejoins the happy path. Its right-hand
  side follows the pipeline rule, or is a plain recovery value
  (`!> 8080`). The handler's value must have the pipeline's ok type.
* Inside `*>`/`?>` over a list of results the railway is per element.

```fire
["1", "2", "oops", "4"]
    *> $.parse_int()     # [{ok: 1}, {ok: 2}, {err: ...}, {ok: 4}]
    *> $ * 10            # oks unwrap, errs skip
    !> -1                # [10, 20, -1, 40]

match "7".parse_int()
    {ok} => print("parsed {ok}")
    {err} => print("failed: {err}")

{ok} = must_work()       # unwrap, or abort
```

Fallible builtins: `$io.read_file`, `$io.write_file`, `str.parse_int`,
`str.parse_float`.

## 10. Modules

`$name` is a builtin module; destructure what you need:

```fire
{sqrt, pi} = $math
print(sqrt(2.0) * pi)
text = $io.read_file("data.txt") !> ""
```

* `$math`: `pi e tau inf`, `sqrt sin cos tan asin acos atan atan2 exp
  log(x, base?) log2 log10 floor ceil abs pow min max` (all on floats).
* `$strings`: `join(list, sep?)`, `char_code(c)`, `from_char_code(n)`.
* `$lists`: `zip(a, b)`, `enumerate(xs)`, `flatten(xs)`, `repeat(v, n)`.
* `$io`: `read_file(path)`, `write_file(path, text)`, both results.
* `$time`: `now()`.

## 11. Builtins

**Global**: `print(x, ...)` (returns its argument), `len`, `sum`, `min`,
`max` (a list, or two scalars), `abs`, `round(x, digits?)`, `sorted(xs,
key?)`, `reversed`, `range(end)` / `range(start, end)`, `error(msg)`,
`assert(cond, msg?)`, `str`, `int`, `float`.

**Lists**: `length map filter each reduce(f, seed?) any all find count sum
min max join(sep) contains index_of first last reverse reversed sort(key?)
sorted(key?) push(x, ...) pop drop_last take drop is_empty flatten enumerate
zip(other) to_list`. Indexing: `xs[i]` (negative from the end), slices
`xs[1..3]`, `xs[..2]`, `xs[-2..]`; strings and ranges index and slice the
same way (`(5..10)[1..3]` is `6..8`).

**Strings**: `length upper lower trim trim_start trim_end split(sep?) lines
replace(from, to) contains starts_with ends_with index_of chars repeat(n)
reverse join(list) take drop is_empty to_int to_float parse_int parse_float
char_code to_str`.

**Numbers**: `abs floor ceil round(digits?) sqrt to_str to_int to_float`.

**Dictionaries**: `keys values entries has(k) get(k) set(k, v) remove(k)
length`.

**Ranges**: `to_list map filter each reduce sum min max length first last
contains take drop reversed`. **Streams**: `take drop first`.

`sorted` and `sort` order ints, floats, strings, lists and records
(field by field); with a key they are stable, and the key may itself be
fallible or print.

## 12. Operator precedence

Loosest to tightest:

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

## 13. Not supported

These are rejected with a message: `async`/`await`; importing other files;
f-string destructuring and f-string match patterns; runtime type values
(`type(x)`, `x: int` as a runtime test outside a `T | nothing` match);
`?.`; `[]` on a record; `while … do` comprehensions and nested
comprehension clauses; a `!>` handler whose value has a different type
than the ok value; a block used as a value that branches (move the branch
into a def or an if-expression); mutual recursion between defs, and
function values whose environment holds a function of the same kind
(`compose(f, compose(g, h))`).
