# Fire runtime prelude, emitted at the top of every compiled program (see docs/compiler.md).
# Everything the generated code calls that Bend's Base does not provide: the
# loop drivers, the case eliminators, the derived operations of the builtin
# types, and the string, number, list and map helpers behind Fire's builtin
# methods. Helpers precede their callers; `+` marks reusable values. The
# compiler keeps only the blocks a program reaches.
# -- Core types ---------------------------------------------------------------
# The record {key, value}: dictionary entries, and the pairs that pop and
# lockstep loops pack.

type F.Pair<-A: Data, -B: Data> is Data:
  F.Pair{key: A, value: B}

# A range `a..b`: the end is exclusive.
type F.Range is Data:
  F.Range{start: U32, end: U32}

# What one turn of a loop body answers: go on with a state, leave the loop
# with a state, or return from the enclosing def with a value.
type F.Ctl<-S: Data, -R: Data> is Data:
  F.Next{s: S}
  F.Break{s: S}
  F.Return{r: R}

# -- Generic helpers ----------------------------------------------------------
def F.fst(-A: Data, -B: Data, p: A & B) -> A:
  (a, b) = p
  a

def F.snd(-A: Data, -B: Data, p: A & B) -> B:
  (a, b) = p
  b

# an abort inside IO ends the program with the message
def F.io_unwrap(-A: Data, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Done{v}:
      IO.pure(A, v)
    case Fail{e}:
      IO.die(A, 1, e)

# A failure where it happens, with the source line before its message.
def F.at(-A: Data, line: String, r: Result<&2, &2, String, A>) -> Result<&2, &2, String, A>:
  match r:
    case Done{v}:
      Done{v}
    case Fail{e}:
      Fail{line ++ e}

def F.assert.k(msg: String, c: Bool) -> Result<&2, &2, String, Unit>:
  match c:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{msg}

def F.assert(c: Bool, msg: String) -> Result<&2, &2, String, Unit>:
  F.assert.k(msg, c)

# -- Loop control -------------------------------------------------------------
# After a loop: continue with the returned value, or with the final state.
def F.ctl.case(-S: Data, -R: Data, -T: Data, c: F.Ctl<S, R>, kr: R -> T, ks: S -> T) -> T:
  match c:
    case F.Next{s}:
      ks(s)
    case F.Break{s}:
      ks(s)
    case F.Return{r}:
      kr(r)

# the final state of a loop that cannot return (`d` is never reached)
def F.ctl.state(-S: Data, -R: Data, c: F.Ctl<S, R>, d: S) -> S:
  match c:
    case F.Next{s}:
      s
    case F.Break{s}:
      s
    case F.Return{r}:
      d

# -- Loop drivers -------------------------------------------------------------
# A `for` over a list is a fold of the body over the elements, stopping at
# the first Break or Return. The body is a template (code) with an
# environment value; the state is whatever the loop updates.
def F.for_list(~S: Data, ~R: Data, ~A: Data, ~E: Data, ~body: E -> S -> A -> F.Ctl<S, R>, +env: E, xs: List<&2, A>, c: F.Ctl<S, R>) -> F.Ctl<S, R>:
  match xs:
    case Nil{}:
      c
    case Con{+h, t}:
      match c:
        case F.Next{+s}:
          F.for_list(~S, ~R, ~A, ~E, ~body, env, t, body(env, s, h))
        case F.Break{s}:
          F.Break{s}
        case F.Return{r}:
          F.Return{r}

def F.for_list_res(~S: Data, ~R: Data, ~A: Data, ~E: Data, ~body: E -> S -> A -> Result<&2, &2, String, F.Ctl<S, R>>, +env: E, xs: List<&2, A>, c: F.Ctl<S, R>) -> Result<&2, &2, String, F.Ctl<S, R>>:
  match xs:
    case Nil{}:
      Done{c}
    case Con{+h, t}:
      match c:
        case F.Next{+s}:
          do Result<&2, &2, String, F.Ctl<S, R>>:
            c2 : F.Ctl<S, R> <- body(env, s, h)
            F.for_list_res(~S, ~R, ~A, ~E, ~body, env, t, c2)
        case F.Break{s}:
          Done{F.Break{s}}
        case F.Return{r}:
          Done{F.Return{r}}

def F.for_list_io(~S: Data, ~R: Data, ~A: Data, ~E: Data, ~body: E -> S -> A -> IO(F.Ctl<S, R>), +env: E, xs: List<&2, A>, c: F.Ctl<S, R>) -> IO(F.Ctl<S, R>):
  match xs:
    case Nil{}:
      IO.pure(F.Ctl<S, R>, c)
    case Con{+h, t}:
      match c:
        case F.Next{+s}:
          do IO<F.Ctl<S, R>>:
            c2 : F.Ctl<S, R> <- body(env, s, h)
            F.for_list_io(~S, ~R, ~A, ~E, ~body, env, t, c2)
        case F.Break{s}:
          IO.pure(F.Ctl<S, R>, F.Break{s})
        case F.Return{r}:
          IO.pure(F.Ctl<S, R>, F.Return{r})

# A `for` over a range counts a Nat down; the body sees the current index.
def F.for_range.go(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> F.Ctl<S, R>, +env: E, n: Nat, +i: U32, c: F.Ctl<S, R>) -> F.Ctl<S, R>:
  match n:
    case 0n:
      c
    case 1n+p:
      match c:
        case F.Next{+s}:
          F.for_range.go(~S, ~R, ~E, ~body, env, p, (i + 1 : U32), body(env, s, i))
        case F.Break{s}:
          F.Break{s}
        case F.Return{r}:
          F.Return{r}

def F.i32.gt(a: U32, b: U32) -> Bool:
  U32.is_gt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.min.k(+a: U32, +b: U32, lt: Bool) -> U32:
  match lt:
    case True{}:
      a
    case False{}:
      b

def F.i32.max(+a: U32, +b: U32) -> U32:
  F.i32.min.k(a, b, F.i32.gt(a, b))

def F.for_range(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> F.Ctl<S, R>, +env: E, r: F.Range, c: F.Ctl<S, R>) -> F.Ctl<S, R>:
  match r:
    case F.Range{+s, e}:
      F.for_range.go(~S, ~R, ~E, ~body, env, U32.to_nat(F.i32.max((e - s : U32), 0)), s, c)

def F.for_range_res.go(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> Result<&2, &2, String, F.Ctl<S, R>>, +env: E, n: Nat, +i: U32, c: F.Ctl<S, R>) -> Result<&2, &2, String, F.Ctl<S, R>>:
  match n:
    case 0n:
      Done{c}
    case 1n+p:
      match c:
        case F.Next{+s}:
          do Result<&2, &2, String, F.Ctl<S, R>>:
            c2 : F.Ctl<S, R> <- body(env, s, i)
            F.for_range_res.go(~S, ~R, ~E, ~body, env, p, (i + 1 : U32), c2)
        case F.Break{s}:
          Done{F.Break{s}}
        case F.Return{r}:
          Done{F.Return{r}}

def F.for_range_res(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> Result<&2, &2, String, F.Ctl<S, R>>, +env: E, r: F.Range, c: F.Ctl<S, R>) -> Result<&2, &2, String, F.Ctl<S, R>>:
  match r:
    case F.Range{+s, e}:
      F.for_range_res.go(~S, ~R, ~E, ~body, env, U32.to_nat(F.i32.max((e - s : U32), 0)), s, c)

def F.for_range_io.go(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> IO(F.Ctl<S, R>), +env: E, n: Nat, +i: U32, c: F.Ctl<S, R>) -> IO(F.Ctl<S, R>):
  match n:
    case 0n:
      IO.pure(F.Ctl<S, R>, c)
    case 1n+p:
      match c:
        case F.Next{+s}:
          do IO<F.Ctl<S, R>>:
            c2 : F.Ctl<S, R> <- body(env, s, i)
            F.for_range_io.go(~S, ~R, ~E, ~body, env, p, (i + 1 : U32), c2)
        case F.Break{s}:
          IO.pure(F.Ctl<S, R>, F.Break{s})
        case F.Return{r}:
          IO.pure(F.Ctl<S, R>, F.Return{r})

def F.for_range_io(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> U32 -> IO(F.Ctl<S, R>), +env: E, r: F.Range, c: F.Ctl<S, R>) -> IO(F.Ctl<S, R>):
  match r:
    case F.Range{+s, e}:
      F.for_range_io.go(~S, ~R, ~E, ~body, env, U32.to_nat(F.i32.max((e - s : U32), 0)), s, c)

# A `while` (only inside an unsafe def): the body runs until it breaks or
# returns; the condition is part of the body.
@unsafe
def F.loop(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> F.Ctl<S, R>, +env: E, c: F.Ctl<S, R>) -> F.Ctl<S, R>:
  match c:
    case F.Next{+s}:
      F.loop(~S, ~R, ~E, ~body, env, body(env, s))
    case F.Break{s}:
      F.Break{s}
    case F.Return{r}:
      F.Return{r}

@unsafe
def F.loop_res(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> Result<&2, &2, String, F.Ctl<S, R>>, +env: E, c: F.Ctl<S, R>) -> Result<&2, &2, String, F.Ctl<S, R>>:
  match c:
    case F.Next{+s}:
      do Result<&2, &2, String, F.Ctl<S, R>>:
        c2 : F.Ctl<S, R> <- body(env, s)
        F.loop_res(~S, ~R, ~E, ~body, env, c2)
    case F.Break{s}:
      Done{F.Break{s}}
    case F.Return{r}:
      Done{F.Return{r}}

@unsafe
def F.loop_io(~S: Data, ~R: Data, ~E: Data, ~body: E -> S -> IO(F.Ctl<S, R>), +env: E, c: F.Ctl<S, R>) -> IO(F.Ctl<S, R>):
  match c:
    case F.Next{+s}:
      do IO<F.Ctl<S, R>>:
        c2 : F.Ctl<S, R> <- body(env, s)
        F.loop_io(~S, ~R, ~E, ~body, env, c2)
    case F.Break{s}:
      IO.pure(F.Ctl<S, R>, F.Break{s})
    case F.Return{r}:
      IO.pure(F.Ctl<S, R>, F.Return{r})

# -- Case eliminators ---------------------------------------------------------
# A match on a computed value: one continuation per constructor.
def F.list.case(-A: Data, -R: Type, xs: List<&2, A>, kn: Unit -> R, kc: A -> List<&2, A> -> R) -> R:
  match xs:
    case Nil{}:
      kn(Unit{})
    case Con{h, t}:
      kc(h, t)

def F.maybe.case(-A: Data, -R: Type, m: Maybe<&2, A>, kn: Unit -> R, ks: A -> R) -> R:
  match m:
    case None{}:
      kn(Unit{})
    case Some{v}:
      ks(v)

def F.result.case(-E: Data, -A: Data, -R: Type, r: Result<&2, &2, E, A>, kf: E -> R, kd: A -> R) -> R:
  match r:
    case Fail{e}:
      kf(e)
    case Done{v}:
      kd(v)

# -- Unit and Bool ------------------------------------------------------------
def F.unit.show(u: Unit) -> String:
  "nothing"

def F.unit.eq(a: Unit, b: Unit) -> Bool:
  True{}

def F.unit.lt(a: Unit, b: Unit) -> Bool:
  False{}

def F.unit.default() -> Unit:
  Unit{}

def F.bool.show(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def F.bool.eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def F.bool.lt(a: Bool, b: Bool) -> Bool:
  Bool.and(Bool.not(a), b)

def F.bool.default() -> Bool:
  False{}

# -- 32-bit signed integers over U32 -----------------------------------------
def F.i32.neg(+x: U32) -> Bool:
  U32.is_ne(U32.and(x, 2147483648), 0)

# arithmetic shift right: a logical shift of the complement keeps the sign
def F.i32.shr.go(x: U32, n: Nat, neg: Bool) -> U32:
  match neg:
    case True{}:
      U32.not(U32.shrn(U32.not(x), n))
    case False{}:
      U32.shrn(x, n)

def F.i32.shr(+x: U32, n: Nat) -> U32:
  F.i32.shr.go(x, n, F.i32.neg(x))

def F.i32.add(a: U32, b: U32) -> U32:
  (a + b : U32)

def F.i32.eq(a: U32, b: U32) -> Bool:
  U32.is_eq(a, b)

def F.i32.lt(a: U32, b: U32) -> Bool:
  U32.is_lt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.le(a: U32, b: U32) -> Bool:
  U32.is_le(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.ge(a: U32, b: U32) -> Bool:
  U32.is_ge(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.default() -> U32:
  0

def F.i32.abs.k(+x: U32, neg: Bool) -> U32:
  match neg:
    case True{}:
      (0 - x : U32)
    case False{}:
      x

def F.i32.abs(+x: U32) -> U32:
  F.i32.abs.k(x, F.i32.neg(x))

def F.i32.min(+a: U32, +b: U32) -> U32:
  F.i32.min.k(a, b, F.i32.lt(a, b))

# The fuel of a def that recurses on an int decreased by literals under a
# guard: one more than the int, so the fuel outlasts every call.
def F.i32.fuel(+x: U32) -> Nat:
  (1n + U32.to_nat(F.i32.max(x, 0)) : Nat)

# Euclidean division: the remainder is never negative.
def F.i32.divmod.fix(+q: U32, +r: U32, +b: U32, bneg: Bool) -> U32 & U32:
  match bneg:
    case True{}:
      ((q + 1 : U32), (r + b : U32))
    case False{}:
      ((q - 1 : U32), (r + b : U32))

def F.i32.divmod.adj(+q: U32, +r: U32, +b: U32, rneg: Bool) -> U32 & U32:
  match rneg:
    case True{}:
      F.i32.divmod.fix(q, r, b, F.i32.neg(b))
    case False{}:
      (q, r)

def F.i32.divmod.signed(+a: U32, +b: U32, +qa: U32, +qb: U32, aneg: Bool, bneg: Bool) -> U32 & U32:
  match aneg bneg:
    case False{} False{}:
      ((qa / qb : U32), (qa % qb : U32))
    case True{} False{}:
      F.i32.divmod.adj((0 - (qa / qb : U32) : U32), (0 - (qa % qb : U32) : U32), b, F.i32.neg((0 - (qa % qb : U32) : U32)))
    case False{} True{}:
      ((0 - (qa / qb : U32) : U32), (qa % qb : U32))
    case True{} True{}:
      F.i32.divmod.adj((qa / qb : U32), (0 - (qa % qb : U32) : U32), b, F.i32.neg((0 - (qa % qb : U32) : U32)))

def F.i32.divmod.z(+a: U32, +b: U32, bzero: Bool) -> U32 & U32:
  match bzero:
    case True{}:
      (0, 0)
    case False{}:
      F.i32.divmod.signed(a, b, F.i32.abs(a), F.i32.abs(b), F.i32.neg(a), F.i32.neg(b))

def F.i32.divmod(+a: U32, +b: U32) -> U32 & U32:
  F.i32.divmod.z(a, b, U32.is_zero(b))

def F.i32.div(+a: U32, +b: U32) -> U32:
  F.fst(U32, U32, F.i32.divmod(a, b))

def F.i32.mod(+a: U32, +b: U32) -> U32:
  F.snd(U32, U32, F.i32.divmod(a, b))

def F.i32.pow.go(n: Nat, +base: U32, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      F.i32.pow.go(p, base, (acc * base : U32))

def F.i32.pow(+a: U32, +b: U32) -> U32:
  F.i32.pow.go(U32.to_nat(b), a, 1)

def F.i32.show.k(+x: U32, neg: Bool) -> String:
  match neg:
    case True{}:
      "-" ++ U32.show((0 - x : U32))
    case False{}:
      U32.show(x)

def F.i32.show(+x: U32) -> String:
  F.i32.show.k(x, F.i32.neg(x))

# the message an index out of range aborts with
def F.index_error(what: String, +i: U32, +len: U32) -> String:
  what ++ " index " ++ F.i32.show(i) ++ " out of range for length " ++ F.i32.show(len)

def F.i32.to_f32.k(+x: U32, neg: Bool) -> F32:
  match neg:
    case True{}:
      F32.neg(F32.from_nat(U32.to_nat((0 - x : U32))))
    case False{}:
      F32.from_nat(U32.to_nat(x))

def F.i32.to_f32(+x: U32) -> F32:
  F.i32.to_f32.k(x, F.i32.neg(x))

def F.i32.parse.neg(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case Some{v}:
      Some{(0 - v : U32)}
    case None{}:
      None{}

def F.i32.parse.dash.k(h: Char, +t: String, dash: Bool) -> Maybe<&2, U32>:
  match dash:
    case True{}:
      F.i32.parse.neg(U32.read(t))
    case False{}:
      U32.read(SCon{h, t})

def F.i32.parse.dash(+h: Char, t: String) -> Maybe<&2, U32>:
  F.i32.parse.dash.k(h, t, Char.is_eq(h, '-'))

def F.i32.parse.sign(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      F.i32.parse.dash(h, t)

def F.i32.parse(s: String) -> Maybe<&2, U32>:
  F.i32.parse.sign(String.trim(s))

def F.i32.parse_result.k(+s: String, m: Maybe<&2, U32>) -> Result<&2, &2, String, U32>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"'" ++ s ++ "' is not an integer"}

def F.i32.parse_result(+s: String) -> Result<&2, &2, String, U32>:
  F.i32.parse_result.k(s, F.i32.parse(s))

def F.i32.parse_or_abort(+s: String) -> Result<&2, &2, String, U32>:
  F.i32.parse_result(s)

# -- Floats -------------------------------------------------------------------
def F.f32.show.k(+s: String, has_dot: Bool) -> String:
  match has_dot:
    case True{}:
      s
    case False{}:
      s ++ ".0"

def F.f32.has_dot(+s: String) -> Bool:
  Bool.or(String.contains(s, "."), Bool.or(String.contains(s, "e"), Bool.or(String.contains(s, "n"), String.contains(s, "i"))))

def F.f32.show(+x: F32) -> String:
  F.f32.show.k(F32.show(x), F.f32.has_dot(F32.show(x)))

def F.f32.add(a: F32, b: F32) -> F32:
  (a + b : F32)

def F.f32.eq(a: F32, b: F32) -> Bool:
  F32.is_eq(a, b)

def F.f32.lt(a: F32, b: F32) -> Bool:
  F32.is_lt(a, b)

def F.f32.default() -> F32:
  0.0

def F.f32.pow10.go(n: Nat, +acc: F32) -> F32:
  match n:
    case 0n:
      acc
    case 1n+p:
      F.f32.pow10.go(p, (acc * 10.0 : F32))

def F.f32.pow10(+n: U32) -> F32:
  F.f32.pow10.go(U32.to_nat(n), 1.0)

# pad the fraction with zeros up to `want` digits
def F.f32.pad_frac(n: Nat, +s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      F.f32.pad_frac(p, s ++ "0")

# digits after the dot (0 without a dot): one walk, the dot seen so far
def F.f32.frac_len.go(s: String, +seen: Bool, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{h, t}:
      F.f32.frac_len.go(t, Bool.or(seen, Char.is_eq(h, '.')), (n + Bool.to_u32(seen) : U32))

def F.f32.frac_len(s: String) -> U32:
  F.f32.frac_len.go(s, False{}, 0)

def F.f32.show_fixed.dot(+s: String, has: Bool) -> String:
  match has:
    case True{}:
      s
    case False{}:
      s ++ "."

def F.f32.show_fixed.k(+s: String, +digits: U32) -> String:
  F.f32.pad_frac(U32.to_nat(F.i32.max((digits - F.f32.frac_len(s) : U32), 0)), F.f32.show_fixed.dot(s, String.contains(s, ".")))

def F.f32.to_i32.k(+x: F32, neg: Bool) -> U32:
  match neg:
    case True{}:
      (0 - U32.from_nat(F32.to_nat(F32.neg(x))) : U32)
    case False{}:
      U32.from_nat(F32.to_nat(x))

def F.f32.to_i32(+x: F32) -> U32:
  F.f32.to_i32.k(x, F32.is_lt(x, 0.0))

def F.f32.show_fixed.zero(+x: F32, digits: U32) -> String:
  F.i32.show(F.f32.to_i32(F32.round(x)))

def F.f32.show_fixed.pick(+x: F32, +digits: U32, zero: Bool) -> String:
  match zero:
    case True{}:
      F.f32.show_fixed.zero(x, digits)
    case False{}:
      F.f32.show_fixed.k(F32.show((F32.round((x * F.f32.pow10(digits) : F32)) / F.f32.pow10(digits) : F32)), digits)

def F.f32.show_fixed(+x: F32, +digits: U32) -> String:
  F.f32.show_fixed.pick(x, digits, U32.is_zero(digits))

def F.f32.round_digits(+x: F32, +digits: U32) -> F32:
  (F32.round((x * F.f32.pow10(digits) : F32)) / F.f32.pow10(digits) : F32)

def F.f32.inf() -> F32:
  (1.0 / 0.0 : F32)

def F.f32.log_base(x: F32, b: F32) -> F32:
  (F32.log(x) / F32.log(b) : F32)

def F.f32.parse_result.k(+s: String, m: Maybe<&2, F32>) -> Result<&2, &2, String, F32>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"'" ++ s ++ "' is not a number"}

def F.f32.parse_result(+s: String) -> Result<&2, &2, String, F32>:
  F.f32.parse_result.k(s, F32.read(String.trim(s)))

def F.f32.parse_or_abort(+s: String) -> Result<&2, &2, String, F32>:
  F.f32.parse_result(s)

# -- Strings ------------------------------------------------------------------
def F.str.show(s: String) -> String:
  s

# a string inside a container shows quoted
def F.str.repr(s: String) -> String:
  "'" ++ s ++ "'"

def F.str.eq(a: String, b: String) -> Bool:
  String.eq(a, b)

def F.str.lt(a: String, b: String) -> Bool:
  String.is_lt(a, b)

def F.str.default() -> String:
  ""

def F.str.len(s: String) -> U32:
  U32.from_nat(String.length(s))

def F.str.clamp.k(+len: U32, +i: U32, neg: Bool) -> U32:
  match neg:
    case True{}:
      F.i32.max((len + i : U32), 0)
    case False{}:
      F.i32.min(i, len)

# a slice bound clamped into [0, len]
def F.str.clamp(+len: U32, +i: U32) -> U32:
  F.str.clamp.k(len, i, F.i32.neg(i))

def F.str.slice.k(s: String, +a: U32, +b: U32) -> String:
  String.take(String.drop(s, U32.to_nat(a)), U32.to_nat(F.i32.max((b - a : U32), 0)))

def F.str.slice(+s: String, +a: U32, +b: U32) -> String:
  F.str.slice.k(s, F.str.clamp(F.str.len(s), a), F.str.clamp(F.str.len(s), b))

def F.str.slice_range(s: String, r: F.Range) -> String:
  match r:
    case F.Range{a, b}:
      F.str.slice(s, a, b)

# drop a known prefix and the final character (`Name{a: 1}` -> `a: 1`)
def F.str.strip_wrapper(prefix: String, +s: String) -> String:
  F.str.slice(s, F.str.len(prefix), (F.str.len(s) - 1 : U32))

def F.str.nat_index.k(+len: U32, +i: U32, neg: Bool) -> Nat:
  match neg:
    case True{}:
      U32.to_nat((len + i : U32))
    case False{}:
      U32.to_nat(i)

# a Fire index (negative counts from the end) as a Nat position
def F.str.nat_index(+len: U32, +i: U32) -> Nat:
  F.str.nat_index.k(len, i, F.i32.neg(i))

def F.str.index.k(m: Maybe<&2, Char>, +i: U32, +len: U32) -> Result<&2, &2, String, String>:
  match m:
    case Some{c}:
      Done{SCon{c, SNil{}}}
    case None{}:
      Fail{F.index_error("string", i, len)}

def F.str.index(+s: String, +i: U32) -> Result<&2, &2, String, String>:
  F.str.index.k(String.get(s, F.str.nat_index(F.str.len(s), i)), i, F.str.len(s))

def F.str.take(s: String, +n: U32) -> String:
  String.take(s, U32.to_nat(F.i32.max(n, 0)))

def F.str.drop(s: String, +n: U32) -> String:
  String.drop(s, U32.to_nat(F.i32.max(n, 0)))

def F.str.chars(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{h, t}:
      SCon{h, SNil{}} <> F.str.chars(t)

def F.str.repeat(+s: String, +n: U32) -> String:
  String.repeat(s, U32.to_nat(F.i32.max(n, 0)))

def F.str.char_code(s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{h, t}:
      Char.to_u32(h)

def F.str.from_char_code(c: U32) -> String:
  SCon{Char.from_u32(c), SNil{}}

# split at every occurrence of `sep`: one character per turn of the fuel
def F.str.split.go(n: Nat, +s: String, +sep: String, +cur: String, +acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      List.reverse(&2, String, (String.reverse(cur) <> acc))
    case 1n+p:
      match s:
        case SNil{}:
          List.reverse(&2, String, (String.reverse(cur) <> acc))
        case SCon{h, t}:
          +hit = String.starts_with(s, sep)
          F.str.split.go(p, (Bool.pick(Unit -> String, hit, _ => String.drop(s, String.length(sep)), _ => t))(Unit{}), sep, (Bool.pick(Unit -> String, hit, _ => SNil{}, _ => SCon{h, cur}))(Unit{}), (Bool.pick(Unit -> List<&2, String>, hit, _ => (String.reverse(cur) <> acc), _ => acc))(Unit{}))

def F.str.split.pick(+s: String, +sep: String, empty: Bool) -> List<&2, String>:
  match empty:
    case True{}:
      F.str.chars(s)
    case False{}:
      F.str.split.go(String.length(s), s, sep, SNil{}, Nil{})

def F.str.split(+s: String, +sep: String) -> List<&2, String>:
  F.str.split.pick(s, sep, String.is_empty(sep))

def F.str.split_ws.head_space(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Char.is_space(h)

def F.str.split_ws.push.k(+cur: String, +acc: List<&2, String>, empty: Bool) -> List<&2, String>:
  match empty:
    case True{}:
      acc
    case False{}:
      (String.reverse(cur) <> acc)

def F.str.split_ws.push(+cur: String, +acc: List<&2, String>) -> List<&2, String>:
  F.str.split_ws.push.k(cur, acc, String.is_empty(cur))

# split on whitespace: `sp` says whether the current head is a space
def F.str.split_ws.go(s: String, +cur: String, +acc: List<&2, String>, sp: Bool) -> List<&2, String>:
  match s:
    case SNil{}:
      List.reverse(&2, String, F.str.split_ws.push(cur, acc))
    case SCon{h, +t}:
      match sp:
        case True{}:
          +t2 = t
          F.str.split_ws.go(t2, SNil{}, F.str.split_ws.push(cur, acc), F.str.split_ws.head_space(t2))
        case False{}:
          +t3 = t
          F.str.split_ws.go(t3, SCon{h, cur}, acc, F.str.split_ws.head_space(t3))

def F.str.split_ws(+s: String) -> List<&2, String>:
  F.str.split_ws.go(s, SNil{}, Nil{}, F.str.split_ws.head_space(s))

# replace every occurrence of `from`: one character per turn of the fuel
def F.str.replace.go(n: Nat, +s: String, +from: String, +to: String, +acc: String) -> String:
  match n:
    case 0n:
      String.reverse(acc)
    case 1n+p:
      match s:
        case SNil{}:
          String.reverse(acc)
        case SCon{h, t}:
          +hit = String.starts_with(s, from)
          F.str.replace.go(p, (Bool.pick(Unit -> String, hit, _ => String.drop(s, String.length(from)), _ => t))(Unit{}), from, to, (Bool.pick(Unit -> String, hit, _ => String.append(String.reverse(to), acc), _ => SCon{h, acc}))(Unit{}))

def F.str.replace.pick(+s: String, +from: String, +to: String, empty: Bool) -> String:
  match empty:
    case True{}:
      s
    case False{}:
      F.str.replace.go(String.length(s), s, from, to, SNil{})

def F.str.replace(+s: String, +from: String, +to: String) -> String:
  F.str.replace.pick(s, from, to, String.is_empty(from))

def F.str.index_of.go(+s: String, +p: String, +i: U32) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      (Bool.pick(Unit -> Maybe<&2, U32>, String.starts_with(s, p), _ => Some{i}, _ => F.str.index_of.go(t, p, (i + 1 : U32))))(Unit{})

def F.str.index_of(+s: String, +p: String) -> Maybe<&2, U32>:
  F.str.index_of.go(s, p, 0)

# -- Formatting ---------------------------------------------------------------
def F.fmt.fill(+n: U32, +c: Char) -> String:
  String.repeat(SCon{c, SNil{}}, U32.to_nat(n))

def F.fmt.pad_left.k(+s: String, +width: U32, +c: Char, +len: U32, short: Bool) -> String:
  match short:
    case True{}:
      F.fmt.fill((width - len : U32), c) ++ s
    case False{}:
      s

def F.fmt.pad_left(+s: String, +width: U32, +c: Char) -> String:
  F.fmt.pad_left.k(s, width, c, F.str.len(s), U32.is_lt(F.str.len(s), width))

def F.fmt.pad_right.k(+s: String, +width: U32, +c: Char, +len: U32, short: Bool) -> String:
  match short:
    case True{}:
      s ++ F.fmt.fill((width - len : U32), c)
    case False{}:
      s

def F.fmt.pad_right(+s: String, +width: U32, +c: Char) -> String:
  F.fmt.pad_right.k(s, width, c, F.str.len(s), U32.is_lt(F.str.len(s), width))

def F.fmt.pad_center.k(+s: String, +width: U32, +c: Char, +len: U32, short: Bool) -> String:
  match short:
    case True{}:
      F.fmt.fill(((width - len : U32) / 2 : U32), c) ++ s ++ F.fmt.fill(((width - len : U32) - ((width - len : U32) / 2 : U32) : U32), c)
    case False{}:
      s

def F.fmt.pad_center(+s: String, +width: U32, +c: Char) -> String:
  F.fmt.pad_center.k(s, width, c, F.str.len(s), U32.is_lt(F.str.len(s), width))

# `{n:05}`: zeros after the sign
def F.fmt.pad_zero.k(+width: U32, h: Char, +t: String, neg: Bool) -> String:
  match neg:
    case True{}:
      SCon{h, F.fmt.pad_left(t, (width - 1 : U32), '0')}
    case False{}:
      F.fmt.pad_left(SCon{h, t}, width, '0')

def F.fmt.pad_zero(s: String, +width: U32) -> String:
  match s:
    case SNil{}:
      F.fmt.pad_left(SNil{}, width, '0')
    case SCon{+h, +t}:
      F.fmt.pad_zero.k(width, h, t, Char.is_eq(h, '-'))

# -- Ranges -------------------------------------------------------------------
def F.range.start(r: F.Range) -> U32:
  match r:
    case F.Range{s, e}:
      s

def F.range.end(r: F.Range) -> U32:
  match r:
    case F.Range{s, e}:
      e

def F.range.to_list.go(n: Nat, +i: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      F.range.to_list.go(p, (i + 1 : U32), (i <> acc))

def F.range.to_list(r: F.Range) -> List<&2, U32>:
  match r:
    case F.Range{+s, e}:
      F.range.to_list.go(U32.to_nat(F.i32.max((e - s : U32), 0)), s, Nil{})

def F.range.len(r: F.Range) -> U32:
  match r:
    case F.Range{s, e}:
      F.i32.max((e - s : U32), 0)

def F.range.contains(r: F.Range, +x: U32) -> Bool:
  match r:
    case F.Range{s, e}:
      Bool.and(F.i32.ge(x, s), F.i32.lt(x, e))

def F.range.index.fin(v: U32, ok: Bool) -> Result<&2, &2, String, U32>:
  match ok:
    case True{}:
      Done{v}
    case False{}:
      Fail{"range index out of range"}

def F.range.index.k(+s: U32, +e: U32, +i: U32, neg: Bool) -> Result<&2, &2, String, U32>:
  match neg:
    case True{}:
      F.range.index.fin((e + i : U32), F.i32.ge((e + i : U32), s))
    case False{}:
      F.range.index.fin((s + i : U32), F.i32.lt((s + i : U32), e))

def F.range.index(r: F.Range, +i: U32) -> Result<&2, &2, String, U32>:
  match r:
    case F.Range{s, e}:
      F.range.index.k(s, e, i, F.i32.neg(i))

def F.range.first.k(+s: U32, nonempty: Bool) -> Result<&2, &2, String, U32>:
  match nonempty:
    case True{}:
      Done{s}
    case False{}:
      Fail{"min() of an empty range"}

def F.range.first(r: F.Range) -> Result<&2, &2, String, U32>:
  match r:
    case F.Range{+s, e}:
      F.range.first.k(s, F.i32.lt(s, e))

def F.range.last.k(+e: U32, nonempty: Bool) -> Result<&2, &2, String, U32>:
  match nonempty:
    case True{}:
      Done{(e - 1 : U32)}
    case False{}:
      Fail{"max() of an empty range"}

def F.range.last(r: F.Range) -> Result<&2, &2, String, U32>:
  match r:
    case F.Range{s, +e}:
      F.range.last.k(e, F.i32.lt(s, e))

def F.range.slice(r: F.Range, +a: U32, +b: U32) -> F.Range:
  match r:
    case F.Range{+s, +e}:
      F.Range{(s + F.str.clamp((e - s : U32), a) : U32), (s + F.str.clamp((e - s : U32), b) : U32)}

def F.range.slice_range(r: F.Range, r2: F.Range) -> F.Range:
  match r2:
    case F.Range{a, b}:
      F.range.slice(r, a, b)

def F.range.show(r: F.Range) -> String:
  match r:
    case F.Range{s, e}:
      F.i32.show(s) ++ ".." ++ F.i32.show(e)

def F.range.eq(a: F.Range, b: F.Range) -> Bool:
  match a:
    case F.Range{s1, e1}:
      match b:
        case F.Range{s2, e2}:
          Bool.and(U32.is_eq(s1, s2), U32.is_eq(e1, e2))

def F.range.lt(a: F.Range, b: F.Range) -> Bool:
  match a:
    case F.Range{+s1, e1}:
      match b:
        case F.Range{+s2, e2}:
          Bool.or(F.i32.lt(s1, s2), Bool.and(U32.is_eq(s1, s2), F.i32.lt(e1, e2)))

def F.range.default() -> F.Range:
  F.Range{0, 0}

# -- Lists --------------------------------------------------------------------
def F.list.len(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

def F.list.is_empty(-A: Data, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      False{}

def F.list.first(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{h}

def F.list.last.go(-A: Data, t: List<&2, A>, h: A) -> A:
  match t:
    case Nil{}:
      h
    case h2 <> t2:
      F.list.last.go(A, t2, h2)

def F.list.last(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{F.list.last.go(A, t, h)}

def F.list.push(-A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:
  List.append(&2, A, xs, [x])

# the list without its last element, and that element
def F.list.pop.k(-A: Data, r: List<&2, A>) -> Result<&2, &2, String, F.Pair<List<&2, A>, A>>:
  match r:
    case Nil{}:
      Fail{"pop from an empty list"}
    case h <> t:
      Done{F.Pair{List.reverse(&2, A, t), h}}

def F.list.pop(-A: Data, xs: List<&2, A>) -> Result<&2, &2, String, F.Pair<List<&2, A>, A>>:
  F.list.pop.k(A, List.reverse(&2, A, xs))

def F.list.drop_last.go(-A: Data, t: List<&2, A>, h: A) -> List<&2, A>:
  match t:
    case Nil{}:
      Nil{}
    case h2 <> t2:
      (h <> F.list.drop_last.go(A, t2, h2))

# all but the last element (the empty list stays empty)
def F.list.drop_last(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      F.list.drop_last.go(A, t, h)

def F.list.take(-A: Data, xs: List<&2, A>, +n: U32) -> List<&2, A>:
  List.take(&2, A, xs, U32.to_nat(F.i32.max(n, 0)))

def F.list.drop(-A: Data, xs: List<&2, A>, +n: U32) -> List<&2, A>:
  List.drop(&2, A, xs, U32.to_nat(F.i32.max(n, 0)))

def F.list.index.k(-A: Data, m: Maybe<&2, A>, +i: U32, +len: U32) -> Result<&2, &2, String, A>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{F.index_error("list", i, len)}

def F.list.index(-A: Data, +xs: List<&2, A>, +i: U32) -> Result<&2, &2, String, A>:
  F.list.index.k(A, List.get(&2, A, xs, F.str.nat_index(F.list.len(A, xs), i)), i, F.list.len(A, xs))

def F.list.slice.k(-A: Data, xs: List<&2, A>, +a: U32, +b: U32) -> List<&2, A>:
  List.take(&2, A, List.drop(&2, A, xs, U32.to_nat(a)), U32.to_nat(F.i32.max((b - a : U32), 0)))

def F.list.slice(-A: Data, +xs: List<&2, A>, +a: U32, +b: U32) -> List<&2, A>:
  F.list.slice.k(A, xs, F.str.clamp(F.list.len(A, xs), a), F.str.clamp(F.list.len(A, xs), b))

def F.list.slice_range(-A: Data, xs: List<&2, A>, r: F.Range) -> List<&2, A>:
  match r:
    case F.Range{a, b}:
      F.list.slice(A, xs, a, b)

def F.list.set.go(-A: Data, xs: List<&2, A>, n: Nat, +v: A) -> List<&2, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      (v <> t)
    case h <> t 1n+p:
      (h <> F.list.set.go(A, t, p, v))

def F.list.set.k(-A: Data, +xs: List<&2, A>, +i: U32, +v: A, ok: Bool) -> Result<&2, &2, String, List<&2, A>>:
  match ok:
    case True{}:
      Done{F.list.set.go(A, xs, F.str.nat_index(F.list.len(A, xs), i), v)}
    case False{}:
      Fail{F.index_error("list", i, F.list.len(A, xs))}

def F.list.set(-A: Data, +xs: List<&2, A>, +i: U32, +v: A) -> Result<&2, &2, String, List<&2, A>>:
  F.list.set.k(A, xs, i, v, Bool.and(F.i32.lt(i, F.list.len(A, xs)), F.i32.ge(i, (0 - F.list.len(A, xs) : U32))))

# a list pattern needs a list of the right length
def F.list.need_exactly.k(+n: U32, +len: U32) -> Result<&2, &2, String, Unit>:
  F.assert(U32.is_eq(len, n), "expected a list of " ++ F.i32.show(n) ++ " elements, got " ++ F.i32.show(len))

def F.list.need_exactly(-A: Data, xs: List<&2, A>, +n: U32) -> Result<&2, &2, String, Unit>:
  F.list.need_exactly.k(n, F.list.len(A, xs))

def F.list.need_at_least.k(+n: U32, +len: U32) -> Result<&2, &2, String, Unit>:
  F.assert(U32.is_ge(len, n), "expected a list of at least " ++ F.i32.show(n) ++ " elements, got " ++ F.i32.show(len))

def F.list.need_at_least(-A: Data, xs: List<&2, A>, +n: U32) -> Result<&2, &2, String, Unit>:
  F.list.need_at_least.k(n, F.list.len(A, xs))

def F.list.sum(~A: Data, ~add: A -> A -> A, xs: List<&2, A>, acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      F.list.sum(~A, ~add, t, add(acc, h))

def F.list.pick(-A: Data, acc: A, h: A, take: Bool) -> A:
  match take:
    case True{}:
      h
    case False{}:
      acc

def F.list.min.go(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>, +acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      F.list.min.go(~A, ~lt, t, F.list.pick(A, acc, h, lt(h, acc)))

def F.list.min(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  match xs:
    case Nil{}:
      Fail{"min() of an empty list"}
    case h <> t:
      Done{F.list.min.go(~A, ~lt, t, h)}

def F.list.max.go(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>, +acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      F.list.max.go(~A, ~lt, t, F.list.pick(A, acc, h, lt(acc, h)))

def F.list.max(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  match xs:
    case Nil{}:
      Fail{"max() of an empty list"}
    case h <> t:
      Done{F.list.max.go(~A, ~lt, t, h)}

def F.list.contains(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(eq(h, x), F.list.contains(~A, ~eq, t, x))

def F.list.index_of.go(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A, +i: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      (Bool.pick(Unit -> Maybe<&2, U32>, eq(h, x), _ => Some{i}, _ => F.list.index_of.go(~A, ~eq, t, x, (i + 1 : U32))))(Unit{})

def F.list.index_of(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Maybe<&2, U32>:
  F.list.index_of.go(~A, ~eq, xs, x, 0)

def F.list.flatten(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  List.concat(&2, A, xss)

def F.list.repeat(-A: Data, +x: A, +n: U32) -> List<&2, A>:
  List.replicate(A, U32.to_nat(F.i32.max(n, 0)), x)

def F.list.enumerate_from(-A: Data, xs: List<&2, A>, +i: U32) -> List<&2, F.Pair<U32, A>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (F.Pair{i, h} <> F.list.enumerate_from(A, t, (i + 1 : U32)))

def F.list.zip(-A: Data, -B: Data, xs: List<&2, A>, ys: List<&2, B>) -> List<&2, F.Pair<A, B>>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case h <> t Nil{}:
      Nil{}
    case h <> t h2 <> t2:
      (F.Pair{h, h2} <> F.list.zip(A, B, t, t2))

def F.list.show.go(~A: Data, ~f: A -> String, xs: List<&2, A>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      ", " ++ f(h) ++ F.list.show.go(~A, ~f, t)

def F.list.show(~A: Data, ~f: A -> String, xs: List<&2, A>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case h <> t:
      "[" ++ f(h) ++ F.list.show.go(~A, ~f, t) ++ "]"

def F.list.eq(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} h2 <> t2:
      False{}
    case h <> t Nil{}:
      False{}
    case h <> t h2 <> t2:
      Bool.and(eq(h, h2), F.list.eq(~A, ~eq, t, t2))

# lexicographic order from the element order alone
def F.list.lt(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      False{}
    case Nil{} h2 <> t2:
      True{}
    case h <> t Nil{}:
      False{}
    case +h <> t +h2 <> t2:
      Bool.or(lt(h, h2), Bool.and(Bool.not(lt(h2, h)), F.list.lt(~A, ~lt, t, t2)))

def F.list.sort.le(~A: Data, ~lt: A -> A -> Bool, a: A, b: A) -> Bool:
  Bool.not(lt(b, a))

def F.list.sort(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  List.sort(~A, ~F.list.sort.le(~A, ~lt), xs)

# sort by precomputed keys: zip, sort the pairs by key, drop the keys
def F.list.sort_decorated.key(~K: Data, ~A: Data, e: Unit, p: F.Pair<K, A>) -> K:
  match p:
    case F.Pair{k, v}:
      k

def F.list.sort_decorated.val(~K: Data, ~A: Data, e: Unit, p: F.Pair<K, A>) -> A:
  match p:
    case F.Pair{k, v}:
      v

def F.list.sort_decorated.le(~K: Data, ~A: Data, ~lt: K -> K -> Bool, a: F.Pair<K, A>, b: F.Pair<K, A>) -> Bool:
  match a:
    case F.Pair{ka, va}:
      match b:
        case F.Pair{kb, vb}:
          Bool.not(lt(kb, ka))

# -- Lists: higher-order, threading an environment ---------------------------
def F.list.map_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> B, +e: E, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (f(e, h) <> F.list.map_env(~E, ~A, ~B, ~f, e, t))

def F.list.sort_decorated(~K: Data, ~A: Data, ~lt: K -> K -> Bool, keys: List<&2, K>, xs: List<&2, A>) -> List<&2, A>:
  F.list.map_env(~Unit, ~F.Pair<K, A>, ~A, ~F.list.sort_decorated.val(~K, ~A), Unit{}, List.sort(~F.Pair<K, A>, ~F.list.sort_decorated.le(~K, ~A, ~lt), F.list.zip(K, A, keys, xs)))

def F.list.map_res_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> Result<&2, &2, String, B>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, List<&2, B>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case h <> t:
      do Result<&2, &2, String, List<&2, B>>:
        y : B <- f(e, h)
        ys : List<&2, B> <- F.list.map_res_env(~E, ~A, ~B, ~f, e, t)
        return (y <> ys)

def F.list.map_io_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> IO(B), +e: E, xs: List<&2, A>) -> IO(List<&2, B>):
  match xs:
    case Nil{}:
      IO.pure(List<&2, B>, Nil{})
    case h <> t:
      do IO<List<&2, B>>:
        y : B <- f(e, h)
        ys : List<&2, B> <- F.list.map_io_env(~E, ~A, ~B, ~f, e, t)
        return (y <> ys)

def F.list.sort_by_key_env(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, +xs: List<&2, A>) -> List<&2, A>:
  F.list.sort_decorated(~K, ~A, ~lt, F.list.map_env(~E, ~A, ~K, ~key, e, xs), xs)

def F.list.sort_by_key_res_env(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> Result<&2, &2, String, K>, ~lt: K -> K -> Bool, +e: E, +xs: List<&2, A>) -> Result<&2, &2, String, List<&2, A>>:
  do Result<&2, &2, String, List<&2, A>>:
    keys : List<&2, K> <- F.list.map_res_env(~E, ~A, ~K, ~key, e, xs)
    return F.list.sort_decorated(~K, ~A, ~lt, keys, xs)

def F.list.sort_by_key_io_env(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> IO(K), ~lt: K -> K -> Bool, +e: E, +xs: List<&2, A>) -> IO(List<&2, A>):
  do IO<List<&2, A>>:
    keys : List<&2, K> <- F.list.map_io_env(~E, ~A, ~K, ~key, e, xs)
    return F.list.sort_decorated(~K, ~A, ~lt, keys, xs)

def F.list.filter.put(-A: Data, h: A, r: List<&2, A>, keep: Bool) -> List<&2, A>:
  match keep:
    case True{}:
      (h <> r)
    case False{}:
      r

def F.list.filter_env(~E: Data, ~A: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      F.list.filter.put(A, h, F.list.filter_env(~E, ~A, ~f, e, t), f(e, h))

def F.list.filter_res_env(~E: Data, ~A: Data, ~f: E -> A -> Result<&2, &2, String, Bool>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, List<&2, A>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case +h <> t:
      do Result<&2, &2, String, List<&2, A>>:
        keep : Bool <- f(e, h)
        rest : List<&2, A> <- F.list.filter_res_env(~E, ~A, ~f, e, t)
        return F.list.filter.put(A, h, rest, keep)

def F.list.filter_io_env(~E: Data, ~A: Data, ~f: E -> A -> IO(Bool), +e: E, xs: List<&2, A>) -> IO(List<&2, A>):
  match xs:
    case Nil{}:
      IO.pure(List<&2, A>, Nil{})
    case +h <> t:
      do IO<List<&2, A>>:
        keep : Bool <- f(e, h)
        rest : List<&2, A> <- F.list.filter_io_env(~E, ~A, ~f, e, t)
        return F.list.filter.put(A, h, rest, keep)

def F.list.each_env.drop(-B: Data, y: B, u: Unit) -> Unit:
  u

def F.list.each_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> B, +e: E, xs: List<&2, A>) -> Unit:
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      F.list.each_env.drop(B, f(e, h), F.list.each_env(~E, ~A, ~B, ~f, e, t))

def F.list.each_res_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> Result<&2, &2, String, B>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, Unit>:
  match xs:
    case Nil{}:
      Done{Unit{}}
    case h <> t:
      do Result<&2, &2, String, Unit>:
        y : B <- f(e, h)
        F.list.each_res_env(~E, ~A, ~B, ~f, e, t)

def F.list.each_io_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> IO(B), +e: E, xs: List<&2, A>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        y : B <- f(e, h)
        F.list.each_io_env(~E, ~A, ~B, ~f, e, t)

def F.list.foldl_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> B -> A -> B, +e: E, xs: List<&2, A>, acc: B) -> B:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      F.list.foldl_env(~E, ~A, ~B, ~f, e, t, f(e, acc, h))

def F.list.foldl_res_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> B -> A -> Result<&2, &2, String, B>, +e: E, xs: List<&2, A>, acc: B) -> Result<&2, &2, String, B>:
  match xs:
    case Nil{}:
      Done{acc}
    case h <> t:
      do Result<&2, &2, String, B>:
        acc2 : B <- f(e, acc, h)
        F.list.foldl_res_env(~E, ~A, ~B, ~f, e, t, acc2)

def F.list.foldl_io_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> B -> A -> IO(B), +e: E, xs: List<&2, A>, acc: B) -> IO(B):
  match xs:
    case Nil{}:
      IO.pure(B, acc)
    case h <> t:
      do IO<B>:
        acc2 : B <- f(e, acc, h)
        F.list.foldl_io_env(~E, ~A, ~B, ~f, e, t, acc2)

def F.list.reduce1_env(~E: Data, ~A: Data, ~f: E -> A -> A -> A, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  match xs:
    case Nil{}:
      Fail{"reduce() of an empty list"}
    case h <> t:
      Done{F.list.foldl_env(~E, ~A, ~A, ~f, e, t, h)}

def F.list.reduce1_res_env(~E: Data, ~A: Data, ~f: E -> A -> A -> Result<&2, &2, String, A>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  match xs:
    case Nil{}:
      Fail{"reduce() of an empty list"}
    case h <> t:
      F.list.foldl_res_env(~E, ~A, ~A, ~f, e, t, h)

def F.list.reduce1_io_env(~E: Data, ~A: Data, ~f: E -> A -> A -> IO(A), +e: E, xs: List<&2, A>) -> IO(A):
  match xs:
    case Nil{}:
      IO.die(A, 1, "reduce() of an empty list")
    case h <> t:
      F.list.foldl_io_env(~E, ~A, ~A, ~f, e, t, h)

def F.list.any_env(~E: Data, ~A: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(f(e, h), F.list.any_env(~E, ~A, ~f, e, t))

def F.list.all_env(~E: Data, ~A: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(f(e, h), F.list.all_env(~E, ~A, ~f, e, t))

def F.list.find.put(-A: Data, h: A, r: Maybe<&2, A>, hit: Bool) -> Maybe<&2, A>:
  match hit:
    case True{}:
      Some{h}
    case False{}:
      r

def F.list.find_env(~E: Data, ~A: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case +h <> t:
      F.list.find.put(A, h, F.list.find_env(~E, ~A, ~f, e, t), f(e, h))

def F.list.count_env(~E: Data, ~A: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case h <> t:
      (Bool.to_u32(f(e, h)) + F.list.count_env(~E, ~A, ~f, e, t) : U32)

# any/all/count/find over a callback that may fail or do IO: the callback
# runs on each element in order; any/all/find stop at the first decisive one
def F.list.any_res_env(~E: Data, ~A: Data, ~f: E -> A -> Result<&2, &2, String, Bool>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, Bool>:
  match xs:
    case Nil{}:
      Done{False{}}
    case h <> t:
      do Result<&2, &2, String, Bool>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> Result<&2, &2, String, Bool>, hit, _ => Done{True{}}, _ => F.list.any_res_env(~E, ~A, ~f, e, t)))(Unit{})

def F.list.any_io_env(~E: Data, ~A: Data, ~f: E -> A -> IO(Bool), +e: E, xs: List<&2, A>) -> IO(Bool):
  match xs:
    case Nil{}:
      IO.pure(Bool, False{})
    case h <> t:
      do IO<Bool>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> IO(Bool), hit, _ => IO.pure(Bool, True{}), _ => F.list.any_io_env(~E, ~A, ~f, e, t)))(Unit{})

def F.list.all_res_env(~E: Data, ~A: Data, ~f: E -> A -> Result<&2, &2, String, Bool>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, Bool>:
  match xs:
    case Nil{}:
      Done{True{}}
    case h <> t:
      do Result<&2, &2, String, Bool>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> Result<&2, &2, String, Bool>, hit, _ => F.list.all_res_env(~E, ~A, ~f, e, t), _ => Done{False{}}))(Unit{})

def F.list.all_io_env(~E: Data, ~A: Data, ~f: E -> A -> IO(Bool), +e: E, xs: List<&2, A>) -> IO(Bool):
  match xs:
    case Nil{}:
      IO.pure(Bool, True{})
    case h <> t:
      do IO<Bool>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> IO(Bool), hit, _ => F.list.all_io_env(~E, ~A, ~f, e, t), _ => IO.pure(Bool, False{})))(Unit{})

def F.list.find_res_env(~E: Data, ~A: Data, ~f: E -> A -> Result<&2, &2, String, Bool>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, Maybe<&2, A>>:
  match xs:
    case Nil{}:
      Done{None{}}
    case +h <> t:
      do Result<&2, &2, String, Maybe<&2, A>>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> Result<&2, &2, String, Maybe<&2, A>>, hit, _ => Done{Some{h}}, _ => F.list.find_res_env(~E, ~A, ~f, e, t)))(Unit{})

def F.list.find_io_env(~E: Data, ~A: Data, ~f: E -> A -> IO(Bool), +e: E, xs: List<&2, A>) -> IO(Maybe<&2, A>):
  match xs:
    case Nil{}:
      IO.pure(Maybe<&2, A>, None{})
    case +h <> t:
      do IO<Maybe<&2, A>>:
        hit : Bool <- f(e, h)
        (Bool.pick(Unit -> IO(Maybe<&2, A>), hit, _ => IO.pure(Maybe<&2, A>, Some{h}), _ => F.list.find_io_env(~E, ~A, ~f, e, t)))(Unit{})

def F.list.count_res_env(~E: Data, ~A: Data, ~f: E -> A -> Result<&2, &2, String, Bool>, +e: E, xs: List<&2, A>) -> Result<&2, &2, String, U32>:
  match xs:
    case Nil{}:
      Done{0}
    case h <> t:
      do Result<&2, &2, String, U32>:
        hit : Bool <- f(e, h)
        rest : U32 <- F.list.count_res_env(~E, ~A, ~f, e, t)
        return (Bool.to_u32(hit) + rest : U32)

def F.list.count_io_env(~E: Data, ~A: Data, ~f: E -> A -> IO(Bool), +e: E, xs: List<&2, A>) -> IO(U32):
  match xs:
    case Nil{}:
      IO.pure(U32, 0)
    case h <> t:
      do IO<U32>:
        hit : Bool <- f(e, h)
        rest : U32 <- F.list.count_io_env(~E, ~A, ~f, e, t)
        return (Bool.to_u32(hit) + rest : U32)

# -- Maybe --------------------------------------------------------------------
def F.maybe.show(~A: Data, ~f: A -> String, m: Maybe<&2, A>) -> String:
  match m:
    case Some{v}:
      f(v)
    case None{}:
      "nothing"

def F.maybe.eq(~A: Data, ~eq: A -> A -> Bool, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      eq(x, y)
    case Some{x} None{}:
      False{}
    case None{} Some{y}:
      False{}
    case None{} None{}:
      True{}

# nothing sorts before every value
def F.maybe.lt(~A: Data, ~lt: A -> A -> Bool, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      lt(x, y)
    case Some{x} None{}:
      False{}
    case None{} Some{y}:
      True{}
    case None{} None{}:
      False{}

def F.maybe.default(~A: Data, ~d: A) -> Maybe<&2, A>:
  None{}

def F.maybe.or(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case Some{v}:
      v
    case None{}:
      d

def F.maybe.unwrap(-A: Data, m: Maybe<&2, A>) -> Result<&2, &2, String, A>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"unwrap of nothing"}

# -- Result -------------------------------------------------------------------
def F.result.show(~X: Data, ~A: Data, ~fx: X -> String, ~fa: A -> String, r: Result<&2, &2, X, A>) -> String:
  match r:
    case Done{v}:
      "{ok: " ++ fa(v) ++ "}"
    case Fail{x}:
      "{err: " ++ fx(x) ++ "}"

def F.result.eq(~X: Data, ~A: Data, ~ex: X -> X -> Bool, ~ea: A -> A -> Bool, a: Result<&2, &2, X, A>, b: Result<&2, &2, X, A>) -> Bool:
  match a b:
    case Done{v} Done{w}:
      ea(v, w)
    case Done{v} Fail{y}:
      False{}
    case Fail{x} Done{w}:
      False{}
    case Fail{x} Fail{y}:
      ex(x, y)

# errors sort before values
def F.result.lt(~X: Data, ~A: Data, ~lx: X -> X -> Bool, ~la: A -> A -> Bool, a: Result<&2, &2, X, A>, b: Result<&2, &2, X, A>) -> Bool:
  match a b:
    case Done{v} Done{w}:
      la(v, w)
    case Done{v} Fail{y}:
      False{}
    case Fail{x} Done{w}:
      True{}
    case Fail{x} Fail{y}:
      lx(x, y)

def F.result.default(~X: Data, ~A: Data, ~dx: X, ~da: A) -> Result<&2, &2, X, A>:
  Done{da}

def F.result.unwrap_ok(-X: Data, -A: Data, r: Result<&2, &2, X, A>) -> Result<&2, &2, String, A>:
  match r:
    case Done{v}:
      Done{v}
    case Fail{x}:
      Fail{"expected an ok result"}

def F.result.unwrap_err(-X: Data, -A: Data, r: Result<&2, &2, X, A>) -> Result<&2, &2, String, X>:
  match r:
    case Done{v}:
      Fail{"expected an err result"}
    case Fail{x}:
      Done{x}

# -- The record {key, value} --------------------------------------------------
def F.pair.key(-A: Data, -B: Data, p: F.Pair<A, B>) -> A:
  match p:
    case F.Pair{k, v}:
      k

def F.pair.value(-A: Data, -B: Data, p: F.Pair<A, B>) -> B:
  match p:
    case F.Pair{k, v}:
      v

def F.pair.show(~A: Data, ~B: Data, ~fa: A -> String, ~fb: B -> String, p: F.Pair<A, B>) -> String:
  match p:
    case F.Pair{k, v}:
      "{key: " ++ fa(k) ++ ", value: " ++ fb(v) ++ "}"

def F.pair.eq(~A: Data, ~B: Data, ~ea: A -> A -> Bool, ~eb: B -> B -> Bool, a: F.Pair<A, B>, b: F.Pair<A, B>) -> Bool:
  match a:
    case F.Pair{k1, v1}:
      match b:
        case F.Pair{k2, v2}:
          Bool.and(ea(k1, k2), eb(v1, v2))

def F.pair.lt(~A: Data, ~B: Data, ~la: A -> A -> Bool, ~lb: B -> B -> Bool, a: F.Pair<A, B>, b: F.Pair<A, B>) -> Bool:
  match a:
    case F.Pair{+k1, v1}:
      match b:
        case F.Pair{+k2, v2}:
          Bool.or(la(k1, k2), Bool.and(Bool.not(la(k2, k1)), lb(v1, v2)))

def F.pair.default(~A: Data, ~B: Data, ~da: A, ~db: B) -> F.Pair<A, B>:
  F.Pair{da, db}

# -- Maps (string-keyed dictionaries) -----------------------------------------
def F.map.lookup(-V: Data, +m: Map<&2, V>, key: String) -> Maybe<&2, V>:
  F.snd(Map<&2, V>, Maybe<&2, V>, Map.pop(&2, V, m, key))

def F.map.has(-V: Data, +m: Map<&2, V>, key: String) -> Bool:
  F.snd(Map<&2, V>, Bool, Map.has(&2, V, m, key))

def F.map.size(-V: Data, m: Map<&2, V>) -> U32:
  U32.from_nat(Map.size(&2, V, m))

def F.map.values(-V: Data, m: Map<&2, V>) -> List<&2, V>:
  Map.values(&2, V, m)

# a key from Map.keys always has a value; a missing one is skipped
def F.map.entries.one(-V: Data, k: String, mv: Maybe<&2, V>, rest: List<&2, F.Pair<String, V>>) -> List<&2, F.Pair<String, V>>:
  match mv:
    case Some{v}:
      (F.Pair{k, v} <> rest)
    case None{}:
      rest

def F.map.entries.go(-V: Data, +m: Map<&2, V>, keys: List<&2, String>) -> List<&2, F.Pair<String, V>>:
  match keys:
    case Nil{}:
      Nil{}
    case +k <> t:
      F.map.entries.one(V, k, F.map.lookup(V, m, k), F.map.entries.go(V, m, t))

def F.map.entries(-V: Data, +m: Map<&2, V>) -> List<&2, F.Pair<String, V>>:
  F.map.entries.go(V, m, Map.keys(&2, V, m))

def F.map.show.go(~V: Data, ~f: V -> String, kvs: List<&2, F.Pair<String, V>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case F.Pair{k, v} <> t:
      ", " ++ k ++ ": " ++ f(v) ++ F.map.show.go(~V, ~f, t)

def F.map.show.list(~V: Data, ~f: V -> String, kvs: List<&2, F.Pair<String, V>>) -> String:
  match kvs:
    case Nil{}:
      "{}"
    case F.Pair{k, v} <> t:
      "{" ++ k ++ ": " ++ f(v) ++ F.map.show.go(~V, ~f, t) ++ "}"

def F.map.show(~V: Data, ~f: V -> String, m: Map<&2, V>) -> String:
  F.map.show.list(~V, ~f, F.map.entries(V, m))

def F.map.eq(~V: Data, ~eq: V -> V -> Bool, a: Map<&2, V>, b: Map<&2, V>) -> Bool:
  F.list.eq(~F.Pair<String, V>, ~F.pair.eq(~String, ~V, ~String.eq, ~eq), F.map.entries(V, a), F.map.entries(V, b))

def F.map.lt(~V: Data, ~lt: V -> V -> Bool, a: Map<&2, V>, b: Map<&2, V>) -> Bool:
  F.list.lt(~F.Pair<String, V>, ~F.pair.lt(~String, ~V, ~String.is_lt, ~lt), F.map.entries(V, a), F.map.entries(V, b))

# -- Effects ------------------------------------------------------------------
def F.io.err_text(e: U32 & String) -> String:
  (code, msg) = e
  msg

def F.io.read_file.fin(r: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, String, String>:
  match r:
    case Done{s}:
      Done{s}
    case Fail{e}:
      Fail{F.io.err_text(e)}

def F.io.read_file.k(m: File & Result<&1, &1, U32 & String, String>) -> IO(Result<&2, &2, String, String>):
  (f, r) = m
  do IO<Result<&2, &2, String, String>>:
    File.close(f)
    return F.io.read_file.fin(r)

def F.io.read_file.open(r: Result<&1, &1, U32 & String, File>) -> IO(Result<&2, &2, String, String>):
  match r:
    case Done{f}:
      do IO<Result<&2, &2, String, String>>:
        m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
        F.io.read_file.k(m)
    case Fail{e}:
      IO.pure(Result<&2, &2, String, String>, Fail{F.io.err_text(e)})

def F.io.read_file(path: String) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    F.io.read_file.open(r)

def F.io.write_file.fin(r: Result<&1, &1, U32 & String, Unit>) -> Result<&2, &2, String, Unit>:
  match r:
    case Done{u}:
      Done{Unit{}}
    case Fail{e}:
      Fail{F.io.err_text(e)}

def F.io.write_file.k(m: File & Result<&1, &1, U32 & String, Unit>) -> IO(Result<&2, &2, String, Unit>):
  (f, r) = m
  do IO<Result<&2, &2, String, Unit>>:
    File.close(f)
    return F.io.write_file.fin(r)

def F.io.write_file.open(r: Result<&1, &1, U32 & String, File>, content: String) -> IO(Result<&2, &2, String, Unit>):
  match r:
    case Done{f}:
      do IO<Result<&2, &2, String, Unit>>:
        m : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, content)
        F.io.write_file.k(m)
    case Fail{e}:
      IO.pure(Result<&2, &2, String, Unit>, Fail{F.io.err_text(e)})

def F.io.write_file(path: String, content: String) -> IO(Result<&2, &2, String, Unit>):
  do IO<Result<&2, &2, String, Unit>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    F.io.write_file.open(r, content)

def F.time.now() -> IO(U32):
  do IO<U32>:
    n : Nat <- IO.now()
    return U32.from_nat(n)
