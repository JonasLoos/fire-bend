# Fire runtime prelude, emitted at the top of every compiled program (see docs/compiler.md).
# Everything the generated code calls that Bend's Base does not provide.
# Helpers precede their callers; `+` marks reusable values.
# -- Generic helpers ----------------------------------------------------------
# The pair shape used by entries(), zip, enumerate, and zipping loops.

type F.Pair<-A: Data, -B: Data> is Data:
  F.Pair.mk{key: A, value: B}

# a mutating method's answer: the new receiver and the value
type F.Ret<-S: Data, -V: Data> is Data:
  F.Ret.mk{obj: S, value: V}

def F.ret.self(-S: Data, -V: Data, r: F.Ret<S, V>) -> S:
  match r:
    case F.Ret.mk{obj, value}:
      obj

def F.ret.value(-S: Data, -V: Data, r: F.Ret<S, V>) -> V:
  match r:
    case F.Ret.mk{obj, value}:
      value

def F.fst(-A: Data, -B: Data, p: A & B) -> A:
  (a, b) = p
  a

def F.snd(-A: Data, -B: Data, p: A & B) -> B:
  (a, b) = p
  b

def F.io_unwrap(-A: Data, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Done{v}:
      IO.pure(A, v)
    case Fail{e}:
      IO.die(A, 1, e)

# A pure abort: swapping into an unbalanced array traps the runtime
# ("runtime fail-stop"). The trap's result must feed the recursion, or the
# compiler drops the unused swap and the loop below runs forever.
def F.crash.arm(r: Array<U32> & U32) -> Bool:
  (na, x) = r
  U32.is_eq(x, 0)

@unsafe
def F.crash.go(-A: Data, +msg: String, b: Bool) -> A:
  match b:
    case True{}:
      F.crash.go(A, msg, False{})
    case False{}:
      F.crash.go(A, msg, True{})

def F.crash(-A: Data, +msg: String) -> A:
  F.crash.go(A, msg, F.crash.arm(Array.swap(U32, ANode{ALeaf{0}, ANode{ALeaf{0}, ALeaf{0}}}, 3, 0)))

def F.assert.k(msg: String, c: Bool) -> Result<&2, &2, String, Unit>:
  match c:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{msg}

def F.assert(c: Bool, msg: String) -> Result<&2, &2, String, Unit>:
  F.assert.k(msg, c)

def F.unit.show(u: Unit) -> String:
  "nothing"

def F.unit.eq(a: Unit, b: Unit) -> Bool:
  True{}

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

# -- 32-bit signed integers over U32 -----------------------------------------
def F.i32.neg(+x: U32) -> Bool:
  U32.is_ne(U32.and(x, 2147483648), 0)

def F.i32.lt(a: U32, b: U32) -> Bool:
  U32.is_lt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.le(a: U32, b: U32) -> Bool:
  U32.is_le(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.gt(a: U32, b: U32) -> Bool:
  U32.is_gt(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.ge(a: U32, b: U32) -> Bool:
  U32.is_ge(U32.xor(a, 2147483648), U32.xor(b, 2147483648))

def F.i32.abs.k(+x: U32, neg: Bool) -> U32:
  match neg:
    case True{}:
      (0 - x : U32)
    case False{}:
      x

def F.i32.abs(+x: U32) -> U32:
  F.i32.abs.k(x, F.i32.neg(x))

def F.i32.min.k(+a: U32, +b: U32, lt: Bool) -> U32:
  match lt:
    case True{}:
      a
    case False{}:
      b

def F.i32.min(+a: U32, +b: U32) -> U32:
  F.i32.min.k(a, b, F.i32.lt(a, b))

def F.i32.max(+a: U32, +b: U32) -> U32:
  F.i32.min.k(a, b, F.i32.gt(a, b))

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

# affine wrappers for use as template arguments
def F.i32.show.t(x: U32) -> String:
  F.i32.show(x)

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

def F.f32.pow10.go(n: Nat, +acc: F32) -> F32:
  match n:
    case 0n:
      acc
    case 1n+p:
      F.f32.pow10.go(p, (acc * 10.0 : F32))

def F.f32.pow10(+n: U32) -> F32:
  F.f32.pow10.go(U32.to_nat(n), 1.0)

@unsafe
def F.f32.pad_frac(+s: String, +want: U32, +have: U32, done: Bool) -> String:
  match done:
    case True{}:
      s
    case False{}:
      F.f32.pad_frac(s ++ "0", want, (have + 1 : U32), U32.is_ge((have + 1 : U32), want))

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
  F.f32.pad_frac(F.f32.show_fixed.dot(s, String.contains(s, ".")), digits, F.f32.frac_len(s), U32.is_ge(F.f32.frac_len(s), digits))

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

def F.f32.round_to_int(x: F32) -> U32:
  F.f32.to_i32(F32.round(x))

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

def F.f32.show.t(x: F32) -> String:
  F.f32.show(x)

# -- Strings ------------------------------------------------------------------
def F.str.id(s: String) -> String:
  s

# `sep ++ s` unless s is empty (joining an inherited member list)
def F.str.join_nonempty.k(sep: String, s: String, empty: Bool) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      (sep ++ s)

def F.str.join_nonempty(sep: String, +s: String) -> String:
  F.str.join_nonempty.k(sep, s, String.is_empty(s))

# `s ++ sep` unless s is empty
def F.str.join_nonempty_after.k(s: String, sep: String, empty: Bool) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      (s ++ sep)

def F.str.join_nonempty_after(+s: String, sep: String) -> String:
  F.str.join_nonempty_after.k(s, sep, String.is_empty(s))

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

# drop a known prefix and the final character (`Name{a: 1}` -> `a: 1`)
def F.str.strip_wrapper(prefix: String, +s: String) -> String:
  F.str.slice(s, F.str.len(prefix), (F.str.len(s) - 1 : U32))

def F.str.repr(s: String) -> String:
  "'" ++ s ++ "'"

def F.str.nat_index.k(+len: U32, +i: U32, neg: Bool) -> Nat:
  match neg:
    case True{}:
      U32.to_nat((len + i : U32))
    case False{}:
      U32.to_nat(i)

# a Fire index (negative counts from the end) as a Nat position
def F.str.nat_index(+len: U32, +i: U32) -> Nat:
  F.str.nat_index.k(len, i, F.i32.neg(i))

def F.str.index.k(m: Maybe<&2, Char>) -> Result<&2, &2, String, String>:
  match m:
    case Some{c}:
      Done{SCon{c, SNil{}}}
    case None{}:
      Fail{"string index out of range"}

def F.str.index(+s: String, +i: U32) -> Result<&2, &2, String, String>:
  F.str.index.k(String.get(s, F.str.nat_index(F.str.len(s), i)))

def F.str.slice_from(+s: String, +a: U32) -> String:
  String.drop(s, U32.to_nat(F.str.clamp(F.str.len(s), a)))

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

@unsafe
def F.str.split.go(hit: Bool, +s: String, +sep: String, +cur: String, +acc: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      +rest = String.drop(s, String.length(sep))
      F.str.split.go(String.starts_with(rest, sep), rest, sep, SNil{}, (String.reverse(cur) <> acc))
    case False{}:
      match s:
        case SNil{}:
          List.reverse(&2, String, (String.reverse(cur) <> acc))
        case SCon{h, t}:
          +t2 = t
          F.str.split.go(String.starts_with(t2, sep), t2, sep, SCon{h, cur}, acc)

def F.str.split.pick(+s: String, +sep: String, empty: Bool) -> List<&2, String>:
  match empty:
    case True{}:
      F.str.chars(s)
    case False{}:
      F.str.split.go(String.starts_with(s, sep), s, sep, SNil{}, Nil{})

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

@unsafe
def F.str.replace.go(hit: Bool, +s: String, +from: String, +to: String, +acc: String) -> String:
  match hit:
    case True{}:
      +rest = String.drop(s, String.length(from))
      F.str.replace.go(String.starts_with(rest, from), rest, from, to, String.append(String.reverse(to), acc))
    case False{}:
      match s:
        case SNil{}:
          String.reverse(acc)
        case SCon{h, t}:
          +t2 = t
          F.str.replace.go(String.starts_with(t2, from), t2, from, to, SCon{h, acc})

def F.str.replace.pick(+s: String, +from: String, +to: String, empty: Bool) -> String:
  match empty:
    case True{}:
      s
    case False{}:
      F.str.replace.go(String.starts_with(s, from), s, from, to, SNil{})

def F.str.replace(+s: String, +from: String, +to: String) -> String:
  F.str.replace.pick(s, from, to, String.is_empty(from))

@unsafe
def F.str.index_of.go(hit: Bool, s: String, +p: String, +i: U32) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      match s:
        case SNil{}:
          None{}
        case SCon{h, t}:
          +t2 = t
          F.str.index_of.go(String.starts_with(t2, p), t2, p, (i + 1 : U32))

def F.str.index_of(+s: String, +p: String) -> Maybe<&2, U32>:
  F.str.index_of.go(String.starts_with(s, p), s, p, 0)

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

# -- Ranges -------------------------------------------------------------------
type F.Range is Data:
  F.Range.mk{start: U32, end: U32}

def F.range.start(r: F.Range) -> U32:
  match r:
    case F.Range.mk{s, e}:
      s

def F.range.end(r: F.Range) -> U32:
  match r:
    case F.Range.mk{s, e}:
      e

def F.range.to_list.go(n: Nat, +i: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      F.range.to_list.go(p, (i + 1 : U32), (i <> acc))

def F.range.to_list(+a: U32, +b: U32) -> List<&2, U32>:
  F.range.to_list.go(U32.to_nat(F.i32.max((b - a : U32), 0)), a, Nil{})

def F.range.list(r: F.Range) -> List<&2, U32>:
  match r:
    case F.Range.mk{s, e}:
      F.range.to_list(s, e)

def F.range.len(r: F.Range) -> U32:
  match r:
    case F.Range.mk{s, e}:
      F.i32.max((e - s : U32), 0)

def F.range.contains(r: F.Range, +x: U32) -> Bool:
  match r:
    case F.Range.mk{s, e}:
      Bool.and(F.i32.ge(x, s), F.i32.lt(x, e))

def F.range.index.k(+s: U32, +e: U32, +i: U32, neg: Bool) -> U32:
  match neg:
    case True{}:
      (e + i : U32)
    case False{}:
      (s + i : U32)

def F.range.index(r: F.Range, +i: U32) -> U32:
  match r:
    case F.Range.mk{s, e}:
      F.range.index.k(s, e, i, F.i32.neg(i))

def F.range.slice(r: F.Range, +a: U32, +b: U32) -> F.Range:
  match r:
    case F.Range.mk{+s, +e}:
      F.Range.mk{(s + F.str.clamp((e - s : U32), a) : U32), (s + F.str.clamp((e - s : U32), b) : U32)}

def F.range.slice_from(r: F.Range, +a: U32) -> F.Range:
  match r:
    case F.Range.mk{+s, +e}:
      F.Range.mk{(s + F.str.clamp((e - s : U32), a) : U32), e}

def F.range.show(r: F.Range) -> String:
  match r:
    case F.Range.mk{s, e}:
      F.i32.show(s) ++ ".." ++ F.i32.show(e)

def F.range.eq(a: F.Range, b: F.Range) -> Bool:
  match a:
    case F.Range.mk{s1, e1}:
      match b:
        case F.Range.mk{s2, e2}:
          Bool.and(U32.is_eq(s1, s2), U32.is_eq(e1, e2))

# -- Lists --------------------------------------------------------------------
def F.list.len(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

def F.list.is_empty(-A: Data, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      False{}

def F.list.tail(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def F.list.head_unsafe(-A: Data, xs: List<&2, A>) -> A:
  match xs:
    case Nil{}:
      F.crash(A, "empty list")
    case h <> t:
      h

def F.list.head_or_abort(-A: Data, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  match xs:
    case Nil{}:
      Fail{"the stream produced no item"}
    case h <> t:
      Done{h}

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

def F.list.last_or_abort.k(-A: Data, m: Maybe<&2, A>) -> Result<&2, &2, String, A>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"pop from an empty list"}

def F.list.last_or_abort(-A: Data, xs: List<&2, A>) -> Result<&2, &2, String, A>:
  F.list.last_or_abort.k(A, F.list.last(A, xs))

def F.list.reverse(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  List.reverse(&2, A, xs)

def F.list.append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  List.append(&2, A, xs, ys)

def F.list.push(-A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:
  List.append(&2, A, xs, [x])

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

def F.list.index.k(-A: Data, m: Maybe<&2, A>) -> Result<&2, &2, String, A>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"list index out of range"}

def F.list.index(-A: Data, +xs: List<&2, A>, +i: U32) -> Result<&2, &2, String, A>:
  F.list.index.k(A, List.get(&2, A, xs, F.str.nat_index(F.list.len(A, xs), i)))

def F.list.slice.k(-A: Data, xs: List<&2, A>, +a: U32, +b: U32) -> List<&2, A>:
  List.take(&2, A, List.drop(&2, A, xs, U32.to_nat(a)), U32.to_nat(F.i32.max((b - a : U32), 0)))

def F.list.slice(-A: Data, +xs: List<&2, A>, +a: U32, +b: U32) -> List<&2, A>:
  F.list.slice.k(A, xs, F.str.clamp(F.list.len(A, xs), a), F.str.clamp(F.list.len(A, xs), b))

def F.list.slice_from(-A: Data, +xs: List<&2, A>, +a: U32) -> List<&2, A>:
  List.drop(&2, A, xs, U32.to_nat(F.str.clamp(F.list.len(A, xs), a)))

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
      Fail{"list index out of range"}

def F.list.set(-A: Data, +xs: List<&2, A>, +i: U32, +v: A) -> Result<&2, &2, String, List<&2, A>>:
  F.list.set.k(A, xs, i, v, Bool.and(F.i32.lt(i, F.list.len(A, xs)), F.i32.ge(i, (0 - F.list.len(A, xs) : U32))))

def F.list.sum_u32(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case h <> t:
      (h + F.list.sum_u32(t) : U32)

def F.list.sum_f32(xs: List<&2, F32>) -> F32:
  match xs:
    case Nil{}:
      0.0
    case h <> t:
      (h + F.list.sum_f32(t) : F32)

def F.list.fold_i32.pick(+acc: U32, +h: U32, take: Bool) -> U32:
  match take:
    case True{}:
      h
    case False{}:
      acc

def F.list.fold_i32.go(xs: List<&2, U32>, +acc: U32, +pick_lt: Bool) -> U32:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      F.list.fold_i32.go(t, F.list.fold_i32.pick(acc, h, F.bool.eq(pick_lt, F.i32.lt(h, acc))), pick_lt)

def F.list.min_i32(xs: List<&2, U32>) -> Result<&2, &2, String, U32>:
  match xs:
    case Nil{}:
      Fail{"min() of an empty list"}
    case h <> t:
      Done{F.list.fold_i32.go(t, h, True{})}

def F.list.max_i32(xs: List<&2, U32>) -> Result<&2, &2, String, U32>:
  match xs:
    case Nil{}:
      Fail{"max() of an empty list"}
    case h <> t:
      Done{F.list.fold_i32.go(t, h, False{})}

def F.list.fold_f32.pick(+acc: F32, +h: F32, take: Bool) -> F32:
  match take:
    case True{}:
      h
    case False{}:
      acc

def F.list.fold_f32.go(xs: List<&2, F32>, +acc: F32, +pick_lt: Bool) -> F32:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      F.list.fold_f32.go(t, F.list.fold_f32.pick(acc, h, F.bool.eq(pick_lt, F32.is_lt(h, acc))), pick_lt)

def F.list.min_f32(xs: List<&2, F32>) -> Result<&2, &2, String, F32>:
  match xs:
    case Nil{}:
      Fail{"min() of an empty list"}
    case h <> t:
      Done{F.list.fold_f32.go(t, h, True{})}

def F.list.max_f32(xs: List<&2, F32>) -> Result<&2, &2, String, F32>:
  match xs:
    case Nil{}:
      Fail{"max() of an empty list"}
    case h <> t:
      Done{F.list.fold_f32.go(t, h, False{})}

def F.list.join(xs: List<&2, String>, +sep: String) -> String:
  String.join(xs, sep)

def F.list.contains(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(eq(h, x), F.list.contains(~A, ~eq, t, x))

@unsafe
def F.list.index_of.go(~A: Data, ~eq: A -> A -> Bool, hit: Bool, xs: List<&2, A>, +x: A, +i: U32) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      match xs:
        case Nil{}:
          None{}
        case h <> t:
          F.list.index_of.go(~A, ~eq, eq(h, x), t, x, (i + 1 : U32))

def F.list.index_of(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Maybe<&2, U32>:
  F.list.index_of.go(~A, ~eq, False{}, xs, x, (0 - 1 : U32))

def F.list.flatten(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  List.concat(&2, A, xss)

def F.list.repeat(-A: Data, +x: A, +n: U32) -> List<&2, A>:
  List.replicate(A, U32.to_nat(F.i32.max(n, 0)), x)

def F.list.enumerate.go(-A: Data, xs: List<&2, A>, +i: U32) -> List<&2, F.Pair<U32, A>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (F.Pair.mk{i, h} <> F.list.enumerate.go(A, t, (i + 1 : U32)))

def F.list.enumerate(-A: Data, xs: List<&2, A>) -> List<&2, F.Pair<U32, A>>:
  F.list.enumerate.go(A, xs, 0)

def F.list.zip(-A: Data, -B: Data, xs: List<&2, A>, ys: List<&2, B>) -> List<&2, F.Pair<A, B>>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case h <> t Nil{}:
      Nil{}
    case h <> t h2 <> t2:
      (F.Pair.mk{h, h2} <> F.list.zip(A, B, t, t2))

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

def F.list.lt(~A: Data, ~lt: A -> A -> Bool, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      False{}
    case Nil{} h2 <> t2:
      True{}
    case h <> t Nil{}:
      False{}
    case +h <> t +h2 <> t2:
      Bool.or(lt(h, h2), Bool.and(eq(h, h2), F.list.lt(~A, ~lt, ~eq, t, t2)))

def F.list.sort.le(~A: Data, ~lt: A -> A -> Bool, a: A, b: A) -> Bool:
  Bool.not(lt(b, a))

# sort by precomputed keys: zip, sort the pairs by key, drop the keys
def F.list.sort_decorated.key(~K: Data, ~A: Data, e: Unit, p: F.Pair<K, A>) -> K:
  match p:
    case F.Pair.mk{k, v}:
      k

def F.list.sort_decorated.val(~K: Data, ~A: Data, e: Unit, p: F.Pair<K, A>) -> A:
  match p:
    case F.Pair.mk{k, v}:
      v

# -- Lists: higher-order, threading an environment ---------------------------
def F.list.map_env(~E: Data, ~A: Data, ~B: Data, ~f: E -> A -> B, +e: E, xs: List<&2, A>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (f(e, h) <> F.list.map_env(~E, ~A, ~B, ~f, e, t))

# insertion sort (stable), enough for the sizes tests use
# does x sort before the head of acc? (true for an empty acc)
def F.list.sort_by_key_env.before(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, +x: A, acc: List<&2, A>) -> Bool:
  match acc:
    case Nil{}:
      True{}
    case h <> t:
      lt(key(e, x), key(e, h))

@unsafe
def F.list.sort_by_key_env.insert(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, before: Bool, +e: E, +x: A, +acc: List<&2, A>) -> List<&2, A>:
  match before:
    case True{}:
      (x <> acc)
    case False{}:
      match acc:
        case Nil{}:
          [x]
        case h <> t:
          +t2 = t
          (h <> F.list.sort_by_key_env.insert(~E, ~A, ~K, ~key, ~lt, F.list.sort_by_key_env.before(~E, ~A, ~K, ~key, ~lt, e, x, t2), e, x, t2))

def F.list.sort_by_key_env.insert_all(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, fuel: Nat, xs: List<&2, A>, +acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      +acc2 = acc
      F.list.sort_by_key_env.insert_all(~E, ~A, ~K, ~key, ~lt, e, fuel, t, F.list.sort_by_key_env.insert(~E, ~A, ~K, ~key, ~lt, F.list.sort_by_key_env.before(~E, ~A, ~K, ~key, ~lt, e, h, acc2), e, h, acc2))

def F.list.sort_by_key_env.merge_sort(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, fuel: Nat, +xs: List<&2, A>) -> List<&2, A>:
  match fuel:
    case 0n:
      xs
    case 1n+f:
      F.list.sort_by_key_env.insert_all(~E, ~A, ~K, ~key, ~lt, e, f, xs, Nil{})

def F.list.sort_by_key_env.go(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, +xs: List<&2, A>) -> List<&2, A>:
  F.list.sort_by_key_env.merge_sort(~E, ~A, ~K, ~key, ~lt, e, U32.to_nat(F.list.len(A, xs)), xs)

def F.list.sort_by_key_env(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, xs: List<&2, A>) -> List<&2, A>:
  F.list.sort_by_key_env.go(~E, ~A, ~K, ~key, ~lt, e, xs)

def F.list.sort_decorated(~K: Data, ~A: Data, ~lt: K -> K -> Bool, keys: List<&2, K>, xs: List<&2, A>) -> List<&2, A>:
  F.list.map_env(~Unit, ~F.Pair<K, A>, ~A, ~F.list.sort_decorated.val(~K, ~A), Unit{}, F.list.sort_by_key_env(~Unit, ~F.Pair<K, A>, ~K, ~F.list.sort_decorated.key(~K, ~A), ~lt, Unit{}, F.list.zip(K, A, keys, xs)))

def F.list.sort(~A: Data, ~lt: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  List.sort(~A, ~F.list.sort.le(~A, ~lt), xs)

def F.list.sort_by_key_env.le(~E: Data, ~A: Data, ~K: Data, ~key: E -> A -> K, ~lt: K -> K -> Bool, +e: E, +a: A, +b: A) -> Bool:
  Bool.not(lt(key(e, b), key(e, a)))

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

def F.list.filter.put(-A: Data, h: A, +r: List<&2, A>, keep: Bool) -> List<&2, A>:
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

# -- Lists of results: the per-element railway --------------------------------
def F.list.rmap.one(~E: Data, ~A: Data, ~B: Data, ~X: Data, ~f: E -> A -> B, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, X, B>:
  match r:
    case Done{v}:
      Done{f(e, v)}
    case Fail{x}:
      Fail{x}

def F.list.rmap_env(~E: Data, ~A: Data, ~B: Data, ~X: Data, ~f: E -> A -> B, +e: E, xs: List<&2, Result<&2, &2, X, A>>) -> List<&2, Result<&2, &2, X, B>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (F.list.rmap.one(~E, ~A, ~B, ~X, ~f, e, h) <> F.list.rmap_env(~E, ~A, ~B, ~X, ~f, e, t))

def F.list.rfilter.keep(~E: Data, ~A: Data, ~X: Data, ~f: E -> A -> Bool, +e: E, r: Result<&2, &2, X, A>) -> Bool:
  match r:
    case Done{v}:
      f(e, v)
    case Fail{x}:
      True{}

def F.list.rfilter_env(~E: Data, ~A: Data, ~X: Data, ~f: E -> A -> Bool, +e: E, xs: List<&2, Result<&2, &2, X, A>>) -> List<&2, Result<&2, &2, X, A>>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      F.list.filter.put(Result<&2, &2, X, A>, h, F.list.rfilter_env(~E, ~A, ~X, ~f, e, t), F.list.rfilter.keep(~E, ~A, ~X, ~f, e, h))

def F.list.rhandle.one(~E: Data, ~X: Data, ~A: Data, ~f: E -> X -> A, +e: E, r: Result<&2, &2, X, A>) -> A:
  match r:
    case Done{v}:
      v
    case Fail{x}:
      f(e, x)

def F.list.rhandle_env(~E: Data, ~X: Data, ~A: Data, ~f: E -> X -> A, +e: E, xs: List<&2, Result<&2, &2, X, A>>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (F.list.rhandle.one(~E, ~X, ~A, ~f, e, h) <> F.list.rhandle_env(~E, ~X, ~A, ~f, e, t))

def F.list.rhandle_value.one(-X: Data, -A: Data, r: Result<&2, &2, X, A>, +d: A) -> A:
  match r:
    case Done{v}:
      v
    case Fail{x}:
      d

def F.list.rhandle_value(-X: Data, -A: Data, xs: List<&2, Result<&2, &2, X, A>>, +d: A) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      (F.list.rhandle_value.one(X, A, h, d) <> F.list.rhandle_value(X, A, t, d))

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

# -- Result -------------------------------------------------------------------
def F.result.show(~X: Data, ~A: Data, ~fx: X -> String, ~fa: A -> String, r: Result<&2, &2, X, A>) -> String:
  match r:
    case Done{v}:
      "{ok: " ++ fa(v) ++ "}"
    case Fail{x}:
      "{err: " ++ fx(x) ++ "}"

def F.result.eq.err(~X: Data, ~A: Data, ~ex: X -> X -> Bool, x: X, b: Result<&2, &2, X, A>) -> Bool:
  match b:
    case Done{w}:
      False{}
    case Fail{y}:
      ex(x, y)

def F.result.eq.ok(~X: Data, ~A: Data, ~ea: A -> A -> Bool, v: A, b: Result<&2, &2, X, A>) -> Bool:
  match b:
    case Done{w}:
      ea(v, w)
    case Fail{y}:
      False{}

def F.result.eq(~X: Data, ~A: Data, ~ex: X -> X -> Bool, ~ea: A -> A -> Bool, a: Result<&2, &2, X, A>, +b: Result<&2, &2, X, A>) -> Bool:
  match a:
    case Done{v}:
      F.result.eq.ok(~X, ~A, ~ea, v, b)
    case Fail{x}:
      F.result.eq.err(~X, ~A, ~ex, x, b)

def F.result.or(-X: Data, -A: Data, r: Result<&2, &2, X, A>, d: A) -> A:
  match r:
    case Done{v}:
      v
    case Fail{x}:
      d

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

def F.result.map_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> B, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, X, B>:
  match r:
    case Done{v}:
      Done{f(e, v)}
    case Fail{x}:
      Fail{x}

def F.result.bind_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> Result<&2, &2, X, B>, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, X, B>:
  match r:
    case Done{v}:
      f(e, v)
    case Fail{x}:
      Fail{x}

def F.result.map_res_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> Result<&2, &2, String, B>, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, String, Result<&2, &2, X, B>>:
  match r:
    case Done{v}:
      do Result<&2, &2, String, Result<&2, &2, X, B>>:
        w : B <- f(e, v)
        return Done{w}
    case Fail{x}:
      Done{Fail{x}}

def F.result.bind_res_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> Result<&2, &2, String, Result<&2, &2, X, B>>, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, String, Result<&2, &2, X, B>>:
  match r:
    case Done{v}:
      f(e, v)
    case Fail{x}:
      Done{Fail{x}}

def F.result.map_io_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> IO(B), +e: E, r: Result<&2, &2, X, A>) -> IO(Result<&2, &2, X, B>):
  match r:
    case Done{v}:
      do IO<Result<&2, &2, X, B>>:
        w : B <- f(e, v)
        return Done{w}
    case Fail{x}:
      IO.pure(Result<&2, &2, X, B>, Fail{x})

def F.result.bind_io_env(~E: Data, ~X: Data, ~A: Data, ~B: Data, ~f: E -> A -> IO(Result<&2, &2, X, B>), +e: E, r: Result<&2, &2, X, A>) -> IO(Result<&2, &2, X, B>):
  match r:
    case Done{v}:
      f(e, v)
    case Fail{x}:
      IO.pure(Result<&2, &2, X, B>, Fail{x})

def F.result.handle_env(~E: Data, ~X: Data, ~A: Data, ~f: E -> X -> A, +e: E, r: Result<&2, &2, X, A>) -> A:
  match r:
    case Done{v}:
      v
    case Fail{x}:
      f(e, x)

def F.result.handle_res_env(~E: Data, ~X: Data, ~A: Data, ~f: E -> X -> Result<&2, &2, String, A>, +e: E, r: Result<&2, &2, X, A>) -> Result<&2, &2, String, A>:
  match r:
    case Done{v}:
      Done{v}
    case Fail{x}:
      f(e, x)

def F.result.handle_io_env(~E: Data, ~X: Data, ~A: Data, ~f: E -> X -> IO(A), +e: E, r: Result<&2, &2, X, A>) -> IO(A):
  match r:
    case Done{v}:
      IO.pure(A, v)
    case Fail{x}:
      f(e, x)

# -- Maps (string-keyed dictionaries) -----------------------------------------
def F.map.lookup(-V: Data, +m: Map<&2, V>, key: String) -> Maybe<&2, V>:
  F.snd(Map<&2, V>, Maybe<&2, V>, Map.pop(&2, V, m, key))

def F.map.get_or_abort.k(-V: Data, m: Maybe<&2, V>) -> Result<&2, &2, String, V>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{"missing key"}

def F.map.get_or_abort(-V: Data, +m: Map<&2, V>, key: String) -> Result<&2, &2, String, V>:
  F.map.get_or_abort.k(V, F.map.lookup(V, m, key))

def F.map.has(-V: Data, +m: Map<&2, V>, key: String) -> Bool:
  F.snd(Map<&2, V>, Bool, Map.has(&2, V, m, key))

def F.map.size(-V: Data, m: Map<&2, V>) -> U32:
  U32.from_nat(Map.size(&2, V, m))

def F.io.err_text(e: U32 & String) -> String:
  (code, msg) = e
  msg

def F.io.read_file.fin(r: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, String, String>:
  match r:
    case Done{s}:
      Done{s}
    case Fail{e}:
      Fail{F.io.err_text(e)}

# a key from Map.keys always has a value; a missing one is skipped
def F.map.entries.one(-V: Data, k: String, mv: Maybe<&2, V>, rest: List<&2, F.Pair<String, V>>) -> List<&2, F.Pair<String, V>>:
  match mv:
    case Some{v}:
      (F.Pair.mk{k, v} <> rest)
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
    case F.Pair.mk{k, v} <> t:
      ", " ++ k ++ ": " ++ f(v) ++ F.map.show.go(~V, ~f, t)

def F.map.show.list(~V: Data, ~f: V -> String, kvs: List<&2, F.Pair<String, V>>) -> String:
  match kvs:
    case Nil{}:
      "{}"
    case F.Pair.mk{k, v} <> t:
      "{" ++ k ++ ": " ++ f(v) ++ F.map.show.go(~V, ~f, t) ++ "}"

def F.map.show(~V: Data, ~f: V -> String, m: Map<&2, V>) -> String:
  F.map.show.list(~V, ~f, F.map.entries(V, m))

def F.map.eq.lists(~V: Data, ~eq: V -> V -> Bool, xs: List<&2, F.Pair<String, V>>, ys: List<&2, F.Pair<String, V>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} h2 <> t2:
      False{}
    case h <> t Nil{}:
      False{}
    case F.Pair.mk{k1, v1} <> t F.Pair.mk{k2, v2} <> t2:
      Bool.and(Bool.and(String.eq(k1, k2), eq(v1, v2)), F.map.eq.lists(~V, ~eq, t, t2))

def F.map.eq(~V: Data, ~eq: V -> V -> Bool, a: Map<&2, V>, b: Map<&2, V>) -> Bool:
  F.map.eq.lists(~V, ~eq, F.map.entries(V, a), F.map.entries(V, b))

# -- Effects ------------------------------------------------------------------
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
