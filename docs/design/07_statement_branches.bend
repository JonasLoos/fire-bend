# An if-statement without a self-call or an early return is a helper def
# that answers its live-out variables; the enclosing body stays straight
# line and reads them back through projection defs (a destructuring let
# would be a match on a computed value).
import Base

# a Bend pair is affine, so live-outs travel in a Data record
type F.Out2<-A: Data, -B: Data> is Data:
  F.Out2{a: A, b: B}

def F.Out2.a(-A: Data, -B: Data, p: F.Out2<A, B>) -> A:
  match p:
    case F.Out2{a, b}:
      a

def F.Out2.b(-A: Data, -B: Data, p: F.Out2<A, B>) -> B:
  match p:
    case F.Out2{a, b}:
      b

def step.if1(+x: U32, +y: U32, c: Bool) -> F.Out2<U32, U32>:
  match c:
    case True{}:
      F.Out2{(x + 1 : U32), (y * 2 : U32)}
    case False{}:
      F.Out2{x, (y + 7 : U32)}

def step.if2(+x: U32, c: Bool) -> U32:
  match c:
    case True{}:
      (x * 10 : U32)
    case False{}:
      x

def step(+x: U32, +y: U32) -> U32:
  +r1 = step.if1(x, y, U32.is_even(x))
  +x = F.Out2.a(U32, U32, r1)
  y = F.Out2.b(U32, U32, r1)
  x = step.if2(x, U32.is_lt(x, 5))
  (x + y : U32)

def step_io(+x: U32, +y: U32) -> IO(U32):
  do IO<U32>:
    +r1 : F.Out2<U32, U32> = step.if1(x, y, U32.is_even(x))
    +x : U32 = F.Out2.a(U32, U32, r1)
    +y : U32 = F.Out2.b(U32, U32, r1)
    IO.print(U32.show(x) ++ " " ++ U32.show(y))
    x : U32 = step.if2(x, U32.is_lt(x, 5))
    return (x + y : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(step(4, 1)))
    r : U32 <- step_io(4, 1)
    IO.print(U32.show(r))
