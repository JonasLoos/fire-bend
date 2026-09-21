# Branches inside IO and Result blocks through Bool.pick over thunks, in a
# structurally recursive def; the abort effect is a Result the caller
# unwraps at the IO boundary.
import Base

def F.unwrap(-A: Data, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Done{v}:
      IO.pure(A, v)
    case Fail{e}:
      IO.die(A, 1, e)

def report(xs: List<&2, U32>, +total: U32) -> IO(U32):
  match xs:
    case Nil{}:
      IO.pure(U32, total)
    case Con{+h, t}:
      do IO<U32>:
        big : Bool = U32.is_gt(h, 2)
        Bool.pick(Unit -> IO(Unit), big, _ => IO.print("big " ++ U32.show(h)), _ => IO.print("small " ++ U32.show(h)))(Unit{})
        report(t, (total + h : U32))

def safe_div(+a: U32, +b: U32) -> Result<&2, &2, String, U32>:
  Bool.pick(Unit -> Result<&2, &2, String, U32>, U32.is_zero(b), _ => Fail{"division by zero"}, _ => Done{U32.div(a, b)})(Unit{})

def avg(xs: List<&2, U32>, +n: U32, +acc: U32) -> Result<&2, &2, String, U32>:
  match xs:
    case Nil{}:
      safe_div(acc, n)
    case Con{h, t}:
      avg(t, n, (acc + h : U32))

def main() -> IO(Unit):
  do IO<Unit>:
    s : U32 <- report([1, 5, 2, 9], 0)
    IO.print(U32.show(s))
    r : U32 <- F.unwrap(U32, avg([2, 4, 6], 3, 0))
    IO.print(U32.show(r))
    z : U32 <- F.unwrap(U32, avg([], 0, 0))
    IO.print(U32.show(z))
