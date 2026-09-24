# A def that counts an int down and opens with a branch on its parameters.
# The condition is a parameter of a worker def, which matches it: no thunk,
# and the fuel still descends first. The def keeps its name and parameters
# and answers the worker on its condition; a self-call goes to the worker
# with the condition on its own arguments, each bound once.
import Base

def fib.F.go(__fuel: Nat, +n: U32, __c: Bool) -> U32:
  match __fuel:
    case 0n:
      0
    case 1n++__fuel_:
      match __c:
        case True{}:
          n
        case False{}:
          +a : U32 = (n - 1 : U32)
          +b : U32 = (n - 2 : U32)
          (fib.F.go(__fuel_, a, U32.is_le(a, 1)) + fib.F.go(__fuel_, b, U32.is_le(b, 1)) : U32)

def fib(__fuel: Nat, +n: U32) -> U32:
  fib.F.go(__fuel, n, U32.is_le(n, 1))

law fib_ten:
  {fib(11n, 10) == 55 : U32}

def fib_ten():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(fib(21n, 20)))
