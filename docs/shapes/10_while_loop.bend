# A while-loop has no structure to recurse on, so its driver is @unsafe,
# and so is the def that contains it (an `unsafe def` in Fire). The condition
# for the next iteration is computed at the call site, which keeps the
# driver a single def.
import Base

def step(+a: U32) -> U32:
  +b = U32.xor(a, (a << 13n : U32))
  +c = U32.xor(b, (b >> 17n : U32))
  U32.xor(c, (c << 5n : U32))

@unsafe
def F.while(+n: U32, acc: U32, go: Bool) -> U32:
  match go:
    case False{}:
      acc
    case True{}:
      F.while((n - 1 : U32), step(acc), U32.is_gt(n, 1))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(F.while(1000, 1, True{})))
