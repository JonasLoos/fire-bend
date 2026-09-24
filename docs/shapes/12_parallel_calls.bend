# Independent self-calls of a pure def run in parallel: in one term as a
# parallel let around it, and in a block as a parallel let statement after
# the lets the calls read. A binder the rest uses twice is `+`.
import Base

type Tree<-A: Data> is Data:
  Leaf{}
  Node{l: Tree<A>, v: A, r: Tree<A>}

def size(-A: Data, t: Tree<A>) -> U32:
  match t:
    case Leaf{}:
      0
    case Node{l, v, r}:
      (a b = size(A, l) size(A, r); ((a + 1 : U32) + b : U32))

def depth(t: Tree<U32>) -> U32:
  match t:
    case Leaf{}:
      0
    case Node{l, v, r}:
      +a +b = depth(l) depth(r)
      (1 + Bool.pick(U32, U32.is_lt(b, a), a, b) : U32)

def build(n: Nat) -> Tree<U32>:
  match n:
    case 0n:
      Leaf{}
    case 1n+p:
      +q = p
      Node{build(q), U32.from_nat(q), build(q)}

law size_three:
  {size(U32, build(3n)) == 7 : U32}

def size_three():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    +t : Tree<U32> <- IO.pure(Tree<U32>, build(16n))
    IO.print(U32.show(size(U32, t)))
    IO.print(U32.show(depth(t)))
