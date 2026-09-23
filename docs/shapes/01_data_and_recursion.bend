# A declared data type, structural recursion, a branch under a self-call,
# and a closed law proven by normalization. Nothing is @unsafe.
import Base

type Tree<-A: Data> is Data:
  Leaf{}
  Node{l: Tree<A>, v: A, r: Tree<A>}

# an unconstrained generic def: the type parameter is erased
def size(-A: Data, t: Tree<A>) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{l, v, r}:
      (1n + Nat.add(size(A, l), size(A, r)) : Nat)

# the match on the parameter stays a real match (that is what the
# termination checker reads); the branch that contains the self-call is a
# Bool.pick over thunks, so no helper def has to call back into insert
def insert(+x: U32, t: Tree<U32>) -> Tree<U32>:
  match t:
    case Leaf{}:
      Node{Leaf{}, x, Leaf{}}
    case Node{+l, +v, +r}:
      Bool.pick(Unit -> Tree<U32>, U32.is_lt(x, v), _ => Node{insert(x, l), v, r}, _ => Node{l, v, insert(x, r)})(Unit{})

def to_list(t: Tree<U32>) -> List<&2, U32>:
  match t:
    case Leaf{}:
      []
    case Node{l, v, r}:
      List.append(&2, U32, to_list(l), v <> to_list(r))

def show_list(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      U32.show(h) ++ " " ++ show_list(t)

# a closed claim: both sides compute to the same term
law insert_example:
  {to_list(insert(2, insert(3, insert(1, Leaf{})))) == [1, 2, 3] : List<&2, U32>}

def insert_example():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_list(to_list(insert(2, insert(3, insert(1, Leaf{}))))))
    IO.print(Nat.show(size(U32, insert(2, insert(3, insert(1, Leaf{}))))))
