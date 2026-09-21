# A constrained generic def: the operations the body needs on its type
# parameter are template parameters (dictionary passing through ~),
# so one def serves every element type and Bend makes the copies.
import Base

type Tree<-A: Data> is Data:
  Leaf{}
  Node{l: Tree<A>, v: A, r: Tree<A>}

def insert(~A: Data, ~lt: A -> A -> Bool, +x: A, t: Tree<A>) -> Tree<A>:
  match t:
    case Leaf{}:
      Node{Leaf{}, x, Leaf{}}
    case Node{+l, +v, +r}:
      Bool.pick(Unit -> Tree<A>, lt(x, v), _ => Node{insert(~A, ~lt, x, l), v, r}, _ => Node{l, v, insert(~A, ~lt, x, r)})(Unit{})

def to_list(~A: Data, t: Tree<A>) -> List<&2, A>:
  match t:
    case Leaf{}:
      []
    case Node{l, v, r}:
      List.append(&2, A, to_list(~A, l), v <> to_list(~A, r))

def size(-A: Data, t: Tree<A>) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{l, v, r}:
      (1n + Nat.add(size(A, l), size(A, r)) : Nat)

# a closed law about one instance of the generic def
law insert_example:
  {to_list(~U32, insert(~U32, ~U32.is_lt, 2, insert(~U32, ~U32.is_lt, 3, insert(~U32, ~U32.is_lt, 1, Leaf{})))) == [1, 2, 3] : List<&2, U32>}

def insert_example():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    +s : Tree<String> = insert(~String, ~String.is_lt, "b", insert(~String, ~String.is_lt, "a", Leaf{}))
    IO.print(String.join(to_list(~String, s), ","))
    IO.print(Nat.show(size(String, s)))
