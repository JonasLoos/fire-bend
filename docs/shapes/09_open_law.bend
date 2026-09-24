# An open claim with a hypothesis. The hypothesis is an extra parameter of
# equality type; `where` would make xs a dependent pair instead. With no
# proof, `bend --check-only` reports the claim as a TODO, which is the
# "stated, not proven" state Fire reports to the user.
import Base

def sorted.go(t: List<&2, U32>, +h: U32) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{+h2, t2}:
      Bool.and(U32.is_le(h, h2), sorted.go(t2, h2))

def sorted(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      sorted.go(t, h)

def insert(+x: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [x]
    case Con{+h, +t}:
      Bool.pick(Unit -> List<&2, U32>, U32.is_le(x, h), _ => x <> h <> t, _ => h <> insert(x, t))(Unit{})

law insert_keeps_sorted:
  for +x: U32
  for xs: List<&2, U32>
  for h: {sorted(xs) == True{} : Bool}
  {sorted(insert(x, xs)) == True{} : Bool}

law insert_example:
  {insert(3, [1, 2, 5]) == [1, 2, 3, 5] : List<&2, U32>}

def insert_example():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Bool.show(sorted(insert(3, [1, 2, 5]))))
