# A match on a computed value goes through a generated case eliminator:
# one def per declared type, thunks for the arms. The thunks may capture
# locals, and the enclosing def stays structurally recursive.
import Base

def F.Maybe.case(-A: Data, -R: Type, m: Maybe<&2, A>, none: Unit -> R, some: A -> R) -> R:
  match m:
    case None{}:
      none(Unit{})
    case Some{v}:
      some(v)

def find_gt(xs: List<&2, U32>, +k: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Bool.pick(Unit -> Maybe<&2, U32>, U32.is_gt(h, k), _ => Some{h}, _ => find_gt(t, k))(Unit{})

def report(xs: List<&2, U32>, +label: String) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, +t}:
      do IO<Unit>:
        F.Maybe.case(U32, IO(Unit), find_gt(t, h), _ => IO.print(label ++ ": nothing after " ++ U32.show(h)), v => IO.print(label ++ ": " ++ U32.show(h) ++ " then " ++ U32.show(v)))
        report(t, label)

def main() -> IO(Unit):
  do IO<Unit>:
    report([3, 1, 4, 1, 5], "scan")
