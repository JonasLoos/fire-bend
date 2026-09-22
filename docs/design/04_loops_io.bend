# The same loop driver in IO: the recursive call sits inside the do block
# and the termination checker still accepts it.
import Base

type Ctl<-S: Data> is Data:
  Next{s: S}
  Break{s: S}

def F.for_list_io(~S: Data, ~A: Data, ~E: Data, ~body: E -> S -> A -> IO(Ctl<S>), +env: E, xs: List<&2, A>, c: Ctl<S>) -> IO(S):
  match xs c:
    case Nil{} Next{s}:
      IO.pure(S, s)
    case Nil{} Break{s}:
      IO.pure(S, s)
    case Con{h, t} Break{s}:
      IO.pure(S, s)
    case Con{h, t} Next{s}:
      do IO<S>:
        c2 : Ctl<S> <- body(env, s, h)
        F.for_list_io(~S, ~A, ~E, ~body, env, t, c2)

def body(limit: U32, s: U32, x: U32) -> IO(Ctl<U32>):
  +limit = limit
  +x = x
  +t = (s + x : U32)
  do IO<Ctl<U32>>:
    IO.print("item " ++ U32.show(x) ++ " total " ++ U32.show(t))
    return Bool.pick(Ctl<U32>, U32.is_gt(t, limit), Break{t}, Next{t})

def main() -> IO(Unit):
  do IO<Unit>:
    a : U32 <- F.for_list_io(~U32, ~U32, ~U32, ~body, 10, [1, 2, 3, 4, 5, 6], Next{0})
    IO.print(U32.show(a))
