# for-loops as total drivers: the body is a template returning a control
# value, the driver recurses structurally on the list or on a Nat count.
# break, continue and the loop state all fit in Ctl; nothing is @unsafe.
import Base

type Ctl<-S: Data> is Data:
  Next{s: S}
  Break{s: S}

# for x in xs
def F.for_list(~S: Data, ~A: Data, ~E: Data, ~body: E -> S -> A -> Ctl<S>, +env: E, xs: List<&2, A>, c: Ctl<S>) -> S:
  match xs c:
    case Nil{} Next{s}:
      s
    case Nil{} Break{s}:
      s
    case Con{h, t} Break{s}:
      s
    case Con{h, t} Next{s}:
      F.for_list(~S, ~A, ~E, ~body, env, t, body(env, s, h))

# for i in a..b: a Nat countdown (free at runtime), i rides along
def F.for_range(~S: Data, ~E: Data, ~body: E -> S -> U32 -> Ctl<S>, +env: E, n: Nat, +i: U32, c: Ctl<S>) -> S:
  match n c:
    case 0n Next{s}:
      s
    case 0n Break{s}:
      s
    case 1n+p Break{s}:
      s
    case 1n+p Next{s}:
      F.for_range(~S, ~E, ~body, env, p, (i + 1 : U32), body(env, s, i))

# the user's loop body: add x to the total, break once it passes the limit
def body.stop(+s: U32, over: Bool) -> Ctl<U32>:
  match over:
    case True{}:
      Break{s}
    case False{}:
      Next{s}

# code passed as a template has plain parameters and rebinds with + inside
def body(limit: U32, s: U32, x: U32) -> Ctl<U32>:
  +limit = limit
  +t = (s + x : U32)
  body.stop(t, U32.is_gt(t, limit))

def main() -> IO(Unit):
  do IO<Unit>:
    a : U32 = F.for_list(~U32, ~U32, ~U32, ~body, 10, [1, 2, 3, 4, 5, 6], Next{0})
    IO.print(U32.show(a))
    b : U32 = F.for_range(~U32, ~U32, ~body, 100, U32.to_nat(1000), 1, Next{0})
    IO.print(U32.show(b))
