# A law over a finite type is proven by a case split the compiler can
# generate: match every constructor, close each case with {==}.
import Base

type Player is Data:
  X{}
  O{}

def other(p: Player) -> Player:
  match p:
    case X{}:
      O{}
    case O{}:
      X{}

law other_involutive:
  for p: Player
  {other(other(p)) == p : Player}

def other_involutive(p):
  match p:
    case X{}:
      {==}
    case O{}:
      {==}

def show(p: Player) -> String:
  match p:
    case X{}:
      "X"
    case O{}:
      "O"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(other(X{})))
