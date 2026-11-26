import Base
import ./Text.bend as Tx
import ./Load.bend as Load
import ./HsPrelude.bend as HsPrelude
import ./Cata_Base.bend as CB
import ./Telomare_EAL.bend as EAL
import ./Telomare_Fast.bend as Fast

# telomare --fast FILE with its standard input read first: the loop is cata's
# too (Fast.hs's runFastLoop, IO as the state of the console, Cata.Base's
# World). Bend's own here: the arguments, the files' texts, the printing.

def out.of(w: CB.World) -> List<&2, Char>:
  match w:
    case CB.World.World{i, o, f}:
      o

# IO.print ends the line itself
def unline(r: List<&2, Char>) -> List<&2, Char>:
  match r:
    case c <> t:
      match c:
        case '\n':
          t
        case d:
          d <> t
    case Nil{}:
      Nil{}

def fin(r: Either<&2, &1, List<&2, Char>, Sigma<&1, &1, Fast.FastMeter, (_ => CB.World)>>) -> IO(Unit):
  match r:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{p}:
      (m, w) = p
      IO.print(String.from_list(List.reverse(&2, Char, unline(List.reverse(&2, Char, out.of(w))))))

def input(r: Result<&1, &1, String, String>) -> List<&2, Char>:
  match r:
    case Done{s}:
      String.to_list(s)
    case Fail{e}:
      Nil{}

def run(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, List<&2, Char>, Fast.FastExpr>>, inp: List<&2, Char>) -> IO(Unit):
  match e:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inl{m}}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inr{prog}}:
      fin(Fast.runFastLoop(Some{Fast.defaultFastFuel()}, prog, CB.World.World{inp, [], HsPrelude.HsMap.empty(~List<&2, Char>, ~List<&2, Char>)}))

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      +p = Load.split(String.to_list(f))
      do IO<Unit>:
        i : Result<&1, &1, String, String> <- Tx.read_file("/dev/stdin")
        +mods : List<&2, Load.Mod()> <- Load.modules(p)
        run(Fast.compileFastWithin(EAL.defaultVariableBudget(), mods, Load.base.name(Load.file.of(p))), input(i))
    case Nil{}:
      IO.die(Unit, 2, "usage: telomare-fast-batch FILE.tel < INPUT")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
