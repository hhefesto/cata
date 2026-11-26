import Base
import ./Text.bend as Tx
import ./Load.bend as Load
import ./HsPrelude.bend as HsPrelude
import ./Cata_Base.bend as CB
import ./Telomare_EAL.bend as EAL
import ./Telomare_Driver.bend as Driver

# telomare FILE (its usual, sized route: runSized and evalLoop), its standard
# input read first: the compile, the sizing, the evaluator and the loop are
# cata's (IO as the state of the console, Cata.Base's World). Bend's own here:
# the arguments, the files' texts, the printing.

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

# what the program printed (IO.print ends the line itself), if anything
def out.put(o: List<&2, Char>) -> IO(Unit):
  match o:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case c <> t:
      IO.print(String.from_list(List.reverse(&2, Char, unline(List.reverse(&2, Char, c <> t)))))

# the end of a run, IO being IOW (Cata.Base: State World under an ExceptT of
# the message an action throws): the output printed so far, then the
# message of an error nothing caught, as GHC's run prints both
def fin.io(r: Either<&2, &2, List<&2, Char>, Unit>, w: CB.World) -> IO(Unit):
  match r:
    case Inl{m}:
      do IO<Unit>:
        out.put(out.of(w))
        IO.die(Unit, 1, String.from_list(m))
    case Inr{u}:
      out.put(out.of(w))

# a failure of the pure code under the run is the program's alone (the
# world it failed in is not kept)
def fin(r: Either<&2, &1, List<&2, Char>, Sigma<&1, &1, Either<&2, &2, List<&2, Char>, Unit>, (_ => CB.World)>>) -> IO(Unit):
  match r:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{p}:
      (u, w) = p
      fin.io(u, w)

def input(r: Result<&1, &1, String, String>) -> List<&2, Char>:
  match r:
    case Done{s}:
      String.to_list(s)
    case Fail{e}:
      Nil{}

def run(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, List<&2, Char>, Driver.CompiledProgram>>, inp: List<&2, Char>) -> IO(Unit):
  match e:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inl{m}}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inr{cp}}:
      fin(Driver.evalLoop(Driver.programIteration(cp), CB.World.World{inp, [], HsPrelude.HsMap.empty(~List<&2, Char>, ~List<&2, Char>)}))

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      +p = Load.split(String.to_list(f))
      do IO<Unit>:
        i : Result<&1, &1, String, String> <- Tx.read_file("/dev/stdin")
        +mods : List<&2, Load.Mod()> <- Load.modules(p)
        run(Driver.compileModulesWithin(EAL.defaultVariableBudget(), Driver.SizingOption.MainSizing{}, mods, Load.base.name(Load.file.of(p))), input(i))
    case Nil{}:
      IO.die(Unit, 2, "usage: telomare-sized-batch FILE.tel < INPUT")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
