import Base
import ./Text.bend as Tx
import ./Load.bend as Load
import ./HsPrelude.bend as HsPrelude
import ./Telomare_IR_Core.bend as Core
import ./Telomare_EAL.bend as EAL
import ./Telomare_Fast.bend as Fast

# telomare --fast FILE, its loop's input and output Bend's: app/Main.hs's runFast
# and Fast.hs's runFastLoop; everything they run is cata's.

def Res() -> Data:
  Sigma<&2, &2, List<&2, Char>, (_ => Either<&2, &2, Core.RunTimeError, Fast.Value>)>

def St() -> Data:
  Sigma<&2, &2, Fast.FastMeter, (_ => Maybe<&2, HsPrelude.HsInt>)>

def Inp() -> Data:
  Maybe<&2, Sigma<&2, &2, List<&2, Char>, (_ => Fast.Value)>>

# an iteration of main, as runFastLoop's go runs it
def iteration(prog: Fast.FastExpr, inp: Inp()) -> Sigma<&2, &2, Fast.FastMeter, (_ => Either<&2, &2, Fast.FastError, Res()>)>:
  Fast.runEval__Tuple2_List_Char_Either_RunTimeError_Value(Some{Fast.defaultFastFuel()}, Fast.hs.exs.bind(Fast.FastError, St(), Fast.Value, Res(), Fast.mainClosureOf(prog), c => Fast.iterateMain(c, inp)))

type Got is Data:
  GErr{+m: List<&2, Char>}
  GEnd{+out: List<&2, Char>}
  GMore{+out: List<&2, Char>, +s: Fast.Value}

def got.st(out: List<&2, Char>, e: Either<&2, &2, Core.RunTimeError, Fast.Value>) -> Got:
  match e:
    case Inl{_}:
      GEnd{out}
    case Inr{Fast.Value.VZero{}}:
      GEnd{out}
    case Inr{ns}:
      GMore{out, ns}

def got.res(r: Either<&2, &2, Fast.FastError, Res()>) -> Got:
  match r:
    case Inl{e}:
      GErr{Fast.renderFastError(e)}
    case Inr{Tuple{out, e}}:
      got.st(out, e)

def got(r: Sigma<&2, &2, Fast.FastMeter, (_ => Either<&2, &2, Fast.FastError, Res()>)>) -> Got:
  match r:
    case Tuple{m, e}:
      got.res(e)

type Lp is Type:
  Run{inp: Inp(), i: Tx.In}
  Show{g: Got, i: Tx.In}
  Next{s: Fast.Value, l: Tx.Line}

def loop(fuel: Nat, +prog: Fast.FastExpr, st: Lp) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      match st:
        case Run{inp, i}:
          loop(k, prog, Show{got(iteration(prog, inp)), i})
        case Show{g, i}:
          match g:
            case GErr{m}:
              IO.print(String.from_list(m))
            case GEnd{out}:
              IO.print(String.from_list(out))
            case GMore{out, s}:
              do IO<Unit>:
                IO.print(String.from_list(out))
                l : Tx.Line <- Tx.read_line(i)
                loop(k, prog, Next{s, l})
        case Next{s, Tx.Line{i, got}}:
          match got:
            case Tx.GLine{text}:
              loop(k, prog, Run{Some{Tuple{String.to_list(text), s}}, i})
            case Tx.GEnd{}:
              IO.pure(Unit, Unit{})
            case Tx.GErr{m}:
              IO.die(Unit, 1, m)

def run(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, List<&2, Char>, Fast.FastExpr>>) -> IO(Unit):
  match e:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inl{m}}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inr{prog}}:
      loop(U32.to_nat(4294967295), prog, Run{None{}, Tx.Closed{}})

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      +p = Load.split(String.to_list(f))
      do IO<Unit>:
        +mods : List<&2, Load.Mod()> <- Load.modules(p)
        run(Fast.compileFastWithin(EAL.defaultVariableBudget(), mods, Load.base.name(Load.file.of(p))))
    case Nil{}:
      IO.die(Unit, 2, "usage: telomare-fast FILE.tel")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
