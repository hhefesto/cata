import Base
import ./Text.bend as Tx
import ./Load.bend as Load
import ./HsPrelude.bend as HsPrelude
import ./Telomare_IR_Base.bend as IRB
import ./Telomare_IR_Core.bend as Core
import ./Telomare_EAL.bend as EAL
import ./Telomare_Driver.bend as Driver

# telomare FILE (its usual, sized route), played at the terminal: an
# iteration is evalLoopCore's wrappedEval, cata's; its input and output are
# Bend's.

def Cx() -> Data:
  HsPrelude.Fix<(r_ => Core.CompiledExprF<r_>)>

def Bx() -> Data:
  HsPrelude.Fix<(r_ => IRB.BasicExprF<r_>)>

def Inp() -> Data:
  Maybe<&2, Sigma<&2, &2, List<&2, Char>, (_ => Bx())>>

def Res() -> Data:
  Sigma<&2, &2, Unit, (_ => Sigma<&2, &2, List<&2, Char>, (_ => Either<&2, &2, Core.RunTimeError, Bx()>)>)>

type Got is Data:
  GErr{+m: List<&2, Char>}
  GEnd{+out: List<&2, Char>}
  GMore{+out: List<&2, Char>, +s: Bx()}

def got.st(out: List<&2, Char>, e: Either<&2, &2, Core.RunTimeError, Bx()>) -> Got:
  match e:
    case Inl{_}:
      GEnd{out}
    case Inr{HsPrelude.Fix.Fix{IRB.BasicExprF.ZeroSF{}}}:
      GEnd{out}
    case Inr{ns}:
      GMore{out, ns}

def got(r: Either<&2, &2, List<&2, Char>, Res()>) -> Got:
  match r:
    case Inl{e}:
      GErr{e}
    case Inr{Tuple{_, Tuple{out, e}}}:
      got.st(out, e)

def iteration(it: Driver.Iteration, inp: Inp()) -> Either<&2, &2, List<&2, Char>, Res()>:
  match it:
    case Driver.Iteration.Iteration{prologue, expr}:
      Driver.evalLoopCore__Unit.wrappedEval.pt0(~x => Driver.plainEval(x), prologue, expr, inp)

type Lp is Type:
  Run{inp: Inp(), i: Tx.In}
  Show{g: Got, i: Tx.In}
  Next{s: Bx(), l: Tx.Line}

def loop(fuel: Nat, +it: Driver.Iteration, st: Lp) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      match st:
        case Run{inp, i}:
          loop(k, it, Show{got(iteration(it, inp)), i})
        case Show{g, i}:
          match g:
            case GErr{m}:
              IO.die(Unit, 1, String.from_list(m))
            case GEnd{out}:
              IO.print(String.from_list(out))
            case GMore{out, s}:
              do IO<Unit>:
                IO.print(String.from_list(out))
                l : Tx.Line <- Tx.read_line(i)
                loop(k, it, Next{s, l})
        case Next{s, Tx.Line{i, got}}:
          match got:
            case Tx.GLine{text}:
              loop(k, it, Run{Some{Tuple{String.to_list(text), s}}, i})
            case Tx.GEnd{}:
              IO.die(Unit, 1, "Prelude.getLine: end of file")
            case Tx.GErr{m}:
              IO.die(Unit, 1, m)

def run(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, List<&2, Char>, Driver.CompiledProgram>>) -> IO(Unit):
  match e:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inl{m}}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inr{cp}}:
      loop(U32.to_nat(4294967295), Driver.programIteration(cp), Run{None{}, Tx.Closed{}})

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      +p = Load.split(String.to_list(f))
      do IO<Unit>:
        +mods : List<&2, Load.Mod()> <- Load.modules(p)
        run(Driver.compileModulesWithin(EAL.defaultVariableBudget(), Driver.SizingOption.MainSizing{}, mods, Load.base.name(Load.file.of(p))))
    case Nil{}:
      IO.die(Unit, 2, "usage: telomare-sized FILE.tel")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
