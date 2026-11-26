import Base
import ./Text.bend as Tx
import ./Load.bend as Load
import ./HsPrelude.bend as HsPrelude
import ./Telomare_IR_Loc.bend as Loc
import ./Telomare_IR_Base.bend as IB
import ./Telomare_IR_Core.bend as Core
import ./Telomare_IR_Surface.bend as Surface
import ./Telomare_Parse.bend as Parse
import ./Telomare_Expand.bend as Expand
import ./Telomare_Error.bend as Error
import ./Telomare_Resolve.bend as Resolve

# a program's Term3 in prefix notation, its locations left out: the front end
# alone (parse, expand, resolve), to set beside the Haskell's

def T3() -> Data:
  HsPrelude.Cofree<(r_ => Core.Term3F<r_>), Loc.LocTag>

def Ex() -> Data:
  Surface.ExpandedModuleItem<HsPrelude.Cofree<(r_ => Surface.UnprocessedParsedTermF<Unit, HsPrelude.Fix<(r_ => Surface.PatternF<Surface.AnnotatedEST, r_>)>, r_>), Loc.LocTag>>

def EMod() -> Data:
  Sigma<&2, &2, List<&2, Char>, (_ => List<&2, Ex()>)>

def num(n: HsPrelude.HsInt, acc: List<&2, Char>) -> List<&2, Char>:
  List.append(&2, Char, HsPrelude.HsInt.show(n), ' ' <> acc)

def fi(f: IB.FunctionIndex, acc: List<&2, Char>) -> List<&2, Char>:
  match f:
    case IB.FunctionIndex.FunctionIndex{n}:
      num(n, acc)

def ut(f: IB.UnsizedRecursionToken, acc: List<&2, Char>) -> List<&2, Char>:
  match f:
    case IB.UnsizedRecursionToken.UnsizedRecursionToken{n}:
      num(n, acc)

def dump(x: T3(), acc: List<&2, Char>) -> List<&2, Char>:
  match x:
    case HsPrelude.Cofree.Cofree{_, t}:
      match t:
        case Core.Term3F.Term3B{IB.BasicExprF.ZeroSF{}}:
          'Z' <> acc
        case Core.Term3F.Term3B{IB.BasicExprF.PairSF{a, b}}:
          'P' <> dump(a, dump(b, acc))
        case Core.Term3F.Term3S{IB.StuckF.EnvSF{}}:
          'E' <> acc
        case Core.Term3F.Term3S{IB.StuckF.SetEnvSF{a}}:
          'S' <> dump(a, acc)
        case Core.Term3F.Term3S{IB.StuckF.DeferSF{f, a}}:
          'D' <> fi(f, dump(a, acc))
        case Core.Term3F.Term3S{IB.StuckF.GateSF{}}:
          'G' <> acc
        case Core.Term3F.Term3S{IB.StuckF.LeftSF{a}}:
          'L' <> dump(a, acc)
        case Core.Term3F.Term3S{IB.StuckF.RightSF{a}}:
          'R' <> dump(a, acc)
        case Core.Term3F.Term3A{IB.AbortableF.AbortF{_, a}}:
          'A' <> dump(a, acc)
        case Core.Term3F.Term3Unsized{u}:
          'U' <> ut(u, acc)
        case Core.Term3F.Term3CheckingWrapper{_, a, b}:
          'C' <> dump(a, dump(b, acc))

def said(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, Error.ResolverError, T3()>>) -> IO(Unit):
  match e:
    case Inl{m}:
      IO.die(Unit, 1, String.from_list(m))
    case Inr{Inl{m}}:
      IO.die(Unit, 1, "does not resolve")
    case Inr{Inr{t}}:
      IO.print(String.from_list(dump(t, [])))

def grown(n: List<&2, Char>, e: Either<&2, &2, List<&2, Char>, Either<&2, &2, Expand.ExpansionError, List<&2, Ex()>>>) -> EMod():
  match e:
    case Inr{Inr{xs}}:
      (n, xs)
    case _:
      (n, [])

def item(n: List<&2, Char>, e: Either<&2, &2, List<&2, Char>, List<&2, Load.Item()>>) -> EMod():
  match e:
    case Inl{_}:
      (n, [])
    case Inr{xs}:
      grown(n, Expand.expandModule(xs))

def one(m: Load.Mod()) -> EMod():
  (+n, c) = m
  item(n, Parse.runParseModule(n, c))

def all(ms: List<&2, Load.Mod()>) -> List<&2, EMod()>:
  match ms:
    case Nil{}:
      []
    case m <> t:
      one(m) <> all(t)

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      +p = Load.split(String.to_list(f))
      do IO<Unit>:
        +mods : List<&2, Load.Mod()> <- Load.modules(p)
        said(Resolve.main2Term3(all(mods), Load.base.name(Load.file.of(p))))
    case Nil{}:
      IO.die(Unit, 2, "usage: front FILE.tel")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
