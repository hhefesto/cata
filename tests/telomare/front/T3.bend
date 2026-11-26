import Base
import ./Text.bend as Tx
import ./HsPrelude.bend as HsPrelude
import ./Telomare_IR_Loc.bend as Loc
import ./Telomare_IR_Base.bend as IB
import ./Telomare_IR_Core.bend as Core
import ./Telomare_EAL.bend as EAL
import ./Telomare_Error.bend as Telomare_Error

def T3() -> Data:
  HsPrelude.Cofree<(r_ => Core.Term3F<r_>), Loc.LocTag>

def mk(l: Core.Term3F<T3()>) -> T3():
  HsPrelude.Cofree.Cofree{Loc.LocTag.UnknownLoc{}, l}

def org() -> IB.AbortOrigin:
  IB.AbortOrigin.AbortOrigin{IB.AbortKind.UserAbort{}, Loc.LocTag.UnknownLoc{}}

type Sk is Data:
  Sk{+st: List<&2, T3()>, +n: Nat, +p: Nat}

def one(+c: U32, +a: T3(), +t: List<&2, T3()>, +n: Nat) -> List<&2, T3()>:
  match c:
    case 83:
      mk(Core.Term3F.Term3S{IB.StuckF.SetEnvSF{a}}) <> t
    case 76:
      mk(Core.Term3F.Term3S{IB.StuckF.LeftSF{a}}) <> t
    case 82:
      mk(Core.Term3F.Term3S{IB.StuckF.RightSF{a}}) <> t
    case 65:
      mk(Core.Term3F.Term3A{IB.AbortableF.AbortF{org(), a}}) <> t
    case 68:
      mk(Core.Term3F.Term3S{IB.StuckF.DeferSF{IB.FunctionIndex.FunctionIndex{HsPrelude.HsInt.Pos{n}}, a}}) <> t
    case _:
      a <> t

def two(+c: U32, +a: T3(), +b: T3(), +t: List<&2, T3()>) -> List<&2, T3()>:
  match c:
    case 80:
      mk(Core.Term3F.Term3B{IB.BasicExprF.PairSF{a, b}}) <> t
    case 67:
      mk(Core.Term3F.Term3CheckingWrapper{org(), a, b}) <> t
    case _:
      a <> b <> t

def isz(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 80), U32.is_eq(c, 67))

def pop(+c: U32, two0: Bool, +n: Nat, st: List<&2, T3()>) -> List<&2, T3()>:
  match two0 st:
    case True{} a <> b <> t:
      two(c, a, b, t)
    case False{} a <> t:
      one(c, a, t, n)
    case _ s:
      s

def push(+c: U32, +n: Nat, +st: List<&2, T3()>) -> List<&2, T3()>:
  match c:
    case 90:
      mk(Core.Term3F.Term3B{IB.BasicExprF.ZeroSF{}}) <> st
    case 69:
      mk(Core.Term3F.Term3S{IB.StuckF.EnvSF{}}) <> st
    case 71:
      mk(Core.Term3F.Term3S{IB.StuckF.GateSF{}}) <> st
    case 85:
      mk(Core.Term3F.Term3Unsized{IB.UnsizedRecursionToken.UnsizedRecursionToken{HsPrelude.HsInt.Pos{n}}}) <> st
    case _:
      pop(c, isz(c), n, st)

def dig(d: Bool, sp: Bool, +c: U32, s: Sk) -> Sk:
  match d sp s:
    case True{} _ Sk{st, n, +p}:
      Sk{st, Nat.add(n, Nat.mul(p, U32.to_nat(U32.sub(c, 48)))), Nat.mul(p, 10n)}
    case False{} True{} Sk{st, n, p}:
      Sk{st, 0n, 1n}
    case False{} False{} Sk{st, n, p}:
      Sk{push(c, n, st), 0n, 1n}

def rd(xs: List<&2, U32>, s: Sk) -> Sk:
  match xs:
    case Nil{}:
      s
    case +c <> t:
      rd(t, dig(Bool.and(U32.is_le(48, c), U32.is_le(c, 57)), U32.is_le(c, 32), c, s))

def top(s: Sk) -> Maybe<&2, T3()>:
  match s:
    case Sk{a <> Nil{}, n, p}:
      Some{a}
    case _:
      None{}

def said(e: Either<&2, &2, List<&2, Char>, Either<&2, &2, Telomare_Error.EALError, EAL.EALResult>>) -> String:
  match e:
    case Inl{m}:
      String.append("error: ", String.from_list(m))
    case Inr{Inl{m}}:
      "refused"
    case Inr{Inr{r}}:
      "certified"

def cert(m: Maybe<&2, T3()>) -> IO(Unit):
  match m:
    case None{}:
      IO.die(Unit, 1, "not a term")
    case Some{t}:
      IO.print(said(EAL.certifyMainWithin(EAL.defaultVariableBudget(), t)))

def text(r: Result<&1, &1, String, List<&2, U32>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, e)
    case Done{bs}:
      cert(top(rd(List.reverse(&2, U32, bs), Sk{[], 0n, 1n})))

def go(args: List<String>) -> IO(Unit):
  match args:
    case f <> t:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, U32>> <- Tx.Bytes.read(f)
        text(r)
    case Nil{}:
      IO.die(Unit, 2, "usage")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    go(List.drop(&1, String, argv, 1n))
