# adj/gen/Gen.bend: programs of the model's fragment (Core.bend's Ex, with
# variables), typed and random from a seed, printed as Haskell, so the
# model can be tried against GHC and against cata itself.
#   gen hs NAME FROM COUNT   the Haskell module NAME, defs dFROM ...
#   gen chk NAME FROM COUNT  a Haskell program that runs them on inputs and
#                            compares GHC's answers with the model's (ev.def:
#                            what eval.h (cc.def t) answers, PROPOSED.bend's
#                            cc.def.ok, and F's Bend, cc.F)
#   gen ex NAME FROM COUNT   the programs as Core.bend's Ex
# Run by adj/gen/run.zsh.

import Base
import ../Core.bend as C

# types -------------------------------------------------------------------------

type Ty is Data:
  TN{}
  TB{}
  TU{}
  TP{a: Ty, b: Ty}
  TS{a: Ty, b: Ty}
  TL{a: Ty}

def ty.eq(a: Ty, b: Ty) -> Bool:
  match a b:
    case TN{} TN{}:
      True{}
    case TB{} TB{}:
      True{}
    case TU{} TU{}:
      True{}
    case TP{x, y} TP{u, v}:
      Bool.and(ty.eq(x, u), ty.eq(y, v))
    case TS{x, y} TS{u, v}:
      Bool.and(ty.eq(x, u), ty.eq(y, v))
    case TL{x} TL{u}:
      ty.eq(x, u)
    case _ _:
      False{}

def cat(xs: List<&2, String>) -> String:
  String.concat(xs)

def ty.show(t: Ty) -> String:
  match t:
    case TN{}:
      "Natural"
    case TB{}:
      "Bool"
    case TU{}:
      "()"
    case TP{a, b}:
      cat(["(", ty.show(a), ", ", ty.show(b), ")"])
    case TS{a, b}:
      cat(["(Either ", ty.show(a), " ", ty.show(b), ")"])
    case TL{a}:
      cat(["[", ty.show(a), "]"])

# an expression with the types the Haskell needs written (a let's, a
# scrutinee's, a fold's list's, a projection's pair's, an error's): GHC
# would not tell some of them; er erases them
type Gx is Data:
  GVar{i: Nat}
  GLit{n: Nat}
  GUnit{}
  GPair{a: Gx, b: Gx}
  GFst{ty: Ty, a: Gx}
  GSnd{ty: Ty, a: Gx}
  GInl{a: Gx}
  GInr{a: Gx}
  GNil{}
  GCons{a: Gx, b: Gx}
  GPrim{p: C.Prim, a: Gx, b: Gx}
  GIf{c: Gx, t: Gx, e: Gx}
  GLet{ty: Ty, a: Gx, b: Gx}
  GCase{ty: Ty, a: Gx, l: Gx, r: Gx}
  GFold{ty: Ty, a: Gx, z: Gx, s: Gx}
  GErr{ty: Ty}

def er(t: Gx) -> C.Ex:
  match t:
    case GVar{i}:
      C.EVar{i}
    case GLit{n}:
      C.ELit{n}
    case GUnit{}:
      C.EUnit{}
    case GPair{a, b}:
      C.EPair{er(a), er(b)}
    case GFst{ty, a}:
      C.EFst{er(a)}
    case GSnd{ty, a}:
      C.ESnd{er(a)}
    case GInl{a}:
      C.EInl{er(a)}
    case GInr{a}:
      C.EInr{er(a)}
    case GNil{}:
      C.ENil{}
    case GCons{a, b}:
      C.ECons{er(a), er(b)}
    case GPrim{p, a, b}:
      C.EPrim{p, er(a), er(b)}
    case GIf{c, a, e}:
      C.EIf{er(c), er(a), er(e)}
    case GLet{ty, a, b}:
      C.ELet{er(a), er(b)}
    case GCase{ty, a, l, r}:
      C.ELet{er(a), C.ECase{er(l), er(r)}}
    case GFold{ty, a, z, s}:
      C.ELet{er(a), C.EFold{er(z), er(s)}}
    case GErr{ty}:
      C.EErr{}

# random numbers: a seed's children, and a number below n from it -----------------

def rn(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def kid(s: U32, k: U32) -> U32:
  rn(U32.xor(rn(s), U32.mul(k, 2654435761)))

def pick(s: U32, n: U32) -> Nat:
  U32.to_nat(U32.mod(U32.shrn(rn(rn(s)), 13n), n))

# random types --------------------------------------------------------------------

def rty.at(k: Nat, t0: Ty, t1: Ty) -> Ty:
  match k:
    case 0n:
      TN{}
    case 1n:
      TB{}
    case 2n:
      TP{t0, t1}
    case 3n:
      TS{t0, t1}
    case 4n:
      TL{t0}
    case 5n:
      TL{t1}
    case 6n:
      TU{}
    case _:
      TN{}

def rty.base(k: Nat) -> Ty:
  match k:
    case 0n:
      TB{}
    case _:
      TN{}

def rty(fuel: Nat, +s: U32) -> Ty:
  match fuel:
    case 0n:
      rty.base(pick(s, 3))
    case 1n+f:
      +g = f
      rty.at(pick(s, 9), rty(g, kid(s, 1)), rty(g, kid(s, 2)))

# leaves: a variable of the type, or a constant ----------------------------------------

def vars.at(c: Bool, i: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      i <> r
    case False{}:
      r

# the variables of the type ty, i the innermost's number
def vars(ctx: List<&2, Ty>, +ty: Ty, +i: Nat) -> List<&2, Nat>:
  match ctx:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      vars.at(ty.eq(a, ty), i, vars(r, ty, 1n+i))

# the sums (and the lists) among the variables' types
def sums(ctx: List<&2, Ty>) -> List<&2, Ty>:
  match ctx:
    case Nil{}:
      Nil{}
    case Con{TS{a, b}, r}:
      TS{a, b} <> sums(r)
    case Con{_, r}:
      sums(r)

def lists(ctx: List<&2, Ty>) -> List<&2, Ty>:
  match ctx:
    case Nil{}:
      Nil{}
    case Con{TL{a}, r}:
      TL{a} <> lists(r)
    case Con{_, r}:
      lists(r)

def prim.of(k: Nat) -> C.Prim:
  match k:
    case 0n:
      C.PSub{}
    case 1n:
      C.PDiv{}
    case 2n:
      C.PMod{}
    case _:
      C.PAdd{}

def or.ty(m: Maybe<&2, Ty>, d: Ty) -> Ty:
  match m:
    case Some{t}:
      t
    case None{}:
      d

# one of them, or d
def one(+ts: List<&2, Ty>, s: U32, d: Ty) -> Ty:
  or.ty(List.get(&2, Ty, ts, Nat.mod(pick(s, 97), List.length(&2, Ty, ts))), d)

def const.sum(k: Nat, a: Gx, b: Gx) -> Gx:
  match k:
    case 0n:
      GInl{a}
    case _:
      GInr{b}

# an error now and then, else d
def leaf.err(k: Nat, ty: Ty, d: Gx) -> Gx:
  match k:
    case 0n:
      GErr{ty}
    case _:
      d

# a constant
def const(ty: Ty, +s: U32) -> Gx:
  match ty:
    case TN{}:
      GLit{pick(s, 4)}
    case TB{}:
      GPrim{C.PLt{}, GLit{pick(s, 2)}, GLit{1n}}
    case TU{}:
      GUnit{}
    case TP{a, b}:
      GPair{const(a, kid(s, 1)), const(b, kid(s, 2))}
    case TS{a, b}:
      const.sum(pick(s, 2), const(a, kid(s, 1)), const(b, kid(s, 2)))
    case TL{a}:
      GNil{}

def leaf.at(m: Maybe<&2, Nat>, d: Gx) -> Gx:
  match m:
    case Some{i}:
      GVar{i}
    case None{}:
      d

def leaf.of(+vs: List<&2, Nat>, +s: U32, +ty: Ty) -> Gx:
  leaf.at(List.get(&2, Nat, vs, Nat.mod(pick(kid(s, 5), 97), List.length(&2, Nat, vs))), leaf.err(pick(kid(s, 6), 30), ty, const(ty, s)))

def leaf(+ctx: List<&2, Ty>, +s: U32, +ty: Ty) -> Gx:
  leaf.of(vars(ctx, ty, 0n), s, ty)

# an expression's shape, with the types it needs, chosen from the seed ------------------

type Sh is Data:
  ShIf{}
  ShLet{a: Ty}
  ShCase{a: Ty, b: Ty}
  ShFold{a: Ty}
  ShFst{b: Ty}
  ShSnd{a: Ty}
  ShLeaf{}
  ShIntro{c: Nat}

def sh.case(t: Ty) -> Sh:
  match t:
    case TS{a, b}:
      ShCase{a, b}
    case _:
      ShLeaf{}

def sh.fold(t: Ty) -> Sh:
  match t:
    case TL{a}:
      ShFold{a}
    case _:
      ShLeaf{}

def sh.intro(k: Nat) -> Sh:
  ShIntro{Nat.mod(k, 2n)}

def shape.at(k: Nat, +s: U32, +ctx: List<&2, Ty>) -> Sh:
  match k:
    case 0n:
      ShIf{}
    case 1n+k1:
      match k1:
        case 0n:
          ShLet{rty(2n, kid(s, 4))}
        case 1n+k2:
          match k2:
            case 0n:
              sh.case(one(sums(ctx), kid(s, 4), TS{rty(1n, kid(s, 5)), rty(1n, kid(s, 6))}))
            case 1n+k3:
              match k3:
                case 0n:
                  sh.case(one(sums(ctx), kid(s, 4), TS{rty(1n, kid(s, 5)), rty(1n, kid(s, 6))}))
                case 1n+k4:
                  match k4:
                    case 0n:
                      sh.fold(one(lists(ctx), kid(s, 4), TL{rty(1n, kid(s, 5))}))
                    case 1n+k5:
                      match k5:
                        case 0n:
                          sh.fold(one(lists(ctx), kid(s, 4), TL{rty(1n, kid(s, 5))}))
                        case 1n+k6:
                          match k6:
                            case 0n:
                              sh.fold(one(lists(ctx), kid(s, 4), TL{rty(1n, kid(s, 5))}))
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  ShFst{rty(1n, kid(s, 4))}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      ShSnd{rty(1n, kid(s, 4))}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          ShLeaf{}
                                        case 1n+k10:
                                          sh.intro(k10)

def shape(+s: U32, +ctx: List<&2, Ty>) -> Sh:
  shape.at(pick(kid(s, 7), 15), s, ctx)

def sum.at(c: Nat, a: Gx, b: Gx) -> Gx:
  match c:
    case 0n:
      GInl{a}
    case _:
      GInr{b}

# an expression of type ty, its variables' types ctx (innermost first)
def gen(+fuel: Nat, sh: Sh, +s: U32, +ctx: List<&2, Ty>, +ty: Ty) -> Gx:
  match fuel:
    case 0n:
      leaf(ctx, s, ty)
    case 1n+g:
      match sh:
        case ShIf{}:
          GIf{gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TB{}), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, ty), gen(g, shape(kid(s, 3), ctx), kid(s, 3), ctx, ty)}
        case ShLet{+a}:
          GLet{a, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, a), gen(g, shape(kid(s, 2), a <> ctx), kid(s, 2), a <> ctx, ty)}
        case ShCase{+a, +b}:
          GCase{TS{a, b}, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TS{a, b}), gen(g, shape(kid(s, 2), a <> ctx), kid(s, 2), a <> ctx, ty), gen(g, shape(kid(s, 3), b <> ctx), kid(s, 3), b <> ctx, ty)}
        case ShFold{+a}:
          GFold{TL{a}, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TL{a}), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, ty), gen(g, shape(kid(s, 3), ty <> a <> ctx), kid(s, 3), ty <> a <> ctx, ty)}
        case ShFst{+b}:
          GFst{TP{ty, b}, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TP{ty, b})}
        case ShSnd{+a}:
          GSnd{TP{a, ty}, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TP{a, ty})}
        case ShLeaf{}:
          leaf(ctx, s, ty)
        case ShIntro{c}:
          match ty:
            case TN{}:
              GPrim{prim.of(pick(kid(s, 8), 8)), gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TN{}), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, TN{})}
            case TB{}:
              GPrim{C.PLt{}, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, TN{}), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, TN{})}
            case TU{}:
              GUnit{}
            case TP{+a, +b}:
              GPair{gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, a), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, b)}
            case TS{+a, +b}:
              sum.at(c, gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, a), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, b))
            case TL{+a}:
              GCons{gen(g, shape(kid(s, 1), ctx), kid(s, 1), ctx, a), gen(g, shape(kid(s, 2), ctx), kid(s, 2), ctx, TL{a})}

# Haskell ---------------------------------------------------------------------------------

def name(d: Nat) -> String:
  cat(["v", Nat.show(d)])

def prim.hs(p: C.Prim) -> String:
  match p:
    case C.PAdd{}:
      "+"
    case C.PLt{}:
      "<"
    case C.PSub{}:
      "-"
    case C.PDiv{}:
      "`div`"
    case C.PMod{}:
      "`mod`"
    case _:
      "?"

def or.str(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "?"

# an expression, its variables' names (innermost first), d the next name's number
def hs(t: Gx, +ns: List<&2, String>, +d: Nat) -> String:
  match t:
    case GVar{i}:
      or.str(List.get(&2, String, ns, i))
    case GLit{n}:
      cat(["(", Nat.show(n), " :: Natural)"])
    case GUnit{}:
      "()"
    case GPair{a, b}:
      cat(["(", hs(a, ns, d), ", ", hs(b, ns, d), ")"])
    case GFst{ty, a}:
      cat(["(fst (", hs(a, ns, d), " :: ", ty.show(ty), "))"])
    case GSnd{ty, a}:
      cat(["(snd (", hs(a, ns, d), " :: ", ty.show(ty), "))"])
    case GInl{a}:
      cat(["(Left ", hs(a, ns, d), ")"])
    case GInr{a}:
      cat(["(Right ", hs(a, ns, d), ")"])
    case GNil{}:
      "[]"
    case GCons{a, b}:
      cat(["(", hs(a, ns, d), " : ", hs(b, ns, d), ")"])
    case GPrim{p, a, b}:
      cat(["(", hs(a, ns, d), " ", prim.hs(p), " ", hs(b, ns, d), ")"])
    case GIf{c, a, e}:
      cat(["(if ", hs(c, ns, d), " then ", hs(a, ns, d), " else ", hs(e, ns, d), ")"])
    case GCase{ty, a, l, r}:
      cat(["(case (", hs(a, ns, d), " :: ", ty.show(ty), ") of { Left ", name(d), " -> ", hs(l, name(d) <> ns, 1n+d), "; Right ", name(d), " -> ", hs(r, name(d) <> ns, 1n+d), " })"])
    case GFold{ty, a, z, s}:
      cat(["(foldr (\\", name(d), " ", name(1n+d), " -> ", hs(s, name(1n+d) <> name(d) <> ns, 2n+d), ") ", hs(z, ns, d), " (", hs(a, ns, d), " :: ", ty.show(ty), "))"])
    case GLet{ty, a, b}:
      cat(["(let { ", name(d), " :: ", ty.show(ty), "; ", name(d), " = ", hs(a, ns, d), " } in ", hs(b, name(d) <> ns, 1n+d), ")"])
    case GErr{ty}:
      cat(["(error \"E\" :: ", ty.show(ty), ")"])

def hv(x: C.HV) -> String:
  match x:
    case C.HvNat{n}:
      Nat.show(n)
    case C.HvBool{b}:
      match b:
        case True{}:
          "True"
        case False{}:
          "False"
    case C.HvUnit{}:
      "()"
    case C.HvPair{a, b}:
      cat(["(", hv(a), ", ", hv(b), ")"])
    case C.HvInl{a}:
      cat(["(Left ", hv(a), ")"])
    case C.HvInr{a}:
      cat(["(Right ", hv(a), ")"])
    case C.HvNil{}:
      "[]"
    case C.HvCons{h, t}:
      cat(["(", hv(h), " : ", hv(t), ")"])

# random values of a type
def val.sum(k: Nat, a: C.HV, b: C.HV) -> C.HV:
  match k:
    case 0n:
      C.HvInl{a}
    case _:
      C.HvInr{b}

def val.bool(k: Nat) -> C.HV:
  match k:
    case 0n:
      C.HvBool{False{}}
    case _:
      C.HvBool{True{}}

def val.list(k: Nat, a: C.HV, b: C.HV, c: C.HV) -> C.HV:
  match k:
    case 0n:
      C.HvNil{}
    case 1n+k1:
      match k1:
        case 0n:
          C.HvCons{a, C.HvNil{}}
        case 1n+k2:
          match k2:
            case 0n:
              C.HvCons{a, C.HvCons{b, C.HvNil{}}}
            case 1n+k3:
              C.HvCons{a, C.HvCons{b, C.HvCons{c, C.HvNil{}}}}

def val(ty: Ty, +s: U32) -> C.HV:
  match ty:
    case TN{}:
      C.HvNat{pick(s, 5)}
    case TB{}:
      val.bool(pick(s, 2))
    case TU{}:
      C.HvUnit{}
    case TP{a, b}:
      C.HvPair{val(a, kid(s, 1)), val(b, kid(s, 2))}
    case TS{a, b}:
      val.sum(pick(s, 2), val(a, kid(s, 1)), val(b, kid(s, 2)))
    case TL{+a}:
      val.list(pick(s, 4), val(a, kid(s, 1)), val(a, kid(s, 2)), val(a, kid(s, 3)))

# a def: its argument's type (a pair's parts are the variables), its answer's, its body ----

type Df is Data:
  Df{a: Ty, b: Ty, t: Gx}

# \v0 -> let v1 = fst v0 in let v2 = snd v0 in ...
def df.body(+x: Ty, +y: Ty, t: Gx) -> Gx:
  GLet{x, GFst{TP{x, y}, GVar{0n}}, GLet{y, GSnd{TP{x, y}, GVar{1n}}, t}}

def df.at(+s: U32, +x: Ty, +y: Ty, +b: Ty, +ctx: List<&2, Ty>) -> Df:
  Df{TP{x, y}, b, df.body(x, y, gen(4n, shape(kid(s, 3), ctx), kid(s, 3), ctx, b))}

def df(+i: Nat) -> Df:
  +s = kid(20261124, U32.from_nat(i))
  +x = rty(2n, kid(s, 1))
  +y = rty(2n, kid(s, 2))
  df.at(s, x, y, rty(2n, kid(s, 4)), [y, x, TP{x, y}])

def df.hs(d: Df, +i: Nat) -> String:
  match d:
    case Df{a, b, t}:
      cat(["d", Nat.show(i), " :: ", ty.show(a), " -> ", ty.show(b), "\nd", Nat.show(i), " v0 = ", hs(t, ["v0"], 1n), "\n\n"])

def ans(m: Maybe<&2, C.HV>) -> String:
  match m:
    case Some{v}:
      cat(["(Just ", hv(v), ")"])
    case None{}:
      "Nothing"

def row(n: Nat, +i: Nat, +a: Ty, +t: C.Ex, +s: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      +j = m
      +x = val(a, kid(s, U32.from_nat(j)))
      cat(["  r \"d", Nat.show(i), "\" ", ans(C.ev.def(t, x)), " (d", Nat.show(i), " ", hv(x), ")\n", row(j, i, a, t, s)])

def df.chk(d: Df, +i: Nat) -> String:
  match d:
    case Df{+a, b, +t}:
      row(8n, i, a, er(t), kid(977, U32.from_nat(i)))

def defs(n: Nat, +i: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      cat([df.hs(df(i), i), defs(m, 1n+i)])

def rows(n: Nat, +i: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      cat([df.chk(df(i), i), rows(m, 1n+i)])

def out.hs(+nm: String, +i: Nat, +n: Nat) -> String:
  cat(["module ", nm, " where\n\nimport Numeric.Natural (Natural)\n\n", defs(n, i)])

def out.chk(+nm: String, +i: Nat, +n: Nat) -> String:
  cat(["module Main (main) where\n\nimport FragRt (r, done)\nimport ", nm, "\n\nmain :: IO ()\nmain = do\n", rows(n, i), "  done\n"])

def or.nat(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      0n

def out(chk: Bool, +nm: String, +i: Nat, +n: Nat) -> String:
  match chk:
    case True{}:
      out.chk(nm, i, n)
    case False{}:
      out.hs(nm, i, n)

def run(args: List<String>) -> IO(Unit):
  match args:
    case m <> nm <> i <> n <> r:
      IO.write(out(String.eq(m, "chk"), nm, or.nat(Nat.read(i)), or.nat(Nat.read(n))))
    case _:
      IO.print("usage: gen (hs | chk) NAME FROM COUNT")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    run(List.tail(&1, String, argv))
