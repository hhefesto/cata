# cata as a functor, its core: the two categories, F (hs2bend) and G
# (bend2hs) on them, as Bend data with their meanings.  PROPOSED.bend states
# the laws (functors, squares, the adjunction), PROOF.bend proves them, and
# `bend PROOF.bend --verdict` rechecks every proof with BendTT's kernel.
#
# The core is cata's fragment as combinators, point-free (the categories'
# own structure, so F's compositionality is its definition): identities,
# composition, pairs, sums, foldr over lists (lists' initial algebra), the
# numbers' arithmetic and tests, and the primitives where the two languages
# differ: Haskell's Natural subtraction, div and mod are partial (an error
# below 0 or at 0), Bend's Nat.sub, Nat.div and Nat.mod are total (0 below
# 0, 0 at 0, a at 0), and a partial Bend def answers a failure value (the
# Inl of its Either).  A program's meaning is a function from values to
# Maybe values, None its error (Haskell) or failure value (Bend).
#
# Programs are ordered by "is implemented by": p <= q when q answers what p
# answers wherever p answers (PROPOSED.bend's Le.h and Le.b).

import Base

# Values ----------------------------------------------------------------------

# Haskell's values of the fragment (first order; strict: the survey keeps
# laziness out)
type HV is Data:
  HvNat{n: Nat}
  HvBool{b: Bool}
  HvUnit{}
  HvPair{a: HV, b: HV}
  HvInl{a: HV}
  HvInr{b: HV}
  HvNil{}
  HvCons{h: HV, t: HV}

# Bend's
type BV is Data:
  BvNat{n: Nat}
  BvBool{b: Bool}
  BvUnit{}
  BvPair{a: BV, b: BV}
  BvInl{a: BV}
  BvInr{b: BV}
  BvNil{}
  BvCons{h: BV, t: BV}

# F on values (and so on the objects' elements): Natural is Nat, a pair a
# pair, Either Either, a list a list
def enc(x: HV) -> BV:
  match x:
    case HvNat{n}:
      BvNat{n}
    case HvBool{b}:
      BvBool{b}
    case HvUnit{}:
      BvUnit{}
    case HvPair{a, b}:
      BvPair{enc(a), enc(b)}
    case HvInl{a}:
      BvInl{enc(a)}
    case HvInr{b}:
      BvInr{enc(b)}
    case HvNil{}:
      BvNil{}
    case HvCons{h, t}:
      BvCons{enc(h), enc(t)}

# G on values
def dec(y: BV) -> HV:
  match y:
    case BvNat{n}:
      HvNat{n}
    case BvBool{b}:
      HvBool{b}
    case BvUnit{}:
      HvUnit{}
    case BvPair{a, b}:
      HvPair{dec(a), dec(b)}
    case BvInl{a}:
      HvInl{dec(a)}
    case BvInr{b}:
      HvInr{dec(b)}
    case BvNil{}:
      HvNil{}
    case BvCons{h, t}:
      HvCons{dec(h), dec(t)}

# an answer's value through enc, an error a failure value
def encM(r: Maybe<&2, HV>) -> Maybe<&2, BV>:
  match r:
    case None{}:
      None{}
    case Some{v}:
      Some{enc(v)}

def decM(r: Maybe<&2, BV>) -> Maybe<&2, HV>:
  match r:
    case None{}:
      None{}
    case Some{v}:
      Some{dec(v)}

# Haskell's programs ------------------------------------------------------------

type HTm is Data:
  HId{}
  HComp{g: HTm, f: HTm}
  HFst{}
  HSnd{}
  HPr{f: HTm, g: HTm}
  HInl{}
  HInr{}
  HCase{f: HTm, g: HTm}
  HLit{n: Nat}
  HPrim{p: Prim}
  HIf{c: HTm, t: HTm, e: HTm}
  HFold{z: HTm, s: HTm}
  HErr{}

# A pair of numbers, the primitives' argument (anything else: NNo, an error)
type NN is Data:
  NN{a: Nat, b: Nat}
  NNo{}

def h.nn(x: HV) -> NN:
  match x:
    case HvPair{HvNat{a}, HvNat{b}}:
      NN{a, b}
    case _:
      NNo{}

# The primitives at a pair of numbers, in both languages: the arithmetic
# both have, Haskell's partial (-), div and mod, and Bend's total Nat.sub,
# Nat.div and Nat.mod (0 below 0, 0 at 0, a at 0).  Each is a meaning on
# NN, so a primitive's square is one law on NN (PROOF.bend).  A program of
# one language may call the other's kind of primitive: Haskell's BendRt
# wrappers (b'Nat'sub, b'Nat'div, b'Nat'mod: prelude/Back/BendRt.hs) are
# Bend's total ones written in Haskell, and a partial Bend def (cata's
# prelude) is Haskell's partial one written in Bend, answering a failure.
type Prim is Data:
  PAdd{}
  PLt{}
  PSub{}
  PDiv{}
  PMod{}
  PSubT{}
  PDivT{}
  PModT{}

def p.lt.at(lt: Bool, a: Nat, b: Nat) -> Maybe<&2, Nat>:
  match lt:
    case True{}:
      None{}
    case False{}:
      Some{Nat.sub(a, b)}

# a primitive's answer at a pair of numbers: a number, a truth value, or
# None (an error, a failure value)
type PV is Data:
  PvNat{n: Nat}
  PvBool{b: Bool}
  PvNo{}

def p.of(m: Maybe<&2, Nat>) -> PV:
  match m:
    case Some{n}:
      PvNat{n}
    case None{}:
      PvNo{}

def p.at(p: Prim, +a: Nat, +b: Nat) -> PV:
  match p:
    case PAdd{}:
      PvNat{Nat.add(a, b)}
    case PLt{}:
      PvBool{Nat.is_lt(a, b)}
    case PSub{}:
      p.of(p.lt.at(Nat.is_lt(a, b), a, b))
    case PDiv{}:
      match b:
        case 0n:
          PvNo{}
        case 1n+q:
          PvNat{Nat.div(a, 1n+q)}
    case PMod{}:
      match b:
        case 0n:
          PvNo{}
        case 1n+q:
          PvNat{Nat.mod(a, 1n+q)}
    case PSubT{}:
      PvNat{Nat.sub(a, b)}
    case PDivT{}:
      PvNat{Nat.div(a, b)}
    case PModT{}:
      PvNat{Nat.mod(a, b)}

def p.nn(p: Prim, n: NN) -> PV:
  match n:
    case NN{a, b}:
      p.at(p, a, b)
    case NNo{}:
      PvNo{}

def h.pv(v: PV) -> Maybe<&2, HV>:
  match v:
    case PvNat{n}:
      Some{HvNat{n}}
    case PvBool{b}:
      Some{HvBool{b}}
    case PvNo{}:
      None{}

def h.prim(p: Prim, x: HV) -> Maybe<&2, HV>:
  h.pv(p.nn(p, h.nn(x)))

def h.fst(x: HV) -> Maybe<&2, HV>:
  match x:
    case HvPair{a, b}:
      Some{a}
    case _:
      None{}

def h.snd(x: HV) -> Maybe<&2, HV>:
  match x:
    case HvPair{a, b}:
      Some{b}
    case _:
      None{}

def h.pair(a: Maybe<&2, HV>, b: Maybe<&2, HV>) -> Maybe<&2, HV>:
  match a b:
    case Some{u} Some{v}:
      Some{HvPair{u, v}}
    case _ _:
      None{}

def h.if(c: Maybe<&2, HV>, a: Maybe<&2, HV>, e: Maybe<&2, HV>) -> Maybe<&2, HV>:
  match c:
    case Some{HvBool{True{}}}:
      a
    case Some{HvBool{False{}}}:
      e
    case _:
      None{}

# Haskell's meaning: the answer of t at x, None an error
def eval.h(+t: HTm, +x: HV) -> Maybe<&2, HV>:
  match t:
    case HId{}:
      Some{x}
    case HComp{g, f}:
      Maybe.bind(&2, HV, HV, eval.h(f, x), y => eval.h(g, y))
    case HFst{}:
      h.fst(x)
    case HSnd{}:
      h.snd(x)
    case HPr{f, g}:
      h.pair(eval.h(f, x), eval.h(g, x))
    case HInl{}:
      Some{HvInl{x}}
    case HInr{}:
      Some{HvInr{x}}
    case HCase{f, g}:
      match x:
        case HvInl{a}:
          eval.h(f, a)
        case HvInr{b}:
          eval.h(g, b)
        case _:
          None{}
    case HLit{n}:
      Some{HvNat{n}}
    case HPrim{p}:
      h.prim(p, x)
    case HIf{c, a, e}:
      h.if(eval.h(c, x), eval.h(a, x), eval.h(e, x))
    case HFold{z, s}:
      match x:
        case HvNil{}:
          eval.h(z, HvUnit{})
        case HvCons{hd, tl}:
          Maybe.bind(&2, HV, HV, eval.h(t, tl), r => eval.h(s, HvPair{hd, r}))
        case _:
          None{}
    case HErr{}:
      None{}

# Bend's programs ---------------------------------------------------------------

type BTm is Data:
  BId{}
  BComp{g: BTm, f: BTm}
  BFst{}
  BSnd{}
  BPr{f: BTm, g: BTm}
  BInl{}
  BInr{}
  BCase{f: BTm, g: BTm}
  BLit{n: Nat}
  BPrim{p: Prim}
  BIf{c: BTm, t: BTm, e: BTm}
  BFold{z: BTm, s: BTm}
  BFail{}

def b.nn(y: BV) -> NN:
  match y:
    case BvPair{BvNat{a}, BvNat{b}}:
      NN{a, b}
    case _:
      NNo{}

def b.pv(v: PV) -> Maybe<&2, BV>:
  match v:
    case PvNat{n}:
      Some{BvNat{n}}
    case PvBool{b}:
      Some{BvBool{b}}
    case PvNo{}:
      None{}

def b.prim(p: Prim, y: BV) -> Maybe<&2, BV>:
  b.pv(p.nn(p, b.nn(y)))

def b.fst(y: BV) -> Maybe<&2, BV>:
  match y:
    case BvPair{a, b}:
      Some{a}
    case _:
      None{}

def b.snd(y: BV) -> Maybe<&2, BV>:
  match y:
    case BvPair{a, b}:
      Some{b}
    case _:
      None{}

def b.pair(a: Maybe<&2, BV>, b: Maybe<&2, BV>) -> Maybe<&2, BV>:
  match a b:
    case Some{u} Some{v}:
      Some{BvPair{u, v}}
    case _ _:
      None{}

def b.if(c: Maybe<&2, BV>, a: Maybe<&2, BV>, e: Maybe<&2, BV>) -> Maybe<&2, BV>:
  match c:
    case Some{BvBool{True{}}}:
      a
    case Some{BvBool{False{}}}:
      e
    case _:
      None{}

# Bend's meaning: the answer of b at y, None a failure value
def eval.b(+t: BTm, +y: BV) -> Maybe<&2, BV>:
  match t:
    case BId{}:
      Some{y}
    case BComp{g, f}:
      Maybe.bind(&2, BV, BV, eval.b(f, y), z => eval.b(g, z))
    case BFst{}:
      b.fst(y)
    case BSnd{}:
      b.snd(y)
    case BPr{f, g}:
      b.pair(eval.b(f, y), eval.b(g, y))
    case BInl{}:
      Some{BvInl{y}}
    case BInr{}:
      Some{BvInr{y}}
    case BCase{f, g}:
      match y:
        case BvInl{a}:
          eval.b(f, a)
        case BvInr{b}:
          eval.b(g, b)
        case _:
          None{}
    case BLit{n}:
      Some{BvNat{n}}
    case BPrim{p}:
      b.prim(p, y)
    case BIf{c, a, e}:
      b.if(eval.b(c, y), eval.b(a, y), eval.b(e, y))
    case BFold{z, s}:
      match y:
        case BvNil{}:
          eval.b(z, BvUnit{})
        case BvCons{hd, tl}:
          Maybe.bind(&2, BV, BV, eval.b(t, tl), r => eval.b(s, BvPair{hd, r}))
        case _:
          None{}
    case BFail{}:
      None{}

# F and G -------------------------------------------------------------------------

# F (hs2bend), refined: every construct to its own, each primitive to the
# Bend program that means it, so Haskell's partial (-), div and mod to the
# checked defs that answer a failure value where Haskell errs
def F(t: HTm) -> BTm:
  match t:
    case HId{}:
      BId{}
    case HComp{g, f}:
      BComp{F(g), F(f)}
    case HFst{}:
      BFst{}
    case HSnd{}:
      BSnd{}
    case HPr{f, g}:
      BPr{F(f), F(g)}
    case HInl{}:
      BInl{}
    case HInr{}:
      BInr{}
    case HCase{f, g}:
      BCase{F(f), F(g)}
    case HLit{n}:
      BLit{n}
    case HPrim{p}:
      BPrim{p}
    case HIf{c, a, e}:
      BIf{F(c), F(a), F(e)}
    case HFold{z, s}:
      BFold{F(z), F(s)}
    case HErr{}:
      BFail{}

# G (bend2hs): every construct to its own, a failure value to an error
def G(t: BTm) -> HTm:
  match t:
    case BId{}:
      HId{}
    case BComp{g, f}:
      HComp{G(g), G(f)}
    case BFst{}:
      HFst{}
    case BSnd{}:
      HSnd{}
    case BPr{f, g}:
      HPr{G(f), G(g)}
    case BInl{}:
      HInl{}
    case BInr{}:
      HInr{}
    case BCase{f, g}:
      HCase{G(f), G(g)}
    case BLit{n}:
      HLit{n}
    case BPrim{p}:
      HPrim{p}
    case BIf{c, a, e}:
      HIf{G(c), G(a), G(e)}
    case BFold{z, s}:
      HFold{G(z), G(s)}
    case BFail{}:
      HErr{}

# F as cata had it (Fold.bend before 11-23): Haskell's div and mod to
# Base's Nat.div and Nat.mod, total (x `div` 0 is 0, x `mod` 0 is x), so
# F's program answers where Haskell's errs (the "more defined" laws of
# PLAN.md's round trip)
def F.tot.prim(p: Prim) -> Prim:
  match p:
    case PDiv{}:
      PDivT{}
    case PMod{}:
      PModT{}
    case q:
      q

def F.tot(t: HTm) -> BTm:
  match t:
    case HId{}:
      BId{}
    case HComp{g, f}:
      BComp{F.tot(g), F.tot(f)}
    case HFst{}:
      BFst{}
    case HSnd{}:
      BSnd{}
    case HPr{f, g}:
      BPr{F.tot(f), F.tot(g)}
    case HInl{}:
      BInl{}
    case HInr{}:
      BInr{}
    case HCase{f, g}:
      BCase{F.tot(f), F.tot(g)}
    case HLit{n}:
      BLit{n}
    case HPrim{p}:
      BPrim{F.tot.prim(p)}
    case HIf{c, a, e}:
      BIf{F.tot(c), F.tot(a), F.tot(e)}
    case HFold{z, s}:
      BFold{F.tot(z), F.tot(s)}
    case HErr{}:
      BFail{}

# Int and Integer ----------------------------------------------------------------

# F takes Int and Integer to Nat as it takes Natural (Survey.bend: where
# nothing subtracts), so at those types a Haskell value may be one Bend
# has not, a negative number.  ZV is Haskell's values there: HV's, and a
# negative number, ZvNeg{n} = -(n+1), wherever a number goes.
type ZV is Data:
  ZvNat{n: Nat}
  ZvNeg{n: Nat}
  ZvBool{b: Bool}
  ZvUnit{}
  ZvPair{a: ZV, b: ZV}
  ZvInl{a: ZV}
  ZvInr{b: ZV}
  ZvNil{}
  ZvCons{h: ZV, t: ZV}

# Natural's values among Int's (toInteger)
def up(x: HV) -> ZV:
  match x:
    case HvNat{n}:
      ZvNat{n}
    case HvBool{b}:
      ZvBool{b}
    case HvUnit{}:
      ZvUnit{}
    case HvPair{a, b}:
      ZvPair{up(a), up(b)}
    case HvInl{a}:
      ZvInl{up(a)}
    case HvInr{b}:
      ZvInr{up(b)}
    case HvNil{}:
      ZvNil{}
    case HvCons{h, t}:
      ZvCons{up(h), up(t)}

def upM(r: Maybe<&2, HV>) -> Maybe<&2, ZV>:
  match r:
    case None{}:
      None{}
    case Some{v}:
      Some{up(v)}

# whether an Int value is Natural's: no negative number in it
def nonneg(z: ZV) -> Bool:
  match z:
    case ZvNat{n}:
      True{}
    case ZvNeg{n}:
      False{}
    case ZvBool{b}:
      True{}
    case ZvUnit{}:
      True{}
    case ZvPair{a, b}:
      Bool.and(nonneg(a), nonneg(b))
    case ZvInl{a}:
      nonneg(a)
    case ZvInr{b}:
      nonneg(b)
    case ZvNil{}:
      True{}
    case ZvCons{h, t}:
      Bool.and(nonneg(h), nonneg(t))

# an Int value as Natural's (a negative number, never asked for, as 0)
def ofz(z: ZV) -> HV:
  match z:
    case ZvNat{n}:
      HvNat{n}
    case ZvNeg{n}:
      HvNat{0n}
    case ZvBool{b}:
      HvBool{b}
    case ZvUnit{}:
      HvUnit{}
    case ZvPair{a, b}:
      HvPair{ofz(a), ofz(b)}
    case ZvInl{a}:
      HvInl{ofz(a)}
    case ZvInr{b}:
      HvInr{ofz(b)}
    case ZvNil{}:
      HvNil{}
    case ZvCons{h, t}:
      HvCons{ofz(h), ofz(t)}

def down.at(c: Bool, z: ZV) -> Maybe<&2, HV>:
  match c:
    case True{}:
      Some{ofz(z)}
    case False{}:
      None{}

# Int's values to Natural's (fromIntegral): an error, arithmetic
# underflow, at a negative number
def down(+z: ZV) -> Maybe<&2, HV>:
  down.at(nonneg(z), z)

# G's program used at Int: its Haskell is at Natural (Bend's Nat), so its
# argument passes fromIntegral (an error at a negative number) and its
# answer toInteger
def gz(+b: BTm, +z: ZV) -> Maybe<&2, ZV>:
  Maybe.bind(&2, HV, ZV, down(z), x => upM(eval.h(G(b), x)))
