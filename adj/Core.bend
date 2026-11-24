# cata as a functor, its core: the two categories, F (hs2bend) and G
# (bend2hs) on them, as Bend data with their meanings.  PROPOSED.bend states
# the laws (functors, squares, the adjunction), PROOF.bend proves them, and
# `bend PROOF.bend --verdict` rechecks every proof with BendTT's kernel.
#
# The core is cata's fragment as combinators, point-free (the categories'
# own structure, so F's compositionality is its definition): identities,
# composition, pairs, sums, foldr over lists (lists' initial algebra), the
# numbers' arithmetic and tests (at Int, at a range: every integer, or
# Int's 64 bits), general recursion with fuel (near the end: a loop,
# Haskell's until, and cata's fuelled def), and the primitives where the
# two languages differ: Haskell's Natural
# subtraction, div and mod are partial (an error below 0 or at 0), Bend's
# Nat.sub, Nat.div and Nat.mod are total (0 below 0, 0 at 0, a at 0), and
# a partial Bend def answers a failure value (the Inl of its Either).  A
# program's meaning is a function from values to Maybe values, None its
# error (Haskell) or failure value (Bend).
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

# Haskell's meaning at Int --------------------------------------------------------

# h run at Int: its values ZV, negative numbers too, and Int's own
# arithmetic (Integer's here; Int's 64 bits, wrap-around, are a range,
# below and at the end, PROPOSED.bend's section 8).  ZvNat{n} is n,
# ZvNeg{n} is -(n+1).  What F's Nat is right for is then a theorem, not a
# hypothesis: at a Natural value, h at Int means what h at Natural means
# whenever h never subtracts (PROPOSED.bend's agree), and not otherwise
# (agree.sub.not).

# n - m for Natural n and m
def z.minus.at(lt: Bool, +n: Nat, +m: Nat) -> ZV:
  match lt:
    case True{}:
      ZvNeg{Nat.sub(Nat.sub(m, n), 1n)}
    case False{}:
      ZvNat{Nat.sub(n, m)}

def z.minus(+n: Nat, +m: Nat) -> ZV:
  z.minus.at(Nat.is_lt(n, m), n, m)

# -n for Natural n
def z.negn(n: Nat) -> ZV:
  match n:
    case 0n:
      ZvNat{0n}
    case 1n+k:
      ZvNeg{k}

# (+), (-) and (<) at Int; anything but two numbers, an error
def z.add(a: ZV, b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{ZvNat{Nat.add(m, n)}}
        case ZvNeg{n}:
          Some{z.minus(m, 1n+n)}
        case _:
          None{}
    case ZvNeg{m}:
      match b:
        case ZvNat{n}:
          Some{z.minus(n, 1n+m)}
        case ZvNeg{n}:
          Some{ZvNeg{1n+Nat.add(m, n)}}
        case _:
          None{}
    case _:
      None{}

def z.sub(a: ZV, b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{z.minus(m, n)}
        case ZvNeg{n}:
          Some{ZvNat{Nat.add(m, 1n+n)}}
        case _:
          None{}
    case ZvNeg{m}:
      match b:
        case ZvNat{n}:
          Some{ZvNeg{Nat.add(m, n)}}
        case ZvNeg{n}:
          Some{z.minus(n, m)}
        case _:
          None{}
    case _:
      None{}

def z.lt(a: ZV, b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{ZvBool{Nat.is_lt(m, n)}}
        case ZvNeg{n}:
          Some{ZvBool{False{}}}
        case _:
          None{}
    case ZvNeg{m}:
      match b:
        case ZvNat{n}:
          Some{ZvBool{True{}}}
        case ZvNeg{n}:
          Some{ZvBool{Nat.is_lt(n, m)}}
        case _:
          None{}
    case _:
      None{}

# div and mod at Int round toward minus infinity, mod with the divisor's
# sign.  Where the signs differ, of q = |a| div |b| and r = |a| mod |b|:
# the quotient is -q when r is 0, else -(q+1)
def z.divx(+q: Nat, r: Nat) -> ZV:
  match r:
    case 0n:
      z.negn(q)
    case 1n+k:
      ZvNeg{q}

# and the remainder 0 when r is 0, else |b| - r with b's sign: at a
# negative divisor -(n+1), -(n+1-r); at a positive one n, n - r
def z.modn(+n: Nat, r: Nat) -> ZV:
  match r:
    case 0n:
      ZvNat{0n}
    case 1n+k:
      ZvNeg{Nat.sub(n, 1n+k)}

def z.modp(+n: Nat, r: Nat) -> ZV:
  match r:
    case 0n:
      ZvNat{0n}
    case 1n+k:
      ZvNat{Nat.sub(n, 1n+k)}

# the quotient and remainder of a by b where their signs differ (a, b
# their sizes; at a negative divisor -(n+1), at a positive one b)
def z.dx(+a: Nat, +b: Nat) -> ZV:
  z.divx(Nat.div(a, b), Nat.mod(a, b))

def z.mn(+n: Nat, a: Nat) -> ZV:
  z.modn(n, Nat.mod(a, 1n+n))

def z.mp(+b: Nat, a: Nat) -> ZV:
  z.modp(b, Nat.mod(a, b))

# div and mod at Int, an error (divide by zero) at 0
def z.div(a: ZV, b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          match n:
            case 0n:
              None{}
            case 1n+q:
              Some{ZvNat{Nat.div(m, 1n+q)}}
        case ZvNeg{n}:
          Some{z.dx(m, 1n+n)}
        case _:
          None{}
    case ZvNeg{m}:
      match b:
        case ZvNat{n}:
          match n:
            case 0n:
              None{}
            case 1n+q:
              Some{z.dx(1n+m, 1n+q)}
        case ZvNeg{n}:
          Some{ZvNat{Nat.div(1n+m, 1n+n)}}
        case _:
          None{}
    case _:
      None{}

def z.mod(a: ZV, b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          match n:
            case 0n:
              None{}
            case 1n+q:
              Some{ZvNat{Nat.mod(m, 1n+q)}}
        case ZvNeg{n}:
          Some{z.mn(n, m)}
        case _:
          None{}
    case ZvNeg{m}:
      match b:
        case ZvNat{n}:
          match n:
            case 0n:
              None{}
            case 1n+q:
              Some{z.mp(1n+q, 1n+m)}
        case ZvNeg{n}:
          Some{z.negn(Nat.mod(1n+m, 1n+n))}
        case _:
          None{}
    case _:
      None{}

# BendRt's wrappers, at Int (their Haskell is any Num's): b'Nat'sub a b =
# max 0 (a - b), b'Nat'div a b = if b == 0 then 0 else a `div` b,
# b'Nat'mod a b = if b == 0 then a else a `mod` b
def z.max0(r: Maybe<&2, ZV>) -> Maybe<&2, ZV>:
  match r:
    case Some{ZvNeg{n}}:
      Some{ZvNat{0n}}
    case _:
      r

# Int's range (PROPOSED.bend's section 8) ----------------------------------------

# GHC's Int has 64 bits: its numbers are -(m+1)..m, m = 2^63 - 1 (127 at
# Int8), and (+), (-) and a literal take a number outside around, modulo
# 2m + 2; div's one answer outside, minBound `div` (-1), is an error
# (GHC.Real's overflowError).  A comparison and mod make no number outside
# their arguments' range.  The model's Int so far has every integer.

# whether v is in -(m+1)..m (anything but a number is)
def z.inr(+m: Nat, v: ZV) -> Bool:
  match v:
    case ZvNat{n}:
      Bool.not(Nat.is_lt(m, n))
    case ZvNeg{n}:
      Bool.not(Nat.is_lt(m, n))
    case _:
      True{}

# 2m + 2, the modulus
def z.k(+m: Nat) -> Nat:
  Nat.add(Nat.add(m, m), 2n)

# r, 0 <= r < 2m + 2, as the range's number: r, or r - (2m + 2) above m
def z.wrapr.at(c: Bool, +m: Nat, +r: Nat) -> ZV:
  match c:
    case True{}:
      ZvNeg{Nat.sub(Nat.add(Nat.add(m, m), 1n), r)}
    case False{}:
      ZvNat{r}

def z.wrapr(+m: Nat, +r: Nat) -> ZV:
  z.wrapr.at(Nat.is_lt(m, r), m, r)

# a number modulo 2m + 2, in the range
def z.wrapx(+m: Nat, v: ZV) -> ZV:
  match v:
    case ZvNat{n}:
      z.wrapr(m, Nat.mod(n, z.k(m)))
    case ZvNeg{n}:
      z.wrapr(m, Nat.mod(Nat.sub(z.k(m), Nat.mod(1n+n, z.k(m))), z.k(m)))
    case y:
      y

# Int's number for v: v in the range, else v taken around
def z.wrap.at(c: Bool, +m: Nat, v: ZV) -> ZV:
  match c:
    case True{}:
      v
    case False{}:
      z.wrapx(m, v)

def z.wrap(+m: Nat, +v: ZV) -> ZV:
  z.wrap.at(z.inr(m, v), m, v)

# v in the range, else an error
def z.chk.at(c: Bool, v: ZV) -> Maybe<&2, ZV>:
  match c:
    case True{}:
      Some{v}
    case False{}:
      None{}

def z.chk(+m: Nat, +v: ZV) -> Maybe<&2, ZV>:
  z.chk.at(z.inr(m, v), v)

# a run's range: every integer (Integer's, the model's Int so far),
# -(m+1)..m with an error where a number leaves it (the exact run that
# stays in Int's range), or GHC's Int of range m
type Rg is Data:
  RgAll{}
  RgIn{m: Nat}
  RgInt{m: Nat}

# the number a literal, (+) or (-) makes, v exactly
def z.rw(+r: Rg, +v: ZV) -> Maybe<&2, ZV>:
  match r:
    case RgAll{}:
      Some{v}
    case RgIn{m}:
      z.chk(m, v)
    case RgInt{m}:
      Some{z.wrap(m, v)}

# the number div makes, v exactly
def z.rd(+r: Rg, +v: ZV) -> Maybe<&2, ZV>:
  match r:
    case RgAll{}:
      Some{v}
    case RgIn{m}:
      z.chk(m, v)
    case RgInt{m}:
      z.chk(m, v)

# b'Nat'sub, its a - b at r (at two Naturals of the range a - b is in it)
def z.subT(+a: ZV, +b: ZV, +r: Rg) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{ZvNat{Nat.sub(m, n)}}
        case _:
          z.max0(Maybe.bind(&2, ZV, ZV, z.sub(ZvNat{m}, b), y => z.rw(r, y)))
    case _:
      z.max0(Maybe.bind(&2, ZV, ZV, z.sub(a, b), y => z.rw(r, y)))

def z.zero(b: ZV) -> Bool:
  match b:
    case ZvNat{0n}:
      True{}
    case _:
      False{}

def z.divT.at(c: Bool, +a: ZV, +b: ZV) -> Maybe<&2, ZV>:
  match c:
    case True{}:
      Some{ZvNat{0n}}
    case False{}:
      z.div(a, b)

def z.modT.at(c: Bool, +a: ZV, +b: ZV) -> Maybe<&2, ZV>:
  match c:
    case True{}:
      Some{a}
    case False{}:
      z.mod(a, b)

def z.divT(+a: ZV, +b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{ZvNat{Nat.div(m, n)}}
        case _:
          z.divT.at(z.zero(b), ZvNat{m}, b)
    case _:
      z.divT.at(z.zero(b), a, b)

def z.modT(+a: ZV, +b: ZV) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      match b:
        case ZvNat{n}:
          Some{ZvNat{Nat.mod(m, n)}}
        case _:
          z.modT.at(z.zero(b), ZvNat{m}, b)
    case _:
      z.modT.at(z.zero(b), a, b)

# a primitive at Int, at two numbers, at range r
def z.atw(p: Prim, +a: ZV, +b: ZV, +r: Rg) -> Maybe<&2, ZV>:
  match p:
    case PAdd{}:
      Maybe.bind(&2, ZV, ZV, z.add(a, b), y => z.rw(r, y))
    case PLt{}:
      z.lt(a, b)
    case PSub{}:
      Maybe.bind(&2, ZV, ZV, z.sub(a, b), y => z.rw(r, y))
    case PDiv{}:
      Maybe.bind(&2, ZV, ZV, z.div(a, b), y => z.rd(r, y))
    case PMod{}:
      z.mod(a, b)
    case PSubT{}:
      z.subT(a, b, r)
    case PDivT{}:
      Maybe.bind(&2, ZV, ZV, z.divT(a, b), y => z.rd(r, y))
    case PModT{}:
      z.modT(a, b)

# at every integer
def z.at(p: Prim, +a: ZV, +b: ZV) -> Maybe<&2, ZV>:
  z.atw(p, a, b, RgAll{})

# its argument: a pair of numbers, anything else an error
def z.nb(p: Prim, +a: ZV, b: ZV, +r: Rg) -> Maybe<&2, ZV>:
  match b:
    case ZvNat{n}:
      z.atw(p, a, ZvNat{n}, r)
    case ZvNeg{n}:
      z.atw(p, a, ZvNeg{n}, r)
    case _:
      None{}

def z.ab(p: Prim, a: ZV, b: ZV, +r: Rg) -> Maybe<&2, ZV>:
  match a:
    case ZvNat{m}:
      z.nb(p, ZvNat{m}, b, r)
    case ZvNeg{m}:
      z.nb(p, ZvNeg{m}, b, r)
    case _:
      None{}

def z.primw(p: Prim, v: ZV, +r: Rg) -> Maybe<&2, ZV>:
  match v:
    case ZvPair{a, b}:
      z.ab(p, a, b, r)
    case _:
      None{}

def z.prim(p: Prim, v: ZV) -> Maybe<&2, ZV>:
  z.primw(p, v, RgAll{})

def z.fst(v: ZV) -> Maybe<&2, ZV>:
  match v:
    case ZvPair{a, b}:
      Some{a}
    case _:
      None{}

def z.snd(v: ZV) -> Maybe<&2, ZV>:
  match v:
    case ZvPair{a, b}:
      Some{b}
    case _:
      None{}

def z.pair(a: Maybe<&2, ZV>, b: Maybe<&2, ZV>) -> Maybe<&2, ZV>:
  match a b:
    case Some{u} Some{v}:
      Some{ZvPair{u, v}}
    case _ _:
      None{}

def z.if(c: Maybe<&2, ZV>, a: Maybe<&2, ZV>, e: Maybe<&2, ZV>) -> Maybe<&2, ZV>:
  match c:
    case Some{ZvBool{True{}}}:
      a
    case Some{ZvBool{False{}}}:
      e
    case _:
      None{}

# Haskell's meaning at Int, at range r: the answer of t at v, None an
# error
def eval.zr(+r: Rg, +t: HTm, +v: ZV) -> Maybe<&2, ZV>:
  match t:
    case HId{}:
      Some{v}
    case HComp{g, f}:
      Maybe.bind(&2, ZV, ZV, eval.zr(r, f, v), y => eval.zr(r, g, y))
    case HFst{}:
      z.fst(v)
    case HSnd{}:
      z.snd(v)
    case HPr{f, g}:
      z.pair(eval.zr(r, f, v), eval.zr(r, g, v))
    case HInl{}:
      Some{ZvInl{v}}
    case HInr{}:
      Some{ZvInr{v}}
    case HCase{f, g}:
      match v:
        case ZvInl{a}:
          eval.zr(r, f, a)
        case ZvInr{b}:
          eval.zr(r, g, b)
        case _:
          None{}
    case HLit{n}:
      z.rw(r, ZvNat{n})
    case HPrim{p}:
      z.primw(p, v, r)
    case HIf{c, a, e}:
      z.if(eval.zr(r, c, v), eval.zr(r, a, v), eval.zr(r, e, v))
    case HFold{z, s}:
      match v:
        case ZvNil{}:
          eval.zr(r, z, ZvUnit{})
        case ZvCons{hd, tl}:
          Maybe.bind(&2, ZV, ZV, eval.zr(r, t, tl), q => eval.zr(r, s, ZvPair{hd, q}))
        case _:
          None{}
    case HErr{}:
      None{}

# Haskell's meaning at Int, every integer (Integer's: section 8 has Int's
# 64 bits)
def eval.z(+t: HTm, +v: ZV) -> Maybe<&2, ZV>:
  eval.zr(RgAll{}, t, v)

# whether a program never subtracts (Haskell's (-); Survey.bend's int-sub
# refuses it at an Int F takes to Nat, and negate and pred with it)
def p.nosub(p: Prim) -> Bool:
  match p:
    case PSub{}:
      False{}
    case _:
      True{}

def nosub(t: HTm) -> Bool:
  match t:
    case HComp{g, f}:
      Bool.and(nosub(g), nosub(f))
    case HPr{f, g}:
      Bool.and(nosub(f), nosub(g))
    case HCase{f, g}:
      Bool.and(nosub(f), nosub(g))
    case HPrim{p}:
      p.nosub(p)
    case HIf{c, a, e}:
      Bool.and(nosub(c), Bool.and(nosub(a), nosub(e)))
    case HFold{z, s}:
      Bool.and(nosub(z), nosub(s))
    case _:
      True{}

# General recursion: fuel ------------------------------------------------------
#
# Haskell recurses as it likes, and a recursion may never stop; Bend's
# checker takes only recursion it sees end, so cata writes a general
# recursion with fuel (README, "Recursion Bend refuses: fuel"): an extra
# argument, 2^32 - 1 at the start, one less at each call, and the type's
# default (Fold.bend's fd.dv) when it runs out.  The user, 11-23: keep the
# default; the theorem covers the programs that stop.  The model's general
# recursion is Haskell's `until p s` (until p s x = if p x then x else
# until p s (s x)), p and s the fragment's programs: any loop is one.

# a Haskell run of k steps at most: ROut when k runs out first (Haskell's
# own program may never stop: ROut at every k), else its answer
type Run is Data:
  ROut{}
  RDone{r: Maybe<&2, HV>}

# Haskell's `until p s`
type HL is Data:
  HUntil{p: HTm, s: HTm}

# its run at x, k steps at most: c is p's answer at x, n is s's
def run.h(k: Nat, +p: HTm, +s: HTm, +x: HV, c: Maybe<&2, HV>, n: Maybe<&2, HV>) -> Run:
  match k:
    case 0n:
      ROut{}
    case 1n+j:
      match c:
        case Some{HvBool{True{}}}:
          RDone{Some{x}}
        case Some{HvBool{False{}}}:
          match n:
            case Some{+y}:
              run.h(j, p, s, y, eval.h(p, y), eval.h(s, y))
            case None{}:
              RDone{None{}}
        case _:
          RDone{None{}}

def eval.hl(k: Nat, h: HL, +x: HV) -> Run:
  match h:
    case HUntil{+p, +s}:
      run.h(k, p, s, x, eval.h(p, x), eval.h(s, x))

# Bend's fuelled def: n the fuel, d the default it answers when the fuel
# runs out
type BL is Data:
  BLoop{n: Nat, p: BTm, s: BTm, d: BV}

def run.b(n: Nat, +p: BTm, +s: BTm, +d: BV, +y: BV, c: Maybe<&2, BV>, m: Maybe<&2, BV>) -> Maybe<&2, BV>:
  match n:
    case 0n:
      Some{d}
    case 1n+j:
      match c:
        case Some{BvBool{True{}}}:
          Some{y}
        case Some{BvBool{False{}}}:
          match m:
            case Some{+z}:
              run.b(j, p, s, d, z, eval.b(p, z), eval.b(s, z))
            case None{}:
              None{}
        case _:
          None{}

def eval.bl(b: BL, +y: BV) -> Maybe<&2, BV>:
  match b:
    case BLoop{n, +p, +s, +d}:
      run.b(n, p, s, d, y, eval.b(p, y), eval.b(s, y))

# G's Haskell for a fuelled def: the fuel and the default kept, as
# Back.bend writes a def's fuel (a Haskell argument counting down)
type GL is Data:
  GLoop{n: Nat, p: HTm, s: HTm, d: HV}

def run.g(n: Nat, +p: HTm, +s: HTm, +d: HV, +x: HV, c: Maybe<&2, HV>, m: Maybe<&2, HV>) -> Maybe<&2, HV>:
  match n:
    case 0n:
      Some{d}
    case 1n+j:
      match c:
        case Some{HvBool{True{}}}:
          Some{x}
        case Some{HvBool{False{}}}:
          match m:
            case Some{+y}:
              run.g(j, p, s, d, y, eval.h(p, y), eval.h(s, y))
            case None{}:
              None{}
        case _:
          None{}

def eval.gl(g: GL, +x: HV) -> Maybe<&2, HV>:
  match g:
    case GLoop{n, +p, +s, +d}:
      run.g(n, p, s, d, x, eval.h(p, x), eval.h(s, x))

# cata's fuel, Desugar.bend's fuel(): 2^32 - 1
def fuel() -> Nat:
  4294967295n

# F with fuel n: the loop's parts by F, the default Nat's (fd.dv: 0)
def F.ln(n: Nat, h: HL) -> BL:
  match h:
    case HUntil{p, s}:
      BLoop{n, F(p), F(s), BvNat{0n}}

# F on a loop: cata's fuel
def F.l(h: HL) -> BL:
  F.ln(fuel(), h)

def G.l(b: BL) -> GL:
  match b:
    case BLoop{n, p, s, d}:
      GLoop{n, G(p), G(s), dec(d)}

# a <= b
def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      le(i, j)

# Int's range: GHC's Int ------------------------------------------------------

# h at GHC's Int of range m: (+), (-) and literals wrap around, div at
# minBound by -1 errs
def eval.int(+m: Nat, +t: HTm, +v: ZV) -> Maybe<&2, ZV>:
  eval.zr(RgInt{m}, t, v)

# h's exact run while it stays in -(m+1)..m: an error where a number leaves
# the range
def eval.in(+m: Nat, +t: HTm, +v: ZV) -> Maybe<&2, ZV>:
  eval.zr(RgIn{m}, t, v)

# GHC's Int: m = 2^63 - 1 (a term: Bend's literals stop at 2^32 - 1, and
# its Nat is unary, so no proof computes with it)
def int.max() -> Nat:
  Nat.sub(Nat.mul(Nat.mul(65536n, 65536n), 2147483648n), 1n)

# Int8's: 127
def int8.max() -> Nat:
  127n

# Laziness (PROPOSED.bend's section 9) ------------------------------------------

# Haskell is lazy: a pair's parts, a sum's, a list's head and tail are
# thunks, each an answer or an error (None), looked at only when a
# projection, a case, a primitive, an if or a fold needs it; Bend, and
# eval.h, are strict.  LV is a value in weak head normal form, its parts
# Maybe LV; a program's lazy meaning takes a thunk to one.
type LV is Data:
  LvNat{n: Nat}
  LvBool{b: Bool}
  LvUnit{}
  LvPair{a: Maybe<&2, LV>, b: Maybe<&2, LV>}
  LvInl{a: Maybe<&2, LV>}
  LvInr{b: Maybe<&2, LV>}
  LvNil{}
  LvCons{h: Maybe<&2, LV>, t: Maybe<&2, LV>}

# a value with no error in it, as a lazy one
def lz(x: HV) -> LV:
  match x:
    case HvNat{n}:
      LvNat{n}
    case HvBool{b}:
      LvBool{b}
    case HvUnit{}:
      LvUnit{}
    case HvPair{a, b}:
      LvPair{Some{lz(a)}, Some{lz(b)}}
    case HvInl{a}:
      LvInl{Some{lz(a)}}
    case HvInr{b}:
      LvInr{Some{lz(b)}}
    case HvNil{}:
      LvNil{}
    case HvCons{h, t}:
      LvCons{Some{lz(h)}, Some{lz(t)}}

def lzM(r: Maybe<&2, HV>) -> Maybe<&2, LV>:
  match r:
    case None{}:
      None{}
    case Some{v}:
      Some{lz(v)}

# a primitive looks at both numbers of its pair
def l.nn.b(a: Nat, y: Maybe<&2, LV>) -> NN:
  match y:
    case Some{LvNat{b}}:
      NN{a, b}
    case _:
      NNo{}

def l.nn.p(x: Maybe<&2, LV>, y: Maybe<&2, LV>) -> NN:
  match x:
    case Some{LvNat{a}}:
      l.nn.b(a, y)
    case _:
      NNo{}

def l.nn(x: Maybe<&2, LV>) -> NN:
  match x:
    case Some{LvPair{a, b}}:
      l.nn.p(a, b)
    case _:
      NNo{}

def l.pv(v: PV) -> Maybe<&2, LV>:
  match v:
    case PvNat{n}:
      Some{LvNat{n}}
    case PvBool{b}:
      Some{LvBool{b}}
    case PvNo{}:
      None{}

def l.fst(x: Maybe<&2, LV>) -> Maybe<&2, LV>:
  match x:
    case Some{LvPair{a, b}}:
      a
    case _:
      None{}

def l.snd(x: Maybe<&2, LV>) -> Maybe<&2, LV>:
  match x:
    case Some{LvPair{a, b}}:
      b
    case _:
      None{}

def l.if(c: Maybe<&2, LV>, a: Maybe<&2, LV>, e: Maybe<&2, LV>) -> Maybe<&2, LV>:
  match c:
    case Some{LvBool{True{}}}:
      a
    case Some{LvBool{False{}}}:
      e
    case _:
      None{}

# Haskell's lazy meaning: the answer of t at the thunk x (a pair's parts
# computed only when looked at; a fold's recursive answer a thunk too)
def eval.lz(+t: HTm, +x: Maybe<&2, LV>) -> Maybe<&2, LV>:
  match t:
    case HId{}:
      x
    case HComp{g, f}:
      eval.lz(g, eval.lz(f, x))
    case HFst{}:
      l.fst(x)
    case HSnd{}:
      l.snd(x)
    case HPr{f, g}:
      Some{LvPair{eval.lz(f, x), eval.lz(g, x)}}
    case HInl{}:
      Some{LvInl{x}}
    case HInr{}:
      Some{LvInr{x}}
    case HCase{f, g}:
      match x:
        case Some{LvInl{a}}:
          eval.lz(f, a)
        case Some{LvInr{b}}:
          eval.lz(g, b)
        case _:
          None{}
    case HLit{n}:
      Some{LvNat{n}}
    case HPrim{p}:
      l.pv(p.nn(p, l.nn(x)))
    case HIf{c, a, e}:
      l.if(eval.lz(c, x), eval.lz(a, x), eval.lz(e, x))
    case HFold{z, s}:
      match x:
        case Some{LvNil{}}:
          eval.lz(z, Some{LvUnit{}})
        case Some{LvCons{hd, tl}}:
          eval.lz(s, Some{LvPair{hd, eval.lz(t, tl)}})
        case _:
          None{}
    case HErr{}:
      None{}
