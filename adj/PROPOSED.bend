# cata as a functor and an adjunction, proposed for the human to move into
# a LAWS.bend (or reword or drop); PROOF.bend proves them, and
# `bend PROOF.bend --verdict` rechecks the proofs with BendTT's kernel.
#
# Core.bend has the two categories on cata's fragment: Haskell's programs
# (HTm, their meaning eval.h, None an error) and Bend's (BTm, eval.b, None
# a failure value), F (hs2bend) and G (bend2hs) between them, and F.tot,
# F as cata had it (Haskell's div and mod to Bend's total Nat.div and
# Nat.mod).

import Base
import ./Core.bend as C

# The order: q implements p, p <= q, when q answers what p answers
# wherever p answers
def Le.h(+p: C.HTm, +q: C.HTm) -> Type:
  @x: C.HV -> @v: C.HV -> {C.eval.h(p, x) == Some{v} : Maybe<&2, C.HV>} -> {C.eval.h(q, x) == Some{v} : Maybe<&2, C.HV>}

def Le.b(+p: C.BTm, +q: C.BTm) -> Type:
  @y: C.BV -> @w: C.BV -> {C.eval.b(p, y) == Some{w} : Maybe<&2, C.BV>} -> {C.eval.b(q, y) == Some{w} : Maybe<&2, C.BV>}

# 1. F and G are functors, on the nose: each keeps identities and
# composition (cata's compositionality, so a module's translation is its
# parts', linked), and pairs, sums and folds (lists' initial algebra: F
# takes a catamorphism to a catamorphism)

law F.id:
  {C.F(C.HId{}) == C.BId{} : C.BTm}

law F.comp:
  for g: C.HTm
  for f: C.HTm
  {C.F(C.HComp{g, f}) == C.BComp{C.F(g), C.F(f)} : C.BTm}

law F.pair:
  for f: C.HTm
  for g: C.HTm
  {C.F(C.HPr{f, g}) == C.BPr{C.F(f), C.F(g)} : C.BTm}

law F.case:
  for f: C.HTm
  for g: C.HTm
  {C.F(C.HCase{f, g}) == C.BCase{C.F(f), C.F(g)} : C.BTm}

law F.fold:
  for z: C.HTm
  for s: C.HTm
  {C.F(C.HFold{z, s}) == C.BFold{C.F(z), C.F(s)} : C.BTm}

law G.id:
  {C.G(C.BId{}) == C.HId{} : C.HTm}

law G.comp:
  for g: C.BTm
  for f: C.BTm
  {C.G(C.BComp{g, f}) == C.HComp{C.G(g), C.G(f)} : C.HTm}

law G.fold:
  for z: C.BTm
  for s: C.BTm
  {C.G(C.BFold{z, s}) == C.HFold{C.G(z), C.G(s)} : C.HTm}

# on objects' elements: F's values and G's are each other's inverses
law dec.enc:
  for x: C.HV
  {C.dec(C.enc(x)) == x : C.HV}

law enc.dec:
  for y: C.BV
  {C.enc(C.dec(y)) == y : C.BV}

# 2. The squares: F's program means what Haskell's means, at every input
# (an error a failure value), and G's what Bend's means.  Proved one
# construct at a time, so they hold for every program.

law sq.F:
  for +t: C.HTm
  for +x: C.HV
  {C.encM(C.eval.h(t, x)) == C.eval.b(C.F(t), C.enc(x)) : Maybe<&2, C.BV>}

law sq.G:
  for +t: C.BTm
  for +y: C.BV
  {C.decM(C.eval.b(t, y)) == C.eval.h(C.G(t), C.dec(y)) : Maybe<&2, C.HV>}

# 3. The adjunction F -| G: F h <= b exactly when h <= G b (adj.FG.l one
# way, adj.FG.r the other), so "b correctly implements h" is checked on
# whichever side is easier (Haskell with GHC, Bend with BendTT).

law adj.FG.l:
  for +h: C.HTm
  for +b: C.BTm
  for le: Le.b(C.F(h), b)
  Le.h(h, C.G(b))

law adj.FG.r:
  for +h: C.HTm
  for +b: C.BTm
  for le: Le.h(h, C.G(b))
  Le.b(C.F(h), b)

# and G -| F: G b <= h exactly when b <= F h.  With both, on this fragment
# (Natural's numbers, where F's values and G's are each other's inverses)
# F and G are an adjoint equivalence.  At Int and Integer, which F takes
# to Nat, only G -| F survives: section 5.

law adj.GF.l:
  for +h: C.HTm
  for +b: C.BTm
  for le: Le.h(C.G(b), h)
  Le.b(b, C.F(h))

law adj.GF.r:
  for +h: C.HTm
  for +b: C.BTm
  for le: Le.b(b, C.F(h))
  Le.h(C.G(b), h)

# 4. F.tot, F as cata had it, is no left adjoint: h0, x `mod` 0, is an error
# everywhere, so h0 <= G(b) for every b; but F.tot(h0) answers 0 at 0 (Base's
# Nat.mod(0, 0)), so F.tot(h0) <= b fails for b, the constant 7.

def h0() -> C.HTm:
  C.HComp{C.HPrim{C.PMod{}}, C.HPr{C.HId{}, C.HLit{0n}}}

def b7() -> C.BTm:
  C.BLit{7n}

law tot.below:
  Le.h(h0(), C.G(b7()))

law tot.not:
  for le: Le.b(C.F.tot(h0()), b7())
  Empty

# 5. Int and Integer, which F takes to Nat as it takes Natural (the user,
# 11-23: keep Nat, so only G -| F at those types).  h at Int means hz, on
# Int's values (Core.bend's ZV); where F's Nat is right, h means at a
# Natural value what it means at Natural, its answer Natural: Agree.  (The
# survey takes Int to Nat only where nothing subtracts, so every number h
# makes from non-negative ones is non-negative; that is the claim Agree
# states, here a hypothesis, which section 6 proves of every h that never
# subtracts, h's meaning at Int its own.)  G's program used at Int is gz
# (fromIntegral, an underflow error at a negative number, in front of it).

def Agree(+h: C.HTm, hz: C.ZV -> Maybe<&2, C.ZV>) -> Type:
  @x: C.HV -> {hz(C.up(x)) == C.upM(C.eval.h(h, x)) : Maybe<&2, C.ZV>}

def Le.z(p: C.ZV -> Maybe<&2, C.ZV>, q: C.ZV -> Maybe<&2, C.ZV>) -> Type:
  @z: C.ZV -> @u: C.ZV -> {p(z) == Some{u} : Maybe<&2, C.ZV>} -> {q(z) == Some{u} : Maybe<&2, C.ZV>}

# G -| F at Int: G b <= h exactly when b <= F h
law adj.GF.int.l:
  for +h: C.HTm
  for +b: C.BTm
  for hz: C.ZV -> Maybe<&2, C.ZV>
  for ag: Agree(h, hz)
  for le: Le.z(z => C.gz(b, z), hz)
  Le.b(b, C.F(h))

law adj.GF.int.r:
  for +h: C.HTm
  for +b: C.BTm
  for hz: C.ZV -> Maybe<&2, C.ZV>
  for ag: Agree(h, hz)
  for le: Le.b(b, C.F(h))
  Le.z(z => C.gz(b, z), hz)

# and F -| G fails there: its one way, F h <= b giving h <= G b, does not
# hold at Int (h the identity answers -1 at -1, where G's program errs)
def FG.int() -> Type:
  @h: C.HTm -> @b: C.BTm -> @hz: (C.ZV -> Maybe<&2, C.ZV>) -> Agree(h, hz) -> Le.b(C.F(h), b) -> Le.z(hz, z => C.gz(b, z))

law adj.FG.int.not:
  for adj: FG.int()
  Empty

# 6. Agree, proved.  h at Int means eval.z (Core.bend: h run on Int's
# values with Int's own arithmetic; INT.bend checks that arithmetic is
# GHC's on a grid, by computation).  For every h that never subtracts
# (nosub: the survey's int-sub refusal at an Int F takes to Nat), h at Int
# means at a Natural value what h at Natural means: section 5's hypothesis
# holds of it, so G -| F at Int needs none.  And a program that subtracts
# need not agree: x - y at (0, 1) is an error at Natural, -1 at Int.

law agree:
  for +h: C.HTm
  for +e: {C.nosub(h) == True{} : Bool}
  Agree(h, z => C.eval.z(h, z))

law agree.sub.not:
  for ag: Agree(C.HPrim{C.PSub{}}, z => C.eval.z(C.HPrim{C.PSub{}}, z))
  Empty

# G -| F at Int for every h that never subtracts, h's meaning at Int its
# own: G b <= h exactly when b <= F h
law adj.GF.nosub.l:
  for +h: C.HTm
  for +b: C.BTm
  for +e: {C.nosub(h) == True{} : Bool}
  for le: Le.z(z => C.gz(b, z), z => C.eval.z(h, z))
  Le.b(b, C.F(h))

law adj.GF.nosub.r:
  for +h: C.HTm
  for +b: C.BTm
  for +e: {C.nosub(h) == True{} : Bool}
  for le: Le.b(b, C.F(h))
  Le.z(z => C.gz(b, z), z => C.eval.z(h, z))

# 7. General recursion, with fuel (Core.bend's loops: Haskell's until p s,
# and cata's fuelled def, the type's default where the fuel runs out).
# The user, 11-23: keep the default; the theorem covers the programs that
# stop.  For every fuel n (cata's is fuel(), 2^32 - 1): F with fuel n
# means what Haskell's loop means wherever it stops within n steps, and
# F -| G on the loops that stop within n steps at every input; a loop that
# never stops breaks it (F answers the default where Haskell answers
# nothing), at every n.

# h stops within n steps at every input
def Stops(+h: C.HL, +n: Nat) -> Type:
  @x: C.HV -> {C.eval.hl(n, h, x) == C.ROut{} : C.Run} -> Empty

# g implements the loop h: it answers what h answers, wherever h stops
# with an answer
def Le.hl(+h: C.HL, +g: C.GL) -> Type:
  @x: C.HV -> @v: C.HV -> @k: Nat -> {C.eval.hl(k, h, x) == C.RDone{Some{v}} : C.Run} -> {C.eval.gl(g, x) == Some{v} : Maybe<&2, C.HV>}

def Le.bl(+p: C.BL, +q: C.BL) -> Type:
  @y: C.BV -> @w: C.BV -> {C.eval.bl(p, y) == Some{w} : Maybe<&2, C.BV>} -> {C.eval.bl(q, y) == Some{w} : Maybe<&2, C.BV>}

# the squares: F's fuelled def with fuel n means what h means wherever h
# stops within k <= n steps; G's Haskell means what Bend's means, always
law sq.F.l:
  for +k: Nat
  for +n: Nat
  for +h: C.HL
  for +x: C.HV
  for -r: Maybe<&2, C.HV>
  for e: {C.eval.hl(k, h, x) == C.RDone{r} : C.Run}
  for le: {C.le(k, n) == True{} : Bool}
  {C.eval.bl(C.F.ln(n, h), C.enc(x)) == C.encM(r) : Maybe<&2, C.BV>}

law sq.G.l:
  for +b: C.BL
  for +y: C.BV
  {C.decM(C.eval.bl(b, y)) == C.eval.gl(C.G.l(b), C.dec(y)) : Maybe<&2, C.HV>}

# F -| G on the loops that stop within the fuel: F h <= b exactly when
# h <= G b
law adj.FG.loop.l:
  for +n: Nat
  for +h: C.HL
  for +b: C.BL
  for st: Stops(h, n)
  for le: Le.bl(C.F.ln(n, h), b)
  Le.hl(h, C.G.l(b))

law adj.FG.loop.r:
  for +n: Nat
  for +h: C.HL
  for +b: C.BL
  for st: Stops(h, n)
  for le: Le.hl(h, C.G.l(b))
  Le.bl(C.F.ln(n, h), b)

# at cata's own fuel
law adj.FG.fuel.l:
  for +h: C.HL
  for +b: C.BL
  for st: Stops(h, C.fuel())
  for le: Le.bl(C.F.l(h), b)
  Le.hl(h, C.G.l(b))

law adj.FG.fuel.r:
  for +h: C.HL
  for +b: C.BL
  for st: Stops(h, C.fuel())
  for le: Le.hl(h, C.G.l(b))
  Le.bl(C.F.l(h), b)

# and without Stops it fails: hn, until (0 < 0) id, never stops (no run
# of it ends, at any input), so every G b implements it; but F's def of
# it answers the default 0 at 0 (its fuel runs out), where bn7, a loop
# with no fuel and the default 7, answers 7
def hn() -> C.HL:
  C.HUntil{C.HComp{C.HPrim{C.PLt{}}, C.HPr{C.HLit{0n}, C.HLit{0n}}}, C.HId{}}

def bn7() -> C.BL:
  C.BLoop{0n, C.BId{}, C.BId{}, C.BvNat{7n}}

law loop.never:
  for k: Nat
  for +x: C.HV
  {C.eval.hl(k, hn(), x) == C.ROut{} : C.Run}

law loop.default:
  for n: Nat
  {C.eval.bl(C.F.ln(n, hn()), C.BvNat{0n}) == Some{C.BvNat{0n}} : Maybe<&2, C.BV>}

def FG.loop(+n: Nat) -> Type:
  @h: C.HL -> @b: C.BL -> Le.hl(h, C.G.l(b)) -> Le.bl(C.F.ln(n, h), b)

law adj.FG.loop.not:
  for n: Nat
  for adj: FG.loop(n)
  Empty

# 8. Int's range.  GHC's Int has 64 bits: a number outside -(m+1)..m
# (m = 2^63 - 1, Core.bend's int.max()) that (+), (-) or a literal makes
# is taken around, modulo 2m + 2, and minBound `div` (-1) is an error,
# where sections 5 and 6 have every integer (Integer's).  Core.bend has
# both at any m: eval.int is GHC's Int of range m, eval.in the exact run
# while it stays in the range (an error where a number leaves it); INT.bend
# checks the model's Int8 (m = 127) against GHC's Int8 on a grid.  For
# every m: where h's run stays in the range, GHC's Int answers what every
# integer does (range.int, range.z), so section 6 holds there of Int's own
# 64 bits (agree.int: at a Natural value, h at Int means what h at Natural
# means); and the hypothesis is needed: x + x at 127 is -2 at Int8, 254
# at every integer (range.int8, range.not).

law range.int:
  for +m: Nat
  for +h: C.HTm
  for +v: C.ZV
  for +u: C.ZV
  for e: {C.eval.in(m, h, v) == Some{u} : Maybe<&2, C.ZV>}
  {C.eval.int(m, h, v) == Some{u} : Maybe<&2, C.ZV>}

law range.z:
  for +m: Nat
  for +h: C.HTm
  for +v: C.ZV
  for +u: C.ZV
  for e: {C.eval.in(m, h, v) == Some{u} : Maybe<&2, C.ZV>}
  {C.eval.z(h, v) == Some{u} : Maybe<&2, C.ZV>}

law agree.int:
  for +m: Nat
  for +h: C.HTm
  for +e: {C.nosub(h) == True{} : Bool}
  for +x: C.HV
  for +u: C.ZV
  for +ei: {C.eval.in(m, h, C.up(x)) == Some{u} : Maybe<&2, C.ZV>}
  {C.eval.int(m, h, C.up(x)) == C.upM(C.eval.h(h, x)) : Maybe<&2, C.ZV>}

# at GHC's Int, 64 bits
law agree.int64:
  for +h: C.HTm
  for +e: {C.nosub(h) == True{} : Bool}
  for +x: C.HV
  for +u: C.ZV
  for +ei: {C.eval.in(C.int.max(), h, C.up(x)) == Some{u} : Maybe<&2, C.ZV>}
  {C.eval.int(C.int.max(), h, C.up(x)) == C.upM(C.eval.h(h, x)) : Maybe<&2, C.ZV>}

# x + x
def hdbl() -> C.HTm:
  C.HComp{C.HPrim{C.PAdd{}}, C.HPr{C.HId{}, C.HId{}}}

law range.int8:
  {C.eval.int(C.int8.max(), hdbl(), C.ZvNat{127n}) == Some{C.ZvNeg{1n}} : Maybe<&2, C.ZV>}

law range.not:
  for e: {C.eval.int(C.int8.max(), hdbl(), C.ZvNat{127n}) == C.eval.z(hdbl(), C.ZvNat{127n}) : Maybe<&2, C.ZV>}
  Empty

# 9. Laziness.  Haskell is lazy and Bend is strict: the squares are about
# eval.h, h's strict meaning; eval.lz is Haskell's own, lazy (Core.bend:
# a value's parts are thunks, each an answer or an error, looked at only
# when needed).  Wherever the strict meaning answers, the lazy one answers
# the same (lazy.sq), so F's Bend is never wrong under laziness: where it
# answers, h answers that, lazily (lazy.F).  It may answer less: fst (1,
# error) is 1, lazily, and an error in F's Bend (lazy.fe, lazy.fe.F).  So
# the adjunction needs strictness: in the lazy reading of G's Haskell the
# constant 1 is below G b for b = fst (1, failure), whose own Bend fails,
# so F of it is not below b (adj.FG.lazy.not).

law lazy.sq:
  for +t: C.HTm
  for +x: C.HV
  for +v: C.HV
  for e: {C.eval.h(t, x) == Some{v} : Maybe<&2, C.HV>}
  {C.eval.lz(t, Some{C.lz(x)}) == Some{C.lz(v)} : Maybe<&2, C.LV>}

law lazy.F:
  for +h: C.HTm
  for +y: C.BV
  for +w: C.BV
  for e: {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}
  {C.eval.lz(h, Some{C.lz(C.dec(y))}) == Some{C.lz(C.dec(w))} : Maybe<&2, C.LV>}

# fst (1, error)
def hfe() -> C.HTm:
  C.HComp{C.HFst{}, C.HPr{C.HLit{1n}, C.HErr{}}}

law lazy.fe:
  {C.eval.lz(hfe(), Some{C.LvUnit{}}) == Some{C.LvNat{1n}} : Maybe<&2, C.LV>}

law lazy.fe.F:
  {C.eval.b(C.F(hfe()), C.BvUnit{}) == None{} : Maybe<&2, C.BV>}

# h <= g in the lazy reading: g answers lazily what h answers lazily, at
# every value with no error in it
def Le.lz(+h: C.HTm, +g: C.HTm) -> Type:
  @x: C.HV -> @v: C.HV -> {C.eval.lz(h, Some{C.lz(x)}) == Some{C.lz(v)} : Maybe<&2, C.LV>} -> {C.eval.lz(g, Some{C.lz(x)}) == Some{C.lz(v)} : Maybe<&2, C.LV>}

def FG.lazy() -> Type:
  @h: C.HTm -> @b: C.BTm -> Le.lz(h, C.G(b)) -> Le.b(C.F(h), b)

law adj.FG.lazy.not:
  for adj: FG.lazy()
  Empty
