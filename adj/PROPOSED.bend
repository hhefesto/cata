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
