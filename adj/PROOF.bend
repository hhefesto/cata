# The proofs of PROPOSED.bend's laws.  Nothing here is trusted:
# `bend PROOF.bend --verdict` rechecks them with BendTT's kernel.

import Base
import ./Core.bend as C
import ./PROPOSED.bend as P

# 1. functors: by F's and G's definitions

def P.F.id():
  {==}

def P.F.comp(g, f):
  {==}

def P.F.pair(f, g):
  {==}

def P.F.case(f, g):
  {==}

def P.F.fold(z, s):
  {==}

def P.G.id():
  {==}

def P.G.comp(g, f):
  {==}

def P.G.fold(z, s):
  {==}

# values: by induction on the value

def P.dec.enc(x):
  match x:
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{a, b}:
      %P.dec.enc(a) : {C.HvPair{C.dec(C.enc(a)), C.dec(C.enc(b))} == C.HvPair{_, b} : C.HV}
      %P.dec.enc(b) : {C.HvPair{C.dec(C.enc(a)), C.dec(C.enc(b))} == C.HvPair{C.dec(C.enc(a)), _} : C.HV}
      {==}
    case C.HvInl{a}:
      %P.dec.enc(a) : {C.HvInl{C.dec(C.enc(a))} == C.HvInl{_} : C.HV}
      {==}
    case C.HvInr{b}:
      %P.dec.enc(b) : {C.HvInr{C.dec(C.enc(b))} == C.HvInr{_} : C.HV}
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      %P.dec.enc(h) : {C.HvCons{C.dec(C.enc(h)), C.dec(C.enc(t))} == C.HvCons{_, t} : C.HV}
      %P.dec.enc(t) : {C.HvCons{C.dec(C.enc(h)), C.dec(C.enc(t))} == C.HvCons{C.dec(C.enc(h)), _} : C.HV}
      {==}

def P.enc.dec(y):
  match y:
    case C.BvNat{n}:
      {==}
    case C.BvBool{b}:
      {==}
    case C.BvUnit{}:
      {==}
    case C.BvPair{a, b}:
      %P.enc.dec(a) : {C.BvPair{C.enc(C.dec(a)), C.enc(C.dec(b))} == C.BvPair{_, b} : C.BV}
      %P.enc.dec(b) : {C.BvPair{C.enc(C.dec(a)), C.enc(C.dec(b))} == C.BvPair{C.enc(C.dec(a)), _} : C.BV}
      {==}
    case C.BvInl{a}:
      %P.enc.dec(a) : {C.BvInl{C.enc(C.dec(a))} == C.BvInl{_} : C.BV}
      {==}
    case C.BvInr{b}:
      %P.enc.dec(b) : {C.BvInr{C.enc(C.dec(b))} == C.BvInr{_} : C.BV}
      {==}
    case C.BvNil{}:
      {==}
    case C.BvCons{h, t}:
      %P.enc.dec(h) : {C.BvCons{C.enc(C.dec(h)), C.enc(C.dec(t))} == C.BvCons{_, t} : C.BV}
      %P.enc.dec(t) : {C.BvCons{C.enc(C.dec(h)), C.enc(C.dec(t))} == C.BvCons{C.enc(C.dec(h)), _} : C.BV}
      {==}

# 2. the squares, a lemma for each construct

# a pair of numbers is one through enc and dec
def L.nn.F(x: C.HV) -> {C.h.nn(x) == C.b.nn(C.enc(x)) : C.NN}:
  match x:
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvInl{a}:
      {==}
    case C.HvInr{b}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      {==}
    case C.HvPair{p, q}:
      match p:
        case C.HvBool{b}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{c, d}:
          {==}
        case C.HvInl{a}:
          {==}
        case C.HvInr{b}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{h, t}:
          {==}
        case C.HvNat{a}:
          match q:
            case C.HvNat{b}:
              {==}
            case C.HvBool{b}:
              {==}
            case C.HvUnit{}:
              {==}
            case C.HvPair{c, d}:
              {==}
            case C.HvInl{c}:
              {==}
            case C.HvInr{c}:
              {==}
            case C.HvNil{}:
              {==}
            case C.HvCons{h, t}:
              {==}

def L.nn.G(y: C.BV) -> {C.b.nn(y) == C.h.nn(C.dec(y)) : C.NN}:
  match y:
    case C.BvNat{n}:
      {==}
    case C.BvBool{b}:
      {==}
    case C.BvUnit{}:
      {==}
    case C.BvInl{a}:
      {==}
    case C.BvInr{b}:
      {==}
    case C.BvNil{}:
      {==}
    case C.BvCons{h, t}:
      {==}
    case C.BvPair{p, q}:
      match p:
        case C.BvBool{b}:
          {==}
        case C.BvUnit{}:
          {==}
        case C.BvPair{c, d}:
          {==}
        case C.BvInl{a}:
          {==}
        case C.BvInr{b}:
          {==}
        case C.BvNil{}:
          {==}
        case C.BvCons{h, t}:
          {==}
        case C.BvNat{a}:
          match q:
            case C.BvNat{b}:
              {==}
            case C.BvBool{b}:
              {==}
            case C.BvUnit{}:
              {==}
            case C.BvPair{c, d}:
              {==}
            case C.BvInl{c}:
              {==}
            case C.BvInr{c}:
              {==}
            case C.BvNil{}:
              {==}
            case C.BvCons{h, t}:
              {==}

# a primitive's answer
def L.pv.F(v: C.PV) -> {C.encM(C.h.pv(v)) == C.b.pv(v) : Maybe<&2, C.BV>}:
  match v:
    case C.PvNat{n}:
      {==}
    case C.PvBool{b}:
      {==}
    case C.PvNo{}:
      {==}

def L.pv.G(v: C.PV) -> {C.decM(C.b.pv(v)) == C.h.pv(v) : Maybe<&2, C.HV>}:
  match v:
    case C.PvNat{n}:
      {==}
    case C.PvBool{b}:
      {==}
    case C.PvNo{}:
      {==}

# a primitive: Haskell's and Bend's at the same pair of numbers
def L.prim.F(+p: C.Prim, +x: C.HV) -> {C.encM(C.h.prim(p, x)) == C.b.prim(p, C.enc(x)) : Maybe<&2, C.BV>}:
  %L.nn.F(x) : {C.encM(C.h.pv(C.p.nn(p, C.h.nn(x)))) == C.b.pv(C.p.nn(p, _)) : Maybe<&2, C.BV>}
  L.pv.F(C.p.nn(p, C.h.nn(x)))

def L.fst.F(x: C.HV) -> {C.encM(C.h.fst(x)) == C.b.fst(C.enc(x)) : Maybe<&2, C.BV>}:
  match x:
    case C.HvPair{a, b}:
      {==}
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvInl{a}:
      {==}
    case C.HvInr{b}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      {==}

def L.snd.F(x: C.HV) -> {C.encM(C.h.snd(x)) == C.b.snd(C.enc(x)) : Maybe<&2, C.BV>}:
  match x:
    case C.HvPair{a, b}:
      {==}
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvInl{a}:
      {==}
    case C.HvInr{b}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      {==}

def L.pair.F(r: Maybe<&2, C.HV>, s: Maybe<&2, C.HV>) -> {C.encM(C.h.pair(r, s)) == C.b.pair(C.encM(r), C.encM(s)) : Maybe<&2, C.BV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.if.F(c: Maybe<&2, C.HV>, a: Maybe<&2, C.HV>, e: Maybe<&2, C.HV>) -> {C.encM(C.h.if(c, a, e)) == C.b.if(C.encM(c), C.encM(a), C.encM(e)) : Maybe<&2, C.BV>}:
  match c:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case C.HvBool{b}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
        case C.HvNat{n}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{p, q}:
          {==}
        case C.HvInl{p}:
          {==}
        case C.HvInr{p}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{h, t}:
          {==}

# a bind: F's continuation means Haskell's at every value
def L.bind.F(r: Maybe<&2, C.HV>, -kh: C.HV -> Maybe<&2, C.HV>, -kb: C.BV -> Maybe<&2, C.BV>, ih: @v: C.HV -> {C.encM(kh(v)) == kb(C.enc(v)) : Maybe<&2, C.BV>}) -> {C.encM(Maybe.bind(&2, C.HV, C.HV, r, kh)) == Maybe.bind(&2, C.BV, C.BV, C.encM(r), kb) : Maybe<&2, C.BV>}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      ih(v)

# the square for F, by induction on the program (and, at a fold, on the
# list)
def P.sq.F(t, x):
  match t:
    case C.HId{}:
      {==}
    case C.HComp{g, f}:
      %P.sq.F(f, x) : {C.encM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(f, x), y => C.eval.h(g, y))) == Maybe.bind(&2, C.BV, C.BV, _, z => C.eval.b(C.F(g), z)) : Maybe<&2, C.BV>}
      L.bind.F(C.eval.h(f, x), y => C.eval.h(g, y), z => C.eval.b(C.F(g), z), v => P.sq.F(g, v))
    case C.HFst{}:
      L.fst.F(x)
    case C.HSnd{}:
      L.snd.F(x)
    case C.HPr{f, g}:
      %P.sq.F(f, x) : {C.encM(C.h.pair(C.eval.h(f, x), C.eval.h(g, x))) == C.b.pair(_, C.eval.b(C.F(g), C.enc(x))) : Maybe<&2, C.BV>}
      %P.sq.F(g, x) : {C.encM(C.h.pair(C.eval.h(f, x), C.eval.h(g, x))) == C.b.pair(C.encM(C.eval.h(f, x)), _) : Maybe<&2, C.BV>}
      L.pair.F(C.eval.h(f, x), C.eval.h(g, x))
    case C.HInl{}:
      {==}
    case C.HInr{}:
      {==}
    case C.HCase{f, g}:
      match x:
        case C.HvInl{a}:
          P.sq.F(f, a)
        case C.HvInr{b}:
          P.sq.F(g, b)
        case C.HvNat{n}:
          {==}
        case C.HvBool{b}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{a, b}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{h, tl}:
          {==}
    case C.HLit{n}:
      {==}
    case C.HPrim{p}:
      L.prim.F(p, x)
    case C.HIf{c, a, e}:
      %P.sq.F(c, x) : {C.encM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(e, x))) == C.b.if(_, C.eval.b(C.F(a), C.enc(x)), C.eval.b(C.F(e), C.enc(x))) : Maybe<&2, C.BV>}
      %P.sq.F(a, x) : {C.encM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(e, x))) == C.b.if(C.encM(C.eval.h(c, x)), _, C.eval.b(C.F(e), C.enc(x))) : Maybe<&2, C.BV>}
      %P.sq.F(e, x) : {C.encM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(e, x))) == C.b.if(C.encM(C.eval.h(c, x)), C.encM(C.eval.h(a, x)), _) : Maybe<&2, C.BV>}
      L.if.F(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(e, x))
    case C.HFold{z, s}:
      match x:
        case C.HvNil{}:
          P.sq.F(z, C.HvUnit{})
        case C.HvCons{hd, tl}:
          %P.sq.F(t, tl) : {C.encM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, tl), r => C.eval.h(s, C.HvPair{hd, r}))) == Maybe.bind(&2, C.BV, C.BV, _, r => C.eval.b(C.F(s), C.BvPair{C.enc(hd), r})) : Maybe<&2, C.BV>}
          L.bind.F(C.eval.h(t, tl), r => C.eval.h(s, C.HvPair{hd, r}), r => C.eval.b(C.F(s), C.BvPair{C.enc(hd), r}), v => P.sq.F(s, C.HvPair{hd, v}))
        case C.HvNat{n}:
          {==}
        case C.HvBool{b}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{a, b}:
          {==}
        case C.HvInl{a}:
          {==}
        case C.HvInr{b}:
          {==}
    case C.HErr{}:
      {==}

# G's lemmas, the same constructs the other way

def L.prim.G(+p: C.Prim, +y: C.BV) -> {C.decM(C.b.prim(p, y)) == C.h.prim(p, C.dec(y)) : Maybe<&2, C.HV>}:
  %L.nn.G(y) : {C.decM(C.b.pv(C.p.nn(p, C.b.nn(y)))) == C.h.pv(C.p.nn(p, _)) : Maybe<&2, C.HV>}
  L.pv.G(C.p.nn(p, C.b.nn(y)))

def L.fst.G(y: C.BV) -> {C.decM(C.b.fst(y)) == C.h.fst(C.dec(y)) : Maybe<&2, C.HV>}:
  match y:
    case C.BvPair{a, b}:
      {==}
    case C.BvNat{n}:
      {==}
    case C.BvBool{b}:
      {==}
    case C.BvUnit{}:
      {==}
    case C.BvInl{a}:
      {==}
    case C.BvInr{b}:
      {==}
    case C.BvNil{}:
      {==}
    case C.BvCons{h, t}:
      {==}

def L.snd.G(y: C.BV) -> {C.decM(C.b.snd(y)) == C.h.snd(C.dec(y)) : Maybe<&2, C.HV>}:
  match y:
    case C.BvPair{a, b}:
      {==}
    case C.BvNat{n}:
      {==}
    case C.BvBool{b}:
      {==}
    case C.BvUnit{}:
      {==}
    case C.BvInl{a}:
      {==}
    case C.BvInr{b}:
      {==}
    case C.BvNil{}:
      {==}
    case C.BvCons{h, t}:
      {==}

def L.pair.G(r: Maybe<&2, C.BV>, s: Maybe<&2, C.BV>) -> {C.decM(C.b.pair(r, s)) == C.h.pair(C.decM(r), C.decM(s)) : Maybe<&2, C.HV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.if.G(c: Maybe<&2, C.BV>, a: Maybe<&2, C.BV>, e: Maybe<&2, C.BV>) -> {C.decM(C.b.if(c, a, e)) == C.h.if(C.decM(c), C.decM(a), C.decM(e)) : Maybe<&2, C.HV>}:
  match c:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case C.BvBool{b}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
        case C.BvNat{n}:
          {==}
        case C.BvUnit{}:
          {==}
        case C.BvPair{p, q}:
          {==}
        case C.BvInl{p}:
          {==}
        case C.BvInr{p}:
          {==}
        case C.BvNil{}:
          {==}
        case C.BvCons{h, t}:
          {==}

def L.bind.G(r: Maybe<&2, C.BV>, -kb: C.BV -> Maybe<&2, C.BV>, -kh: C.HV -> Maybe<&2, C.HV>, ih: @w: C.BV -> {C.decM(kb(w)) == kh(C.dec(w)) : Maybe<&2, C.HV>}) -> {C.decM(Maybe.bind(&2, C.BV, C.BV, r, kb)) == Maybe.bind(&2, C.HV, C.HV, C.decM(r), kh) : Maybe<&2, C.HV>}:
  match r:
    case None{}:
      {==}
    case Some{w}:
      ih(w)

# the square for G
def P.sq.G(t, y):
  match t:
    case C.BId{}:
      {==}
    case C.BComp{g, f}:
      %P.sq.G(f, y) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.b(f, y), z => C.eval.b(g, z))) == Maybe.bind(&2, C.HV, C.HV, _, x => C.eval.h(C.G(g), x)) : Maybe<&2, C.HV>}
      L.bind.G(C.eval.b(f, y), z => C.eval.b(g, z), x => C.eval.h(C.G(g), x), w => P.sq.G(g, w))
    case C.BFst{}:
      L.fst.G(y)
    case C.BSnd{}:
      L.snd.G(y)
    case C.BPr{f, g}:
      %P.sq.G(f, y) : {C.decM(C.b.pair(C.eval.b(f, y), C.eval.b(g, y))) == C.h.pair(_, C.eval.h(C.G(g), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G(g, y) : {C.decM(C.b.pair(C.eval.b(f, y), C.eval.b(g, y))) == C.h.pair(C.decM(C.eval.b(f, y)), _) : Maybe<&2, C.HV>}
      L.pair.G(C.eval.b(f, y), C.eval.b(g, y))
    case C.BInl{}:
      {==}
    case C.BInr{}:
      {==}
    case C.BCase{f, g}:
      match y:
        case C.BvInl{a}:
          P.sq.G(f, a)
        case C.BvInr{b}:
          P.sq.G(g, b)
        case C.BvNat{n}:
          {==}
        case C.BvBool{b}:
          {==}
        case C.BvUnit{}:
          {==}
        case C.BvPair{a, b}:
          {==}
        case C.BvNil{}:
          {==}
        case C.BvCons{h, tl}:
          {==}
    case C.BLit{n}:
      {==}
    case C.BPrim{p}:
      L.prim.G(p, y)
    case C.BIf{c, a, e}:
      %P.sq.G(c, y) : {C.decM(C.b.if(C.eval.b(c, y), C.eval.b(a, y), C.eval.b(e, y))) == C.h.if(_, C.eval.h(C.G(a), C.dec(y)), C.eval.h(C.G(e), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G(a, y) : {C.decM(C.b.if(C.eval.b(c, y), C.eval.b(a, y), C.eval.b(e, y))) == C.h.if(C.decM(C.eval.b(c, y)), _, C.eval.h(C.G(e), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G(e, y) : {C.decM(C.b.if(C.eval.b(c, y), C.eval.b(a, y), C.eval.b(e, y))) == C.h.if(C.decM(C.eval.b(c, y)), C.decM(C.eval.b(a, y)), _) : Maybe<&2, C.HV>}
      L.if.G(C.eval.b(c, y), C.eval.b(a, y), C.eval.b(e, y))
    case C.BFold{z, s}:
      match y:
        case C.BvNil{}:
          P.sq.G(z, C.BvUnit{})
        case C.BvCons{hd, tl}:
          %P.sq.G(t, tl) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.b(t, tl), r => C.eval.b(s, C.BvPair{hd, r}))) == Maybe.bind(&2, C.HV, C.HV, _, r => C.eval.h(C.G(s), C.HvPair{C.dec(hd), r})) : Maybe<&2, C.HV>}
          L.bind.G(C.eval.b(t, tl), r => C.eval.b(s, C.BvPair{hd, r}), r => C.eval.h(C.G(s), C.HvPair{C.dec(hd), r}), w => P.sq.G(s, C.BvPair{hd, w}))
        case C.BvNat{n}:
          {==}
        case C.BvBool{b}:
          {==}
        case C.BvUnit{}:
          {==}
        case C.BvPair{a, b}:
          {==}
        case C.BvInl{a}:
          {==}
        case C.BvInr{b}:
          {==}
    case C.BFail{}:
      {==}

# 3. the adjunction

# an answer is no error
def L.some(m: Maybe<&2, C.BV>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def L.none.some.b(-v: C.BV, e: {None{} == Some{v} : Maybe<&2, C.BV>}) -> Empty:
  %e : L.some(_)
  Unit{}

def L.some.h(m: Maybe<&2, C.HV>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def L.none.some.h(-v: C.HV, e: {None{} == Some{v} : Maybe<&2, C.HV>}) -> Empty:
  %e : L.some.h(_)
  Unit{}

# the value inside an answer (a placeholder in an error)
def L.val.b(m: Maybe<&2, C.BV>) -> C.BV:
  match m:
    case None{}:
      C.BvUnit{}
    case Some{v}:
      v

def L.val.h(m: Maybe<&2, C.HV>) -> C.HV:
  match m:
    case None{}:
      C.HvUnit{}
    case Some{v}:
      v

# Haskell's answer at x where F's is w: w's dec
def L.encM.inj(r: Maybe<&2, C.HV>, +w: C.BV, e: {C.encM(r) == Some{w} : Maybe<&2, C.BV>}) -> {r == Some{C.dec(w)} : Maybe<&2, C.HV>}:
  match r:
    case None{}:
      Empty.absurd({None{} == Some{C.dec(w)} : Maybe<&2, C.HV>}, L.none.some.b(w, e))
    case Some{u}:
      %Equal.cong(Maybe<&2, C.BV>, C.BV, L.val.b, Some{C.enc(u)}, Some{w}, e) : {Some{u} == Some{C.dec(_)} : Maybe<&2, C.HV>}
      %Equal.sym(C.HV, C.dec(C.enc(u)), u, P.dec.enc(u)) : {Some{u} == Some{_} : Maybe<&2, C.HV>}
      {==}

def L.decM.inj(r: Maybe<&2, C.BV>, +v: C.HV, e: {C.decM(r) == Some{v} : Maybe<&2, C.HV>}) -> {r == Some{C.enc(v)} : Maybe<&2, C.BV>}:
  match r:
    case None{}:
      Empty.absurd({None{} == Some{C.enc(v)} : Maybe<&2, C.BV>}, L.none.some.h(v, e))
    case Some{u}:
      %Equal.cong(Maybe<&2, C.HV>, C.HV, L.val.h, Some{C.dec(u)}, Some{v}, e) : {Some{u} == Some{C.enc(_)} : Maybe<&2, C.BV>}
      %Equal.sym(C.BV, C.enc(C.dec(u)), u, P.enc.dec(u)) : {Some{u} == Some{_} : Maybe<&2, C.BV>}
      {==}

# F h answers h's answer, through enc
def L.F.at(+h: C.HTm, +x: C.HV, -v: C.HV, e: {C.eval.h(h, x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.b(C.F(h), C.enc(x)) == Some{C.enc(v)} : Maybe<&2, C.BV>}:
  %P.sq.F(h, x) : {_ == Some{C.enc(v)} : Maybe<&2, C.BV>}
  %Equal.sym(Maybe<&2, C.HV>, C.eval.h(h, x), Some{v}, e) : {C.encM(_) == Some{C.enc(v)} : Maybe<&2, C.BV>}
  {==}

def L.adj.l(+h: C.HTm, +b: C.BTm, le: P.Le.b(C.F(h), b), +x: C.HV, +v: C.HV, e: {C.eval.h(h, x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}:
  %P.dec.enc(x) : {C.eval.h(C.G(b), _) == Some{v} : Maybe<&2, C.HV>}
  %P.sq.G(b, C.enc(x)) : {_ == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(Maybe<&2, C.BV>, C.eval.b(b, C.enc(x)), Some{C.enc(v)}, le(C.enc(x), C.enc(v), L.F.at(h, x, v, e))) : {C.decM(_) == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(C.HV, C.dec(C.enc(v)), v, P.dec.enc(v)) : {Some{_} == Some{v} : Maybe<&2, C.HV>}
  {==}

def P.adj.FG.l(h, b, le):
  x => v => e => L.adj.l(h, b, le, x, v, e)

def L.h.at.enc(+h: C.HTm, +y: C.BV, -w: C.BV, e: {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.encM(C.eval.h(h, C.dec(y))) == Some{w} : Maybe<&2, C.BV>}:
  %e : {C.encM(C.eval.h(h, C.dec(y))) == _ : Maybe<&2, C.BV>}
  %P.enc.dec(y) : {C.encM(C.eval.h(h, C.dec(y))) == C.eval.b(C.F(h), _) : Maybe<&2, C.BV>}
  P.sq.F(h, C.dec(y))

# h answers at dec y what F h answers at y, through dec
def L.h.at(+h: C.HTm, +y: C.BV, +w: C.BV, e: {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.h(h, C.dec(y)) == Some{C.dec(w)} : Maybe<&2, C.HV>}:
  L.encM.inj(C.eval.h(h, C.dec(y)), w, L.h.at.enc(h, y, w, e))

def L.adj.r(+h: C.HTm, +b: C.BTm, le: P.Le.h(h, C.G(b)), +y: C.BV, +w: C.BV, e: {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.b(b, y) == Some{w} : Maybe<&2, C.BV>}:
  %P.enc.dec(w) : {C.eval.b(b, y) == Some{_} : Maybe<&2, C.BV>}
  L.decM.inj(C.eval.b(b, y), C.dec(w), Equal.trans(Maybe<&2, C.HV>, C.decM(C.eval.b(b, y)), C.eval.h(C.G(b), C.dec(y)), Some{C.dec(w)}, P.sq.G(b, y), le(C.dec(y), C.dec(w), L.h.at(h, y, w, e))))

def P.adj.FG.r(h, b, le):
  y => w => e => L.adj.r(h, b, le, y, w, e)

# G -| F

# G b answers b's answer, through dec
def L.G.at(+b: C.BTm, +y: C.BV, -w: C.BV, e: {C.eval.b(b, y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.h(C.G(b), C.dec(y)) == Some{C.dec(w)} : Maybe<&2, C.HV>}:
  %P.sq.G(b, y) : {_ == Some{C.dec(w)} : Maybe<&2, C.HV>}
  %Equal.sym(Maybe<&2, C.BV>, C.eval.b(b, y), Some{w}, e) : {C.decM(_) == Some{C.dec(w)} : Maybe<&2, C.HV>}
  {==}

def L.adj2.l(+h: C.HTm, +b: C.BTm, le: P.Le.h(C.G(b), h), +y: C.BV, +w: C.BV, e: {C.eval.b(b, y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}:
  %P.enc.dec(y) : {C.eval.b(C.F(h), _) == Some{w} : Maybe<&2, C.BV>}
  %P.enc.dec(w) : {C.eval.b(C.F(h), C.enc(C.dec(y))) == Some{_} : Maybe<&2, C.BV>}
  L.F.at(h, C.dec(y), C.dec(w), le(C.dec(y), C.dec(w), L.G.at(b, y, w, e)))

def P.adj.GF.l(h, b, le):
  y => w => e => L.adj2.l(h, b, le, y, w, e)

# G b's answer at x is its answer at dec (enc x)
def L.G.x(+b: C.BTm, +x: C.HV, -v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.G(b), C.dec(C.enc(x))) == Some{v} : Maybe<&2, C.HV>}:
  %Equal.sym(C.HV, C.dec(C.enc(x)), x, P.dec.enc(x)) : {C.eval.h(C.G(b), _) == Some{v} : Maybe<&2, C.HV>}
  e

# b answers at enc x what G b answers at x, through enc
def L.b.at(+b: C.BTm, +x: C.HV, +v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.b(b, C.enc(x)) == Some{C.enc(v)} : Maybe<&2, C.BV>}:
  L.decM.inj(C.eval.b(b, C.enc(x)), v, Equal.trans(Maybe<&2, C.HV>, C.decM(C.eval.b(b, C.enc(x))), C.eval.h(C.G(b), C.dec(C.enc(x))), Some{v}, P.sq.G(b, C.enc(x)), L.G.x(b, x, v, e)))

def L.adj2.r(+h: C.HTm, +b: C.BTm, le: P.Le.b(b, C.F(h)), +x: C.HV, +v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(h, x) == Some{v} : Maybe<&2, C.HV>}:
  %P.dec.enc(v) : {C.eval.h(h, x) == Some{_} : Maybe<&2, C.HV>}
  L.encM.inj(C.eval.h(h, x), C.enc(v), Equal.trans(Maybe<&2, C.BV>, C.encM(C.eval.h(h, x)), C.eval.b(C.F(h), C.enc(x)), Some{C.enc(v)}, P.sq.F(h, x), le(C.enc(x), C.enc(v), L.b.at(b, x, v, e))))

def P.adj.GF.r(h, b, le):
  x => v => e => L.adj2.r(h, b, le, x, v, e)

# 4. F.tot is no left adjoint

# h0 errs at every value
def L.h0.none(x: C.HV) -> {C.eval.h(P.h0(), x) == None{} : Maybe<&2, C.HV>}:
  match x:
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{a, b}:
      {==}
    case C.HvInl{a}:
      {==}
    case C.HvInr{b}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      {==}

def L.tot.below(+x: C.HV, -v: C.HV, e: {C.eval.h(P.h0(), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.G(P.b7()), x) == Some{v} : Maybe<&2, C.HV>}:
  Empty.absurd({C.eval.h(C.G(P.b7()), x) == Some{v} : Maybe<&2, C.HV>}, L.none.some.h(v, Equal.trans(Maybe<&2, C.HV>, None{}, C.eval.h(P.h0(), x), Some{v}, Equal.sym(Maybe<&2, C.HV>, C.eval.h(P.h0(), x), None{}, L.h0.none(x)), e)))

def P.tot.below():
  x => v => e => L.tot.below(x, v, e)

# 7 is not 0
def L.is7(m: Maybe<&2, C.BV>) -> Type:
  match m:
    case Some{C.BvNat{7n}}:
      Unit
    case _:
      Empty

def P.tot.not(le):
  %le(C.BvNat{0n}, C.BvNat{0n}, {==}) : L.is7(_)
  Unit{}
