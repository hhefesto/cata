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

# 5. Int and Integer

def L.bt(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def L.ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : L.bt(_)
  Unit{}

def L.some.z(m: Maybe<&2, C.ZV>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def L.none.some.z(-v: C.ZV, e: {None{} == Some{v} : Maybe<&2, C.ZV>}) -> Empty:
  %e : L.some.z(_)
  Unit{}

def L.and.tt(p: Bool, q: Bool, ep: {p == True{} : Bool}, eq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  match p:
    case True{}:
      eq
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.ft(ep))

def L.and.l(p: Bool, q: Bool, e: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.ft(e))

def L.and.r(p: Bool, q: Bool, e: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      e
    case False{}:
      Empty.absurd({q == True{} : Bool}, L.ft(e))

# a Natural value at Int has no negative number, and ofz gives it back
def L.nonneg.up(+x: C.HV) -> {C.nonneg(C.up(x)) == True{} : Bool}:
  match x:
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{a, b}:
      L.and.tt(C.nonneg(C.up(a)), C.nonneg(C.up(b)), L.nonneg.up(a), L.nonneg.up(b))
    case C.HvInl{a}:
      L.nonneg.up(a)
    case C.HvInr{b}:
      L.nonneg.up(b)
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      L.and.tt(C.nonneg(C.up(h)), C.nonneg(C.up(t)), L.nonneg.up(h), L.nonneg.up(t))

def L.ofz.up(x: C.HV) -> {C.ofz(C.up(x)) == x : C.HV}:
  match x:
    case C.HvNat{n}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{a, b}:
      %L.ofz.up(a) : {C.HvPair{C.ofz(C.up(a)), C.ofz(C.up(b))} == C.HvPair{_, b} : C.HV}
      %L.ofz.up(b) : {C.HvPair{C.ofz(C.up(a)), C.ofz(C.up(b))} == C.HvPair{C.ofz(C.up(a)), _} : C.HV}
      {==}
    case C.HvInl{a}:
      %L.ofz.up(a) : {C.HvInl{C.ofz(C.up(a))} == C.HvInl{_} : C.HV}
      {==}
    case C.HvInr{b}:
      %L.ofz.up(b) : {C.HvInr{C.ofz(C.up(b))} == C.HvInr{_} : C.HV}
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      %L.ofz.up(h) : {C.HvCons{C.ofz(C.up(h)), C.ofz(C.up(t))} == C.HvCons{_, t} : C.HV}
      %L.ofz.up(t) : {C.HvCons{C.ofz(C.up(h)), C.ofz(C.up(t))} == C.HvCons{C.ofz(C.up(h)), _} : C.HV}
      {==}

# fromIntegral after toInteger is the value again
def L.down.up(+x: C.HV) -> {C.down(C.up(x)) == Some{x} : Maybe<&2, C.HV>}:
  %Equal.sym(Bool, C.nonneg(C.up(x)), True{}, L.nonneg.up(x)) : {C.down.at(_, C.up(x)) == Some{x} : Maybe<&2, C.HV>}
  %Equal.sym(C.HV, C.ofz(C.up(x)), x, L.ofz.up(x)) : {Some{_} == Some{x} : Maybe<&2, C.HV>}
  {==}

# an Int value with no negative number is a Natural one's
def L.up.ofz(+z: C.ZV, +e: {C.nonneg(z) == True{} : Bool}) -> {C.up(C.ofz(z)) == z : C.ZV}:
  match z:
    case C.ZvNat{n}:
      {==}
    case C.ZvNeg{n}:
      Empty.absurd({C.up(C.ofz(C.ZvNeg{n})) == C.ZvNeg{n} : C.ZV}, L.ft(e))
    case C.ZvBool{b}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{a, b}:
      %L.up.ofz(a, L.and.l(C.nonneg(a), C.nonneg(b), e)) : {C.ZvPair{C.up(C.ofz(a)), C.up(C.ofz(b))} == C.ZvPair{_, b} : C.ZV}
      %L.up.ofz(b, L.and.r(C.nonneg(a), C.nonneg(b), e)) : {C.ZvPair{C.up(C.ofz(a)), C.up(C.ofz(b))} == C.ZvPair{C.up(C.ofz(a)), _} : C.ZV}
      {==}
    case C.ZvInl{a}:
      %L.up.ofz(a, e) : {C.ZvInl{C.up(C.ofz(a))} == C.ZvInl{_} : C.ZV}
      {==}
    case C.ZvInr{b}:
      %L.up.ofz(b, e) : {C.ZvInr{C.up(C.ofz(b))} == C.ZvInr{_} : C.ZV}
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{h, t}:
      %L.up.ofz(h, L.and.l(C.nonneg(h), C.nonneg(t), e)) : {C.ZvCons{C.up(C.ofz(h)), C.up(C.ofz(t))} == C.ZvCons{_, t} : C.ZV}
      %L.up.ofz(t, L.and.r(C.nonneg(h), C.nonneg(t), e)) : {C.ZvCons{C.up(C.ofz(h)), C.up(C.ofz(t))} == C.ZvCons{C.up(C.ofz(h)), _} : C.ZV}
      {==}

def L.downM(m: Maybe<&2, C.ZV>) -> Maybe<&2, C.HV>:
  match m:
    case None{}:
      None{}
    case Some{z}:
      C.down(z)

# an answer through toInteger is the answer's
def L.upM.inj(r: Maybe<&2, C.HV>, +v: C.HV, e: {C.upM(r) == Some{C.up(v)} : Maybe<&2, C.ZV>}) -> {r == Some{v} : Maybe<&2, C.HV>}:
  match r:
    case None{}:
      Empty.absurd({None{} == Some{v} : Maybe<&2, C.HV>}, L.none.some.z(C.up(v), e))
    case Some{u}:
      %L.down.up(u) : {_ == Some{v} : Maybe<&2, C.HV>}
      %L.down.up(v) : {C.down(C.up(u)) == _ : Maybe<&2, C.HV>}
      Equal.cong(Maybe<&2, C.ZV>, Maybe<&2, C.HV>, L.downM, Some{C.up(u)}, Some{C.up(v)}, e)

# G's program at Int, at a Natural value: G's answer there
def L.gz.at(+b: C.BTm, +x: C.HV, -v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.gz(b, C.up(x)) == Some{C.up(v)} : Maybe<&2, C.ZV>}:
  %Equal.sym(Maybe<&2, C.HV>, C.down(C.up(x)), Some{x}, L.down.up(x)) : {Maybe.bind(&2, C.HV, C.ZV, _, x2 => C.upM(C.eval.h(C.G(b), x2))) == Some{C.up(v)} : Maybe<&2, C.ZV>}
  %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.G(b), x), Some{v}, e) : {C.upM(_) == Some{C.up(v)} : Maybe<&2, C.ZV>}
  {==}

def L.int.l(+h: C.HTm, +b: C.BTm, -hz: C.ZV -> Maybe<&2, C.ZV>, ag: P.Agree(h, hz), le: P.Le.z(z => C.gz(b, z), hz), +y: C.BV, +w: C.BV, e: {C.eval.b(b, y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F(h), y) == Some{w} : Maybe<&2, C.BV>}:
  %P.enc.dec(y) : {C.eval.b(C.F(h), _) == Some{w} : Maybe<&2, C.BV>}
  %P.enc.dec(w) : {C.eval.b(C.F(h), C.enc(C.dec(y))) == Some{_} : Maybe<&2, C.BV>}
  L.F.at(h, C.dec(y), C.dec(w), L.upM.inj(C.eval.h(h, C.dec(y)), C.dec(w), Equal.trans(Maybe<&2, C.ZV>, C.upM(C.eval.h(h, C.dec(y))), hz(C.up(C.dec(y))), Some{C.up(C.dec(w))}, Equal.sym(Maybe<&2, C.ZV>, hz(C.up(C.dec(y))), C.upM(C.eval.h(h, C.dec(y))), ag(C.dec(y))), le(C.up(C.dec(y)), C.up(C.dec(w)), L.gz.at(b, C.dec(y), C.dec(w), L.G.at(b, y, w, e))))))

def P.adj.GF.int.l(h, b, hz, ag, le):
  y => w => e => L.int.l(h, b, hz, ag, le, y, w, e)

def L.int.r2(+h: C.HTm, +b: C.BTm, -hz: C.ZV -> Maybe<&2, C.ZV>, ag: P.Agree(h, hz), le: P.Le.b(b, C.F(h)), -z: C.ZV, -u: C.ZV, +x: C.HV, zx: {C.up(x) == z : C.ZV}, r: Maybe<&2, C.HV>, er: {C.eval.h(C.G(b), x) == r : Maybe<&2, C.HV>}, e: {C.upM(r) == Some{u} : Maybe<&2, C.ZV>}) -> {hz(z) == Some{u} : Maybe<&2, C.ZV>}:
  match r:
    case None{}:
      Empty.absurd({hz(z) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{v}:
      %zx : {hz(_) == Some{u} : Maybe<&2, C.ZV>}
      %e : {hz(C.up(x)) == _ : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.ZV>, hz(C.up(x)), C.upM(C.eval.h(h, x)), ag(x)) : {_ == Some{C.up(v)} : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(h, x), Some{v}, L.adj2.r(h, b, le, x, v, er)) : {C.upM(_) == Some{C.up(v)} : Maybe<&2, C.ZV>}
      {==}

def L.int.r1(+h: C.HTm, +b: C.BTm, -hz: C.ZV -> Maybe<&2, C.ZV>, ag: P.Agree(h, hz), le: P.Le.b(b, C.F(h)), +z: C.ZV, -u: C.ZV, c: Bool, ec: {C.nonneg(z) == c : Bool}, e: {Maybe.bind(&2, C.HV, C.ZV, C.down.at(c, z), x2 => C.upM(C.eval.h(C.G(b), x2))) == Some{u} : Maybe<&2, C.ZV>}) -> {hz(z) == Some{u} : Maybe<&2, C.ZV>}:
  match c:
    case False{}:
      Empty.absurd({hz(z) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case True{}:
      L.int.r2(h, b, hz, ag, le, z, u, C.ofz(z), L.up.ofz(z, ec), C.eval.h(C.G(b), C.ofz(z)), {==}, e)

def L.int.r(+h: C.HTm, +b: C.BTm, -hz: C.ZV -> Maybe<&2, C.ZV>, ag: P.Agree(h, hz), le: P.Le.b(b, C.F(h)), +z: C.ZV, -u: C.ZV, e: {C.gz(b, z) == Some{u} : Maybe<&2, C.ZV>}) -> {hz(z) == Some{u} : Maybe<&2, C.ZV>}:
  L.int.r1(h, b, hz, ag, le, z, u, C.nonneg(z), {==}, e)

def P.adj.GF.int.r(h, b, hz, ag, le):
  z => u => e => L.int.r(h, b, hz, ag, le, z, u, e)

# F -| G fails at Int: the identity at Int agrees with HId, F(HId) is BId,
# and BId's program at Int errs at -1, where the identity answers

def L.idz(z: C.ZV) -> Maybe<&2, C.ZV>:
  Some{z}

def L.idz.ag(x: C.HV) -> {L.idz(C.up(x)) == C.upM(C.eval.h(C.HId{}, x)) : Maybe<&2, C.ZV>}:
  {==}

def L.int.not(le: P.Le.z(L.idz, z => C.gz(C.BId{}, z))) -> Empty:
  L.none.some.z(C.ZvNeg{0n}, le(C.ZvNeg{0n}, C.ZvNeg{0n}, {==}))

def P.adj.FG.int.not(adj):
  L.int.not(adj(C.HId{}, C.BId{}, L.idz, x => L.idz.ag(x), y => w => e => e))

# 6. Agree, proved: h at Int against h at Natural, at a Natural value, for
# an h that never subtracts; a lemma for each construct, as the squares

# a primitive at two numbers, but (-)
def L.z.at(+p: C.Prim, ep: {C.p.nosub(p) == True{} : Bool}, +a: Nat, +b: Nat) -> {C.upM(C.h.pv(C.p.at(p, a, b))) == C.z.at(p, C.ZvNat{a}, C.ZvNat{b}) : Maybe<&2, C.ZV>}:
  match p:
    case C.PAdd{}:
      {==}
    case C.PLt{}:
      {==}
    case C.PSub{}:
      Empty.absurd({C.upM(C.h.pv(C.p.at(C.PSub{}, a, b))) == C.z.at(C.PSub{}, C.ZvNat{a}, C.ZvNat{b}) : Maybe<&2, C.ZV>}, L.ft(ep))
    case C.PDiv{}:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case C.PMod{}:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case C.PSubT{}:
      {==}
    case C.PDivT{}:
      {==}
    case C.PModT{}:
      {==}

# a primitive, at any value
def L.z.prim(+p: C.Prim, +ep: {C.p.nosub(p) == True{} : Bool}, x: C.HV) -> {C.upM(C.h.prim(p, x)) == C.z.prim(p, C.up(x)) : Maybe<&2, C.ZV>}:
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
    case C.HvPair{u, w}:
      match u:
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
          match w:
            case C.HvNat{b}:
              L.z.at(p, ep, a, b)
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

def L.z.fst(x: C.HV) -> {C.upM(C.h.fst(x)) == C.z.fst(C.up(x)) : Maybe<&2, C.ZV>}:
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

def L.z.snd(x: C.HV) -> {C.upM(C.h.snd(x)) == C.z.snd(C.up(x)) : Maybe<&2, C.ZV>}:
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

def L.z.pair(r: Maybe<&2, C.HV>, s: Maybe<&2, C.HV>) -> {C.upM(C.h.pair(r, s)) == C.z.pair(C.upM(r), C.upM(s)) : Maybe<&2, C.ZV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.z.if(c: Maybe<&2, C.HV>, a: Maybe<&2, C.HV>, e: Maybe<&2, C.HV>) -> {C.upM(C.h.if(c, a, e)) == C.z.if(C.upM(c), C.upM(a), C.upM(e)) : Maybe<&2, C.ZV>}:
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

def L.z.bind(r: Maybe<&2, C.HV>, -kh: C.HV -> Maybe<&2, C.HV>, -kz: C.ZV -> Maybe<&2, C.ZV>, ih: @v: C.HV -> {C.upM(kh(v)) == kz(C.up(v)) : Maybe<&2, C.ZV>}) -> {C.upM(Maybe.bind(&2, C.HV, C.HV, r, kh)) == Maybe.bind(&2, C.ZV, C.ZV, C.upM(r), kz) : Maybe<&2, C.ZV>}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      ih(v)

# h at Natural, through toInteger, is h at Int at a Natural value, by
# induction on h (and, at a fold, on the list)
def L.agree(+t: C.HTm, +e: {C.nosub(t) == True{} : Bool}, +x: C.HV) -> {C.upM(C.eval.h(t, x)) == C.eval.z(t, C.up(x)) : Maybe<&2, C.ZV>}:
  match t:
    case C.HId{}:
      {==}
    case C.HComp{g, f}:
      %L.agree(f, L.and.r(C.nosub(g), C.nosub(f), e), x) : {C.upM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(f, x), y => C.eval.h(g, y))) == Maybe.bind(&2, C.ZV, C.ZV, _, w => C.eval.z(g, w)) : Maybe<&2, C.ZV>}
      L.z.bind(C.eval.h(f, x), y => C.eval.h(g, y), w => C.eval.z(g, w), v => L.agree(g, L.and.l(C.nosub(g), C.nosub(f), e), v))
    case C.HFst{}:
      L.z.fst(x)
    case C.HSnd{}:
      L.z.snd(x)
    case C.HPr{f, g}:
      %L.agree(f, L.and.l(C.nosub(f), C.nosub(g), e), x) : {C.upM(C.h.pair(C.eval.h(f, x), C.eval.h(g, x))) == C.z.pair(_, C.eval.z(g, C.up(x))) : Maybe<&2, C.ZV>}
      %L.agree(g, L.and.r(C.nosub(f), C.nosub(g), e), x) : {C.upM(C.h.pair(C.eval.h(f, x), C.eval.h(g, x))) == C.z.pair(C.upM(C.eval.h(f, x)), _) : Maybe<&2, C.ZV>}
      L.z.pair(C.eval.h(f, x), C.eval.h(g, x))
    case C.HInl{}:
      {==}
    case C.HInr{}:
      {==}
    case C.HCase{f, g}:
      match x:
        case C.HvInl{a}:
          L.agree(f, L.and.l(C.nosub(f), C.nosub(g), e), a)
        case C.HvInr{b}:
          L.agree(g, L.and.r(C.nosub(f), C.nosub(g), e), b)
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
      L.z.prim(p, e, x)
    case C.HIf{c, a, d}:
      %L.agree(c, L.and.l(C.nosub(c), Bool.and(C.nosub(a), C.nosub(d)), e), x) : {C.upM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(d, x))) == C.z.if(_, C.eval.z(a, C.up(x)), C.eval.z(d, C.up(x))) : Maybe<&2, C.ZV>}
      %L.agree(a, L.and.l(C.nosub(a), C.nosub(d), L.and.r(C.nosub(c), Bool.and(C.nosub(a), C.nosub(d)), e)), x) : {C.upM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(d, x))) == C.z.if(C.upM(C.eval.h(c, x)), _, C.eval.z(d, C.up(x))) : Maybe<&2, C.ZV>}
      %L.agree(d, L.and.r(C.nosub(a), C.nosub(d), L.and.r(C.nosub(c), Bool.and(C.nosub(a), C.nosub(d)), e)), x) : {C.upM(C.h.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(d, x))) == C.z.if(C.upM(C.eval.h(c, x)), C.upM(C.eval.h(a, x)), _) : Maybe<&2, C.ZV>}
      L.z.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(d, x))
    case C.HFold{z, s}:
      match x:
        case C.HvNil{}:
          L.agree(z, L.and.l(C.nosub(z), C.nosub(s), e), C.HvUnit{})
        case C.HvCons{hd, tl}:
          %L.agree(t, e, tl) : {C.upM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, tl), r => C.eval.h(s, C.HvPair{hd, r}))) == Maybe.bind(&2, C.ZV, C.ZV, _, r => C.eval.z(s, C.ZvPair{C.up(hd), r})) : Maybe<&2, C.ZV>}
          L.z.bind(C.eval.h(t, tl), r => C.eval.h(s, C.HvPair{hd, r}), r => C.eval.z(s, C.ZvPair{C.up(hd), r}), v => L.agree(s, L.and.r(C.nosub(z), C.nosub(s), e), C.HvPair{hd, v}))
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

def P.agree(h, e):
  x => Equal.sym(Maybe<&2, C.ZV>, C.upM(C.eval.h(h, x)), C.eval.z(h, C.up(x)), L.agree(h, e, x))

# x - y at (0, 1): -1 at Int, an error at Natural
def L.sub.at() -> C.HV:
  C.HvPair{C.HvNat{0n}, C.HvNat{1n}}

def P.agree.sub.not(ag):
  L.none.some.z(C.ZvNeg{0n}, Equal.sym(Maybe<&2, C.ZV>, Some{C.ZvNeg{0n}}, None{}, ag(L.sub.at())))

def P.adj.GF.nosub.l(h, b, e, le):
  y => w => ex => L.int.l(h, b, z => C.eval.z(h, z), P.agree(h, e), le, y, w, ex)

def P.adj.GF.nosub.r(h, b, e, le):
  z => u => ex => L.int.r(h, b, z2 => C.eval.z(h, z2), P.agree(h, e), le, z, u, ex)

# 7. General recursion, with fuel

# n <= n
def L.le.refl(n: Nat) -> {C.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+i:
      L.le.refl(i)

# a Haskell run and a Bend answer agree: where the run ended, its answer
# through enc
def L.agR(r: C.Run, m: Maybe<&2, C.BV>) -> Type:
  match r:
    case C.ROut{}:
      Unit
    case C.RDone{a}:
      {C.encM(a) == m : Maybe<&2, C.BV>}

# Bend's fuelled def with fuel n agrees with Haskell's run of k <= n steps
# (c and m: p's and s's answers at x), by induction on k
def L.run.F(k: Nat, n: Nat, +p: C.HTm, +s: C.HTm, +d: C.BV, +x: C.HV, c: Maybe<&2, C.HV>, m: Maybe<&2, C.HV>, le: {C.le(k, n) == True{} : Bool}) -> L.agR(C.run.h(k, p, s, x, c, m), C.run.b(n, C.F(p), C.F(s), d, C.enc(x), C.encM(c), C.encM(m))):
  match k n:
    case 0n _:
      Unit{}
    case 1n+j 0n:
      Empty.absurd(L.agR(C.run.h(1n+j, p, s, x, c, m), C.run.b(0n, C.F(p), C.F(s), d, C.enc(x), C.encM(c), C.encM(m))), L.ft(le))
    case 1n+j 1n+i:
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
                  match m:
                    case None{}:
                      {==}
                    case Some{+y}:
                      %P.sq.F(p, y) : L.agR(C.run.h(j, p, s, y, C.eval.h(p, y), C.eval.h(s, y)), C.run.b(i, C.F(p), C.F(s), d, C.enc(y), _, C.eval.b(C.F(s), C.enc(y))))
                      %P.sq.F(s, y) : L.agR(C.run.h(j, p, s, y, C.eval.h(p, y), C.eval.h(s, y)), C.run.b(i, C.F(p), C.F(s), d, C.enc(y), C.encM(C.eval.h(p, y)), _))
                      L.run.F(j, i, p, s, d, y, C.eval.h(p, y), C.eval.h(s, y), le)
            case C.HvNat{q}:
              {==}
            case C.HvUnit{}:
              {==}
            case C.HvPair{a, a2}:
              {==}
            case C.HvInl{a}:
              {==}
            case C.HvInr{a}:
              {==}
            case C.HvNil{}:
              {==}
            case C.HvCons{a, a2}:
              {==}

# where a run ended with r: r's answer through enc
def L.agR.done(R: C.Run, -mm: Maybe<&2, C.BV>, -r: Maybe<&2, C.HV>, e: {R == C.RDone{r} : C.Run}, a: L.agR(R, mm)) -> {C.encM(r) == mm : Maybe<&2, C.BV>}:
  %e : L.agR(_, mm)
  a

def P.sq.F.l(k, n, h, x, r, e, le):
  match h:
    case C.HUntil{p, s}:
      %P.sq.F(p, x) : {C.run.b(n, C.F(p), C.F(s), C.BvNat{0n}, C.enc(x), _, C.eval.b(C.F(s), C.enc(x))) == C.encM(r) : Maybe<&2, C.BV>}
      %P.sq.F(s, x) : {C.run.b(n, C.F(p), C.F(s), C.BvNat{0n}, C.enc(x), C.encM(C.eval.h(p, x)), _) == C.encM(r) : Maybe<&2, C.BV>}
      Equal.sym(Maybe<&2, C.BV>, C.encM(r), C.run.b(n, C.F(p), C.F(s), C.BvNat{0n}, C.enc(x), C.encM(C.eval.h(p, x)), C.encM(C.eval.h(s, x))), L.agR.done(C.run.h(k, p, s, x, C.eval.h(p, x), C.eval.h(s, x)), C.run.b(n, C.F(p), C.F(s), C.BvNat{0n}, C.enc(x), C.encM(C.eval.h(p, x)), C.encM(C.eval.h(s, x))), r, e, L.run.F(k, n, p, s, C.BvNat{0n}, x, C.eval.h(p, x), C.eval.h(s, x), le)))

# G's Haskell for a fuelled def means what it means, by induction on the
# fuel
def L.run.G(n: Nat, +p: C.BTm, +s: C.BTm, +d: C.BV, +y: C.BV, c: Maybe<&2, C.BV>, m: Maybe<&2, C.BV>) -> {C.decM(C.run.b(n, p, s, d, y, c, m)) == C.run.g(n, C.G(p), C.G(s), C.dec(d), C.dec(y), C.decM(c), C.decM(m)) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
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
                  match m:
                    case None{}:
                      {==}
                    case Some{+z}:
                      %P.sq.G(p, z) : {C.decM(C.run.b(j, p, s, d, z, C.eval.b(p, z), C.eval.b(s, z))) == C.run.g(j, C.G(p), C.G(s), C.dec(d), C.dec(z), _, C.eval.h(C.G(s), C.dec(z))) : Maybe<&2, C.HV>}
                      %P.sq.G(s, z) : {C.decM(C.run.b(j, p, s, d, z, C.eval.b(p, z), C.eval.b(s, z))) == C.run.g(j, C.G(p), C.G(s), C.dec(d), C.dec(z), C.decM(C.eval.b(p, z)), _) : Maybe<&2, C.HV>}
                      L.run.G(j, p, s, d, z, C.eval.b(p, z), C.eval.b(s, z))
            case C.BvNat{q}:
              {==}
            case C.BvUnit{}:
              {==}
            case C.BvPair{a, a2}:
              {==}
            case C.BvInl{a}:
              {==}
            case C.BvInr{a}:
              {==}
            case C.BvNil{}:
              {==}
            case C.BvCons{a, a2}:
              {==}

def P.sq.G.l(b, y):
  match b:
    case C.BLoop{n, p, s, d}:
      %P.sq.G(p, y) : {C.decM(C.run.b(n, p, s, d, y, C.eval.b(p, y), C.eval.b(s, y))) == C.run.g(n, C.G(p), C.G(s), C.dec(d), C.dec(y), _, C.eval.h(C.G(s), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G(s, y) : {C.decM(C.run.b(n, p, s, d, y, C.eval.b(p, y), C.eval.b(s, y))) == C.run.g(n, C.G(p), C.G(s), C.dec(d), C.dec(y), C.decM(C.eval.b(p, y)), _) : Maybe<&2, C.HV>}
      L.run.G(n, p, s, d, y, C.eval.b(p, y), C.eval.b(s, y))

# a run is deterministic: two runs that both end end alike, by induction
# on the steps
def L.agHH(r1: C.Run, r2: C.Run) -> Type:
  match r1:
    case C.ROut{}:
      Unit
    case C.RDone{a}:
      match r2:
        case C.ROut{}:
          Unit
        case C.RDone{a2}:
          {a == a2 : Maybe<&2, C.HV>}

def L.run.det(k: Nat, k2: Nat, +p: C.HTm, +s: C.HTm, +x: C.HV, c: Maybe<&2, C.HV>, m: Maybe<&2, C.HV>) -> L.agHH(C.run.h(k, p, s, x, c, m), C.run.h(k2, p, s, x, c, m)):
  match k k2:
    case 0n _:
      Unit{}
    case 1n+j 0n:
      match c:
        case None{}:
          Unit{}
        case Some{v}:
          match v:
            case C.HvBool{b}:
              match b:
                case True{}:
                  Unit{}
                case False{}:
                  match m:
                    case None{}:
                      Unit{}
                    case Some{+y}:
                      L.run.det(j, 0n, p, s, y, C.eval.h(p, y), C.eval.h(s, y))
            case C.HvNat{q}:
              Unit{}
            case C.HvUnit{}:
              Unit{}
            case C.HvPair{a, a2}:
              Unit{}
            case C.HvInl{a}:
              Unit{}
            case C.HvInr{a}:
              Unit{}
            case C.HvNil{}:
              Unit{}
            case C.HvCons{a, a2}:
              Unit{}
    case 1n+j 1n+i:
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
                  match m:
                    case None{}:
                      {==}
                    case Some{+y}:
                      L.run.det(j, i, p, s, y, C.eval.h(p, y), C.eval.h(s, y))
            case C.HvNat{q}:
              {==}
            case C.HvUnit{}:
              {==}
            case C.HvPair{a, a2}:
              {==}
            case C.HvInl{a}:
              {==}
            case C.HvInr{a}:
              {==}
            case C.HvNil{}:
              {==}
            case C.HvCons{a, a2}:
              {==}

def L.hl.det(k: Nat, k2: Nat, h: C.HL, +x: C.HV) -> L.agHH(C.eval.hl(k, h, x), C.eval.hl(k2, h, x)):
  match h:
    case C.HUntil{+p, +s}:
      L.run.det(k, k2, p, s, x, C.eval.h(p, x), C.eval.h(s, x))

def L.agHH.at(R1: C.Run, R2: C.Run, -a1: Maybe<&2, C.HV>, -a2: Maybe<&2, C.HV>, e1: {R1 == C.RDone{a1} : C.Run}, e2: {R2 == C.RDone{a2} : C.Run}, d: L.agHH(R1, R2)) -> {a1 == a2 : Maybe<&2, C.HV>}:
  %e2 : L.agHH(C.RDone{a1}, _)
  %e1 : L.agHH(_, R2)
  d

# F -| G on loops that stop within the fuel

# F's def answers h's answer, through enc, where h ends within its fuel
def L.loop.F.at(+n: Nat, +h: C.HL, +x: C.HV, -v: C.HV, -a: Maybe<&2, C.HV>, eR: {C.eval.hl(n, h, x) == C.RDone{a} : C.Run}, ea: {a == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.bl(C.F.ln(n, h), C.enc(x)) == Some{C.enc(v)} : Maybe<&2, C.BV>}:
  %ea : {C.eval.bl(C.F.ln(n, h), C.enc(x)) == C.encM(_) : Maybe<&2, C.BV>}
  P.sq.F.l(n, n, h, x, a, eR, L.le.refl(n))

def L.loop.l(+n: Nat, +h: C.HL, +b: C.BL, le: P.Le.bl(C.F.ln(n, h), b), +x: C.HV, +v: C.HV, -a: Maybe<&2, C.HV>, eR: {C.eval.hl(n, h, x) == C.RDone{a} : C.Run}, ea: {a == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.gl(C.G.l(b), x) == Some{v} : Maybe<&2, C.HV>}:
  %P.dec.enc(x) : {C.eval.gl(C.G.l(b), _) == Some{v} : Maybe<&2, C.HV>}
  %P.sq.G.l(b, C.enc(x)) : {_ == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(Maybe<&2, C.BV>, C.eval.bl(b, C.enc(x)), Some{C.enc(v)}, le(C.enc(x), C.enc(v), L.loop.F.at(n, h, x, v, a, eR, ea))) : {C.decM(_) == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(C.HV, C.dec(C.enc(v)), v, P.dec.enc(v)) : {Some{_} == Some{v} : Maybe<&2, C.HV>}
  {==}

# h's run of n steps at x, R: it ends (Stops), so with h's answer
def L.loop.l.at(+n: Nat, +h: C.HL, +b: C.BL, st: P.Stops(h, n), le: P.Le.bl(C.F.ln(n, h), b), +x: C.HV, +v: C.HV, +k: Nat, e: {C.eval.hl(k, h, x) == C.RDone{Some{v}} : C.Run}, R: C.Run, +eR: {C.eval.hl(n, h, x) == R : C.Run}) -> {C.eval.gl(C.G.l(b), x) == Some{v} : Maybe<&2, C.HV>}:
  match R:
    case C.ROut{}:
      Empty.absurd({C.eval.gl(C.G.l(b), x) == Some{v} : Maybe<&2, C.HV>}, st(x, eR))
    case C.RDone{a}:
      L.loop.l(n, h, b, le, x, v, a, eR, L.agHH.at(C.eval.hl(n, h, x), C.eval.hl(k, h, x), a, Some{v}, eR, e, L.hl.det(n, k, h, x)))

def L.loop.l.go(+n: Nat, +h: C.HL, +b: C.BL, st: P.Stops(h, n), le: P.Le.bl(C.F.ln(n, h), b), +x: C.HV, +v: C.HV, +k: Nat, e: {C.eval.hl(k, h, x) == C.RDone{Some{v}} : C.Run}) -> {C.eval.gl(C.G.l(b), x) == Some{v} : Maybe<&2, C.HV>}:
  L.loop.l.at(n, h, b, st, le, x, v, k, e, C.eval.hl(n, h, x), {==})

def P.adj.FG.loop.l(n, h, b, st, le):
  x => v => k => e => L.loop.l.go(n, h, b, st, le, x, v, k, e)

# h's answer at dec y, where F's def answers w at y
def L.loop.sqy(+n: Nat, +h: C.HL, +y: C.BV, -a: Maybe<&2, C.HV>, eR: {C.eval.hl(n, h, C.dec(y)) == C.RDone{a} : C.Run}) -> {C.encM(a) == C.eval.bl(C.F.ln(n, h), y) : Maybe<&2, C.BV>}:
  %P.enc.dec(y) : {C.encM(a) == C.eval.bl(C.F.ln(n, h), _) : Maybe<&2, C.BV>}
  Equal.sym(Maybe<&2, C.BV>, C.eval.bl(C.F.ln(n, h), C.enc(C.dec(y))), C.encM(a), P.sq.F.l(n, n, h, C.dec(y), a, eR, L.le.refl(n)))

def L.loop.eR(+n: Nat, +h: C.HL, +y: C.BV, +w: C.BV, +a: Maybe<&2, C.HV>, +eR: {C.eval.hl(n, h, C.dec(y)) == C.RDone{a} : C.Run}, e: {C.eval.bl(C.F.ln(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.hl(n, h, C.dec(y)) == C.RDone{Some{C.dec(w)}} : C.Run}:
  %L.encM.inj(a, w, Equal.trans(Maybe<&2, C.BV>, C.encM(a), C.eval.bl(C.F.ln(n, h), y), Some{w}, L.loop.sqy(n, h, y, a, eR), e)) : {C.eval.hl(n, h, C.dec(y)) == C.RDone{_} : C.Run}
  eR

def L.loop.r(+n: Nat, +h: C.HL, +b: C.BL, le: P.Le.hl(h, C.G.l(b)), +y: C.BV, +w: C.BV, a: Maybe<&2, C.HV>, eR: {C.eval.hl(n, h, C.dec(y)) == C.RDone{a} : C.Run}, e: {C.eval.bl(C.F.ln(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.bl(b, y) == Some{w} : Maybe<&2, C.BV>}:
  %P.enc.dec(w) : {C.eval.bl(b, y) == Some{_} : Maybe<&2, C.BV>}
  L.decM.inj(C.eval.bl(b, y), C.dec(w), Equal.trans(Maybe<&2, C.HV>, C.decM(C.eval.bl(b, y)), C.eval.gl(C.G.l(b), C.dec(y)), Some{C.dec(w)}, P.sq.G.l(b, y), le(C.dec(y), C.dec(w), n, L.loop.eR(n, h, y, w, a, eR, e))))

def L.loop.r.at(+n: Nat, +h: C.HL, +b: C.BL, st: P.Stops(h, n), le: P.Le.hl(h, C.G.l(b)), +y: C.BV, +w: C.BV, e: {C.eval.bl(C.F.ln(n, h), y) == Some{w} : Maybe<&2, C.BV>}, R: C.Run, eR: {C.eval.hl(n, h, C.dec(y)) == R : C.Run}) -> {C.eval.bl(b, y) == Some{w} : Maybe<&2, C.BV>}:
  match R:
    case C.ROut{}:
      Empty.absurd({C.eval.bl(b, y) == Some{w} : Maybe<&2, C.BV>}, st(C.dec(y), eR))
    case C.RDone{a}:
      L.loop.r(n, h, b, le, y, w, a, eR, e)

def L.loop.r.go(+n: Nat, +h: C.HL, +b: C.BL, st: P.Stops(h, n), le: P.Le.hl(h, C.G.l(b)), +y: C.BV, +w: C.BV, e: {C.eval.bl(C.F.ln(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.bl(b, y) == Some{w} : Maybe<&2, C.BV>}:
  L.loop.r.at(n, h, b, st, le, y, w, e, C.eval.hl(n, h, C.dec(y)), {==})

def P.adj.FG.loop.r(n, h, b, st, le):
  y => w => e => L.loop.r.go(n, h, b, st, le, y, w, e)

def P.adj.FG.fuel.l(h, b, st, le):
  P.adj.FG.loop.l(C.fuel(), h, b, st, le)

def P.adj.FG.fuel.r(h, b, st, le):
  P.adj.FG.loop.r(C.fuel(), h, b, st, le)

# a loop that never stops: hn's test, 0 < 0, is False at every x, and its
# step is the identity
def L.p0() -> C.HTm:
  C.HComp{C.HPrim{C.PLt{}}, C.HPr{C.HLit{0n}, C.HLit{0n}}}

def L.never(k: Nat, +x: C.HV) -> {C.run.h(k, L.p0(), C.HId{}, x, Some{C.HvBool{False{}}}, Some{x}) == C.ROut{} : C.Run}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.never(j, x)

def P.loop.never(k, x):
  L.never(k, x)

# F's def of it answers the default, 0, at 0: its fuel runs out
def L.default(n: Nat) -> {C.run.b(n, C.F(L.p0()), C.BId{}, C.BvNat{0n}, C.BvNat{0n}, Some{C.BvBool{False{}}}, Some{C.BvNat{0n}}) == Some{C.BvNat{0n}} : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      L.default(j)

def P.loop.default(n):
  L.default(n)

# a run that never ends is no answer
def L.isout(r: C.Run) -> Type:
  match r:
    case C.ROut{}:
      Unit
    case C.RDone{a}:
      Empty

def L.out.done(-a: Maybe<&2, C.HV>, e: {C.ROut{} == C.RDone{a} : C.Run}) -> Empty:
  %e : L.isout(_)
  Unit{}

# so every G b implements hn
def L.never.le(+x: C.HV, -v: C.HV, +k: Nat, e: {C.eval.hl(k, P.hn(), x) == C.RDone{Some{v}} : C.Run}) -> {C.eval.gl(C.G.l(P.bn7()), x) == Some{v} : Maybe<&2, C.HV>}:
  Empty.absurd({C.eval.gl(C.G.l(P.bn7()), x) == Some{v} : Maybe<&2, C.HV>}, L.out.done(Some{v}, Equal.trans(C.Run, C.ROut{}, C.eval.hl(k, P.hn(), x), C.RDone{Some{v}}, Equal.sym(C.Run, C.eval.hl(k, P.hn(), x), C.ROut{}, P.loop.never(k, x)), e)))

# and F's def of hn answers 0 at 0, where bn7 answers 7
def P.adj.FG.loop.not(n, adj):
  %adj(P.hn(), P.bn7(), x => v => k => e => L.never.le(x, v, k, e), C.BvNat{0n}, C.BvNat{0n}, P.loop.default(n)) : L.is7(_)
  Unit{}
