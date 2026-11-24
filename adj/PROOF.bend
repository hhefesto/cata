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

def P.F.unit():
  {==}

def P.F.nil():
  {==}

def P.F.cons(a, b):
  {==}

def P.F.dist():
  {==}

def P.F.foldE(z, s):
  {==}

def P.F.cata(s):
  {==}

def P.G.id():
  {==}

def P.G.comp(g, f):
  {==}

def P.G.fold(z, s):
  {==}

def P.G.cons(a, b):
  {==}

def P.G.foldE(z, s):
  {==}

def P.G.cata(s):
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

def L.cons.F(r: Maybe<&2, C.HV>, s: Maybe<&2, C.HV>) -> {C.encM(C.h.cons(r, s)) == C.b.cons(C.encM(r), C.encM(s)) : Maybe<&2, C.BV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.dist.F(x: C.HV) -> {C.encM(C.h.dist(x)) == C.b.dist(C.enc(x)) : Maybe<&2, C.BV>}:
  match x:
    case C.HvPair{e, q}:
      match q:
        case C.HvInl{a}:
          {==}
        case C.HvInr{b}:
          {==}
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
        case C.HvCons{h, t}:
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
    case C.HUnit{}:
      {==}
    case C.HNil{}:
      {==}
    case C.HCons{a, b}:
      %P.sq.F(a, x) : {C.encM(C.h.cons(C.eval.h(a, x), C.eval.h(b, x))) == C.b.cons(_, C.eval.b(C.F(b), C.enc(x))) : Maybe<&2, C.BV>}
      %P.sq.F(b, x) : {C.encM(C.h.cons(C.eval.h(a, x), C.eval.h(b, x))) == C.b.cons(C.encM(C.eval.h(a, x)), _) : Maybe<&2, C.BV>}
      L.cons.F(C.eval.h(a, x), C.eval.h(b, x))
    case C.HDist{}:
      L.dist.F(x)
    case C.HFoldE{z, s}:
      match x:
        case C.HvPair{+e, l}:
          match l:
            case C.HvNil{}:
              P.sq.F(z, e)
            case C.HvCons{hd, tl}:
              %P.sq.F(t, C.HvPair{e, tl}) : {C.encM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, C.HvPair{e, tl}), r => C.eval.h(s, C.HvPair{e, C.HvPair{hd, r}}))) == Maybe.bind(&2, C.BV, C.BV, _, r => C.eval.b(C.F(s), C.BvPair{C.enc(e), C.BvPair{C.enc(hd), r}})) : Maybe<&2, C.BV>}
              L.bind.F(C.eval.h(t, C.HvPair{e, tl}), r => C.eval.h(s, C.HvPair{e, C.HvPair{hd, r}}), r => C.eval.b(C.F(s), C.BvPair{C.enc(e), C.BvPair{C.enc(hd), r}}), v => P.sq.F(s, C.HvPair{e, C.HvPair{hd, v}}))
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
        case C.HvCons{hd, tl}:
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
    case C.HErr{}:
      {==}
    case C.HCata{s}:
      match x:
        case C.HvPair{sh, ks}:
          %P.sq.F(t, ks) : {C.encM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, ks), rs => C.eval.h(s, C.HvPair{sh, rs}))) == Maybe.bind(&2, C.BV, C.BV, _, rs => C.eval.b(C.F(s), C.BvPair{C.enc(sh), rs})) : Maybe<&2, C.BV>}
          L.bind.F(C.eval.h(t, ks), rs => C.eval.h(s, C.HvPair{sh, rs}), rs => C.eval.b(C.F(s), C.BvPair{C.enc(sh), rs}), v => P.sq.F(s, C.HvPair{sh, v}))
        case C.HvNil{}:
          {==}
        case C.HvCons{k, ks}:
          %P.sq.F(t, k) : {C.encM(C.h.cons(C.eval.h(t, k), C.eval.h(t, ks))) == C.b.cons(_, C.eval.b(C.F(t), C.enc(ks))) : Maybe<&2, C.BV>}
          %P.sq.F(t, ks) : {C.encM(C.h.cons(C.eval.h(t, k), C.eval.h(t, ks))) == C.b.cons(C.encM(C.eval.h(t, k)), _) : Maybe<&2, C.BV>}
          L.cons.F(C.eval.h(t, k), C.eval.h(t, ks))
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

def L.cons.G(r: Maybe<&2, C.BV>, s: Maybe<&2, C.BV>) -> {C.decM(C.b.cons(r, s)) == C.h.cons(C.decM(r), C.decM(s)) : Maybe<&2, C.HV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.dist.G(y: C.BV) -> {C.decM(C.b.dist(y)) == C.h.dist(C.dec(y)) : Maybe<&2, C.HV>}:
  match y:
    case C.BvPair{e, q}:
      match q:
        case C.BvInl{a}:
          {==}
        case C.BvInr{b}:
          {==}
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
        case C.BvCons{h, t}:
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
    case C.BUnit{}:
      {==}
    case C.BNil{}:
      {==}
    case C.BCons{a, b}:
      %P.sq.G(a, y) : {C.decM(C.b.cons(C.eval.b(a, y), C.eval.b(b, y))) == C.h.cons(_, C.eval.h(C.G(b), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G(b, y) : {C.decM(C.b.cons(C.eval.b(a, y), C.eval.b(b, y))) == C.h.cons(C.decM(C.eval.b(a, y)), _) : Maybe<&2, C.HV>}
      L.cons.G(C.eval.b(a, y), C.eval.b(b, y))
    case C.BDist{}:
      L.dist.G(y)
    case C.BFoldE{z, s}:
      match y:
        case C.BvPair{+e, l}:
          match l:
            case C.BvNil{}:
              P.sq.G(z, e)
            case C.BvCons{hd, tl}:
              %P.sq.G(t, C.BvPair{e, tl}) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.b(t, C.BvPair{e, tl}), r => C.eval.b(s, C.BvPair{e, C.BvPair{hd, r}}))) == Maybe.bind(&2, C.HV, C.HV, _, r => C.eval.h(C.G(s), C.HvPair{C.dec(e), C.HvPair{C.dec(hd), r}})) : Maybe<&2, C.HV>}
              L.bind.G(C.eval.b(t, C.BvPair{e, tl}), r => C.eval.b(s, C.BvPair{e, C.BvPair{hd, r}}), r => C.eval.h(C.G(s), C.HvPair{C.dec(e), C.HvPair{C.dec(hd), r}}), w => P.sq.G(s, C.BvPair{e, C.BvPair{hd, w}}))
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
        case C.BvNil{}:
          {==}
        case C.BvCons{hd, tl}:
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
    case C.BFail{}:
      {==}
    case C.BCata{s}:
      match y:
        case C.BvPair{sh, ks}:
          %P.sq.G(t, ks) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.b(t, ks), rs => C.eval.b(s, C.BvPair{sh, rs}))) == Maybe.bind(&2, C.HV, C.HV, _, rs => C.eval.h(C.G(s), C.HvPair{C.dec(sh), rs})) : Maybe<&2, C.HV>}
          L.bind.G(C.eval.b(t, ks), rs => C.eval.b(s, C.BvPair{sh, rs}), rs => C.eval.h(C.G(s), C.HvPair{C.dec(sh), rs}), w => P.sq.G(s, C.BvPair{sh, w}))
        case C.BvNil{}:
          {==}
        case C.BvCons{k, ks}:
          %P.sq.G(t, k) : {C.decM(C.b.cons(C.eval.b(t, k), C.eval.b(t, ks))) == C.h.cons(_, C.eval.h(C.G(t), C.dec(ks))) : Maybe<&2, C.HV>}
          %P.sq.G(t, ks) : {C.decM(C.b.cons(C.eval.b(t, k), C.eval.b(t, ks))) == C.h.cons(C.decM(C.eval.b(t, k)), _) : Maybe<&2, C.HV>}
          L.cons.G(C.eval.b(t, k), C.eval.b(t, ks))
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

def L.z.cons(r: Maybe<&2, C.HV>, s: Maybe<&2, C.HV>) -> {C.upM(C.h.cons(r, s)) == C.z.cons(C.upM(r), C.upM(s)) : Maybe<&2, C.ZV>}:
  match r s:
    case Some{u} Some{v}:
      {==}
    case Some{u} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case None{} None{}:
      {==}

def L.z.dist(x: C.HV) -> {C.upM(C.h.dist(x)) == C.z.dist(C.up(x)) : Maybe<&2, C.ZV>}:
  match x:
    case C.HvPair{e, q}:
      match q:
        case C.HvInl{a}:
          {==}
        case C.HvInr{b}:
          {==}
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
        case C.HvCons{h, t}:
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
    case C.HUnit{}:
      {==}
    case C.HNil{}:
      {==}
    case C.HCons{a, b}:
      %L.agree(a, L.and.l(C.nosub(a), C.nosub(b), e), x) : {C.upM(C.h.cons(C.eval.h(a, x), C.eval.h(b, x))) == C.z.cons(_, C.eval.z(b, C.up(x))) : Maybe<&2, C.ZV>}
      %L.agree(b, L.and.r(C.nosub(a), C.nosub(b), e), x) : {C.upM(C.h.cons(C.eval.h(a, x), C.eval.h(b, x))) == C.z.cons(C.upM(C.eval.h(a, x)), _) : Maybe<&2, C.ZV>}
      L.z.cons(C.eval.h(a, x), C.eval.h(b, x))
    case C.HDist{}:
      L.z.dist(x)
    case C.HFoldE{z, s}:
      match x:
        case C.HvPair{+v, l}:
          match l:
            case C.HvNil{}:
              L.agree(z, L.and.l(C.nosub(z), C.nosub(s), e), v)
            case C.HvCons{hd, tl}:
              %L.agree(t, e, C.HvPair{v, tl}) : {C.upM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, C.HvPair{v, tl}), r => C.eval.h(s, C.HvPair{v, C.HvPair{hd, r}}))) == Maybe.bind(&2, C.ZV, C.ZV, _, r => C.eval.z(s, C.ZvPair{C.up(v), C.ZvPair{C.up(hd), r}})) : Maybe<&2, C.ZV>}
              L.z.bind(C.eval.h(t, C.HvPair{v, tl}), r => C.eval.h(s, C.HvPair{v, C.HvPair{hd, r}}), r => C.eval.z(s, C.ZvPair{C.up(v), C.ZvPair{C.up(hd), r}}), w => L.agree(s, L.and.r(C.nosub(z), C.nosub(s), e), C.HvPair{v, C.HvPair{hd, w}}))
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
        case C.HvCons{hd, tl}:
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
    case C.HErr{}:
      {==}
    case C.HCata{s}:
      match x:
        case C.HvPair{sh, ks}:
          %L.agree(t, e, ks) : {C.upM(Maybe.bind(&2, C.HV, C.HV, C.eval.h(t, ks), rs => C.eval.h(s, C.HvPair{sh, rs}))) == Maybe.bind(&2, C.ZV, C.ZV, _, q => C.eval.z(s, C.ZvPair{C.up(sh), q})) : Maybe<&2, C.ZV>}
          L.z.bind(C.eval.h(t, ks), rs => C.eval.h(s, C.HvPair{sh, rs}), q => C.eval.z(s, C.ZvPair{C.up(sh), q}), v => L.agree(s, e, C.HvPair{sh, v}))
        case C.HvNil{}:
          {==}
        case C.HvCons{k, ks}:
          %L.agree(t, e, k) : {C.upM(C.h.cons(C.eval.h(t, k), C.eval.h(t, ks))) == C.z.cons(_, C.eval.z(t, C.up(ks))) : Maybe<&2, C.ZV>}
          %L.agree(t, e, ks) : {C.upM(C.h.cons(C.eval.h(t, k), C.eval.h(t, ks))) == C.z.cons(C.upM(C.eval.h(t, k)), _) : Maybe<&2, C.ZV>}
          L.z.cons(C.eval.h(t, k), C.eval.h(t, ks))
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

# 8. Int's range

# a run below another: the exact run in -(m+1)..m (RgIn) below GHC's Int
# of range m (LeInt) and below every integer (LeAll)
type RgLe is Data:
  LeInt{m: Nat}
  LeAll{m: Nat}

def L.lo(+o: RgLe) -> C.Rg:
  match o:
    case LeInt{m}:
      C.RgIn{m}
    case LeAll{m}:
      C.RgIn{m}

def L.hi(+o: RgLe) -> C.Rg:
  match o:
    case LeInt{m}:
      C.RgInt{m}
    case LeAll{m}:
      C.RgAll{}

# a number in the range is GHC's Int's (wrap leaves it) and every
# integer's
def L.cw(c: Bool, +m: Nat, +y: C.ZV, +u: C.ZV, e: {C.z.chk.at(c, y) == Some{u} : Maybe<&2, C.ZV>}) -> {Some{C.z.wrap.at(c, m, y)} == Some{u} : Maybe<&2, C.ZV>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({Some{C.z.wrap.at(False{}, m, y)} == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))

def L.ca(c: Bool, +y: C.ZV, +u: C.ZV, e: {C.z.chk.at(c, y) == Some{u} : Maybe<&2, C.ZV>}) -> {Some{y} == Some{u} : Maybe<&2, C.ZV>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({Some{y} == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))

# a number a literal, (+) or (-) makes
def L.rg.w(+o: RgLe, +y: C.ZV, +u: C.ZV, e: {C.z.rw(L.lo(o), y) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.rw(L.hi(o), y) == Some{u} : Maybe<&2, C.ZV>}:
  match o:
    case LeInt{+m}:
      L.cw(C.z.inr(m, y), m, y, u, e)
    case LeAll{+m}:
      L.ca(C.z.inr(m, y), y, u, e)

# a number div makes
def L.rg.d(+o: RgLe, +y: C.ZV, +u: C.ZV, e: {C.z.rd(L.lo(o), y) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.rd(L.hi(o), y) == Some{u} : Maybe<&2, C.ZV>}:
  match o:
    case LeInt{+m}:
      e
    case LeAll{+m}:
      L.ca(C.z.inr(m, y), y, u, e)

def L.rg.bw(+o: RgLe, x: Maybe<&2, C.ZV>, +u: C.ZV, e: {Maybe.bind(&2, C.ZV, C.ZV, x, y => C.z.rw(L.lo(o), y)) == Some{u} : Maybe<&2, C.ZV>}) -> {Maybe.bind(&2, C.ZV, C.ZV, x, y => C.z.rw(L.hi(o), y)) == Some{u} : Maybe<&2, C.ZV>}:
  match x:
    case None{}:
      Empty.absurd({None{} == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{+y}:
      L.rg.w(o, y, u, e)

def L.rg.bd(+o: RgLe, x: Maybe<&2, C.ZV>, +u: C.ZV, e: {Maybe.bind(&2, C.ZV, C.ZV, x, y => C.z.rd(L.lo(o), y)) == Some{u} : Maybe<&2, C.ZV>}) -> {Maybe.bind(&2, C.ZV, C.ZV, x, y => C.z.rd(L.hi(o), y)) == Some{u} : Maybe<&2, C.ZV>}:
  match x:
    case None{}:
      Empty.absurd({None{} == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{+y}:
      L.rg.d(o, y, u, e)

# b'Nat'sub
def L.rg.sa(lt: Bool, +o: RgLe, +d: Maybe<&2, C.ZV>, +u: C.ZV, e: {C.z.subT.at(lt, d, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.subT.at(lt, d, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match lt:
    case True{}:
      e
    case False{}:
      L.rg.bw(o, d, u, e)

def L.rg.subT(+o: RgLe, +a: C.ZV, +b: C.ZV, +u: C.ZV, e: {C.z.subT(a, b, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.subT(a, b, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match a:
    case C.ZvNat{i}:
      match b:
        case C.ZvNat{j}:
          e
        case C.ZvNeg{j}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvNeg{j}), u, e)
        case C.ZvBool{j}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvBool{j}), u, e)
        case C.ZvUnit{}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvUnit{}), u, e)
        case C.ZvPair{p, q}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvPair{p, q}), u, e)
        case C.ZvInl{j}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvInl{j}), u, e)
        case C.ZvInr{j}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvInr{j}), u, e)
        case C.ZvNil{}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvNil{}), u, e)
        case C.ZvCons{p, q}:
          L.rg.bw(o, C.z.sub(C.ZvNat{i}, C.ZvCons{p, q}), u, e)
    case C.ZvNeg{+i}:
      match b:
        case C.ZvNat{j}:
          e
        case C.ZvNeg{+j}:
          L.rg.sa(Nat.is_lt(j, i), o, C.z.sub(C.ZvNeg{i}, C.ZvNeg{j}), u, e)
        case C.ZvBool{j}:
          e
        case C.ZvUnit{}:
          e
        case C.ZvPair{p, q}:
          e
        case C.ZvInl{j}:
          e
        case C.ZvInr{j}:
          e
        case C.ZvNil{}:
          e
        case C.ZvCons{p, q}:
          e
    case C.ZvBool{j}:
      e
    case C.ZvUnit{}:
      e
    case C.ZvPair{p, q}:
      e
    case C.ZvInl{j}:
      e
    case C.ZvInr{j}:
      e
    case C.ZvNil{}:
      e
    case C.ZvCons{p, q}:
      e

# a primitive at two numbers
def L.rg.at(+o: RgLe, p: C.Prim, +a: C.ZV, +b: C.ZV, +u: C.ZV, e: {C.z.atw(p, a, b, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.atw(p, a, b, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match p:
    case C.PAdd{}:
      L.rg.bw(o, C.z.add(a, b), u, e)
    case C.PLt{}:
      e
    case C.PSub{}:
      L.rg.bw(o, C.z.sub(a, b), u, e)
    case C.PDiv{}:
      L.rg.bd(o, C.z.div(a, b), u, e)
    case C.PMod{}:
      e
    case C.PSubT{}:
      L.rg.subT(o, a, b, u, e)
    case C.PDivT{}:
      L.rg.bd(o, C.z.divT(a, b), u, e)
    case C.PModT{}:
      e

# a primitive, at any value (anything but two numbers is an error at both)
def L.rg.nb(+o: RgLe, p: C.Prim, +a: C.ZV, b: C.ZV, +u: C.ZV, e: {C.z.nb(p, a, b, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.nb(p, a, b, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match b:
    case C.ZvNat{j}:
      L.rg.at(o, p, a, C.ZvNat{j}, u, e)
    case C.ZvNeg{j}:
      L.rg.at(o, p, a, C.ZvNeg{j}, u, e)
    case C.ZvBool{q}:
      e
    case C.ZvUnit{}:
      e
    case C.ZvPair{q, r}:
      e
    case C.ZvInl{q}:
      e
    case C.ZvInr{q}:
      e
    case C.ZvNil{}:
      e
    case C.ZvCons{q, r}:
      e

def L.rg.ab(+o: RgLe, p: C.Prim, a: C.ZV, b: C.ZV, +u: C.ZV, e: {C.z.ab(p, a, b, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.ab(p, a, b, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match a:
    case C.ZvNat{i}:
      L.rg.nb(o, p, C.ZvNat{i}, b, u, e)
    case C.ZvNeg{i}:
      L.rg.nb(o, p, C.ZvNeg{i}, b, u, e)
    case C.ZvBool{q}:
      e
    case C.ZvUnit{}:
      e
    case C.ZvPair{q, r}:
      e
    case C.ZvInl{q}:
      e
    case C.ZvInr{q}:
      e
    case C.ZvNil{}:
      e
    case C.ZvCons{q, r}:
      e

def L.rg.prim(+o: RgLe, p: C.Prim, v: C.ZV, +u: C.ZV, e: {C.z.primw(p, v, L.lo(o)) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.primw(p, v, L.hi(o)) == Some{u} : Maybe<&2, C.ZV>}:
  match v:
    case C.ZvPair{a, b}:
      L.rg.ab(o, p, a, b, u, e)
    case C.ZvNat{q}:
      e
    case C.ZvNeg{q}:
      e
    case C.ZvBool{q}:
      e
    case C.ZvUnit{}:
      e
    case C.ZvInl{q}:
      e
    case C.ZvInr{q}:
      e
    case C.ZvNil{}:
      e
    case C.ZvCons{q, r}:
      e

# the runs' combinators: an answer below gives the same answer above
def L.rg.bind(x1: Maybe<&2, C.ZV>, -x2: Maybe<&2, C.ZV>, hx: @y: C.ZV -> {x1 == Some{y} : Maybe<&2, C.ZV>} -> {x2 == Some{y} : Maybe<&2, C.ZV>}, -k1: C.ZV -> Maybe<&2, C.ZV>, -k2: C.ZV -> Maybe<&2, C.ZV>, hk: @y: C.ZV -> @w: C.ZV -> {k1(y) == Some{w} : Maybe<&2, C.ZV>} -> {k2(y) == Some{w} : Maybe<&2, C.ZV>}, +u: C.ZV, e: {Maybe.bind(&2, C.ZV, C.ZV, x1, k1) == Some{u} : Maybe<&2, C.ZV>}) -> {Maybe.bind(&2, C.ZV, C.ZV, x2, k2) == Some{u} : Maybe<&2, C.ZV>}:
  match x1:
    case None{}:
      Empty.absurd({Maybe.bind(&2, C.ZV, C.ZV, x2, k2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{+y}:
      %Equal.sym(Maybe<&2, C.ZV>, x2, Some{y}, hx(y, {==})) : {Maybe.bind(&2, C.ZV, C.ZV, _, k2) == Some{u} : Maybe<&2, C.ZV>}
      hk(y, u, e)

def L.rg.pair(a1: Maybe<&2, C.ZV>, b1: Maybe<&2, C.ZV>, -a2: Maybe<&2, C.ZV>, -b2: Maybe<&2, C.ZV>, ha: @y: C.ZV -> {a1 == Some{y} : Maybe<&2, C.ZV>} -> {a2 == Some{y} : Maybe<&2, C.ZV>}, hb: @y: C.ZV -> {b1 == Some{y} : Maybe<&2, C.ZV>} -> {b2 == Some{y} : Maybe<&2, C.ZV>}, +u: C.ZV, e: {C.z.pair(a1, b1) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.pair(a2, b2) == Some{u} : Maybe<&2, C.ZV>}:
  match a1:
    case None{}:
      Empty.absurd({C.z.pair(a2, b2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{+p}:
      match b1:
        case None{}:
          Empty.absurd({C.z.pair(a2, b2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case Some{+q}:
          %Equal.sym(Maybe<&2, C.ZV>, a2, Some{p}, ha(p, {==})) : {C.z.pair(_, b2) == Some{u} : Maybe<&2, C.ZV>}
          %Equal.sym(Maybe<&2, C.ZV>, b2, Some{q}, hb(q, {==})) : {C.z.pair(Some{p}, _) == Some{u} : Maybe<&2, C.ZV>}
          e

def L.rg.cons(a1: Maybe<&2, C.ZV>, b1: Maybe<&2, C.ZV>, -a2: Maybe<&2, C.ZV>, -b2: Maybe<&2, C.ZV>, ha: @y: C.ZV -> {a1 == Some{y} : Maybe<&2, C.ZV>} -> {a2 == Some{y} : Maybe<&2, C.ZV>}, hb: @y: C.ZV -> {b1 == Some{y} : Maybe<&2, C.ZV>} -> {b2 == Some{y} : Maybe<&2, C.ZV>}, +u: C.ZV, e: {C.z.cons(a1, b1) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.cons(a2, b2) == Some{u} : Maybe<&2, C.ZV>}:
  match a1:
    case None{}:
      Empty.absurd({C.z.cons(a2, b2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{+p}:
      match b1:
        case None{}:
          Empty.absurd({C.z.cons(a2, b2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case Some{+q}:
          %Equal.sym(Maybe<&2, C.ZV>, a2, Some{p}, ha(p, {==})) : {C.z.cons(_, b2) == Some{u} : Maybe<&2, C.ZV>}
          %Equal.sym(Maybe<&2, C.ZV>, b2, Some{q}, hb(q, {==})) : {C.z.cons(Some{p}, _) == Some{u} : Maybe<&2, C.ZV>}
          e

def L.rg.if(c1: Maybe<&2, C.ZV>, a1: Maybe<&2, C.ZV>, d1: Maybe<&2, C.ZV>, -c2: Maybe<&2, C.ZV>, -a2: Maybe<&2, C.ZV>, -d2: Maybe<&2, C.ZV>, hc: @y: C.ZV -> {c1 == Some{y} : Maybe<&2, C.ZV>} -> {c2 == Some{y} : Maybe<&2, C.ZV>}, ha: @y: C.ZV -> {a1 == Some{y} : Maybe<&2, C.ZV>} -> {a2 == Some{y} : Maybe<&2, C.ZV>}, hd: @y: C.ZV -> {d1 == Some{y} : Maybe<&2, C.ZV>} -> {d2 == Some{y} : Maybe<&2, C.ZV>}, +u: C.ZV, e: {C.z.if(c1, a1, d1) == Some{u} : Maybe<&2, C.ZV>}) -> {C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}:
  match c1:
    case None{}:
      Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
    case Some{cv}:
      match cv:
        case C.ZvBool{bb}:
          match bb:
            case True{}:
              %Equal.sym(Maybe<&2, C.ZV>, c2, Some{C.ZvBool{True{}}}, hc(C.ZvBool{True{}}, {==})) : {C.z.if(_, a2, d2) == Some{u} : Maybe<&2, C.ZV>}
              ha(u, e)
            case False{}:
              %Equal.sym(Maybe<&2, C.ZV>, c2, Some{C.ZvBool{False{}}}, hc(C.ZvBool{False{}}, {==})) : {C.z.if(_, a2, d2) == Some{u} : Maybe<&2, C.ZV>}
              hd(u, e)
        case C.ZvNat{q}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvNeg{q}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvUnit{}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvPair{q, r}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvInl{q}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvInr{q}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvNil{}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))
        case C.ZvCons{q, r}:
          Empty.absurd({C.z.if(c2, a2, d2) == Some{u} : Maybe<&2, C.ZV>}, L.none.some.z(u, e))

# the run below answers u: the run above answers u, by induction on t (and,
# at a fold, on the list)
def L.rg.ev(+o: RgLe, +t: C.HTm, +v: C.ZV, +u: C.ZV, e: {C.eval.zr(L.lo(o), t, v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.zr(L.hi(o), t, v) == Some{u} : Maybe<&2, C.ZV>}:
  match t:
    case C.HId{}:
      e
    case C.HComp{+g, +f}:
      L.rg.bind(C.eval.zr(L.lo(o), f, v), C.eval.zr(L.hi(o), f, v), y => ey => L.rg.ev(o, f, v, y, ey), y => C.eval.zr(L.lo(o), g, y), y => C.eval.zr(L.hi(o), g, y), y => w => ew => L.rg.ev(o, g, y, w, ew), u, e)
    case C.HFst{}:
      e
    case C.HSnd{}:
      e
    case C.HPr{+f, +g}:
      L.rg.pair(C.eval.zr(L.lo(o), f, v), C.eval.zr(L.lo(o), g, v), C.eval.zr(L.hi(o), f, v), C.eval.zr(L.hi(o), g, v), y => ey => L.rg.ev(o, f, v, y, ey), y => ey => L.rg.ev(o, g, v, y, ey), u, e)
    case C.HInl{}:
      e
    case C.HInr{}:
      e
    case C.HCase{+f, +g}:
      match v:
        case C.ZvInl{a}:
          L.rg.ev(o, f, a, u, e)
        case C.ZvInr{b}:
          L.rg.ev(o, g, b, u, e)
        case C.ZvNat{q}:
          e
        case C.ZvNeg{q}:
          e
        case C.ZvBool{q}:
          e
        case C.ZvUnit{}:
          e
        case C.ZvPair{q, r}:
          e
        case C.ZvNil{}:
          e
        case C.ZvCons{q, r}:
          e
    case C.HLit{n}:
      L.rg.w(o, C.ZvNat{n}, u, e)
    case C.HPrim{p}:
      L.rg.prim(o, p, v, u, e)
    case C.HIf{+c, +a, +d}:
      L.rg.if(C.eval.zr(L.lo(o), c, v), C.eval.zr(L.lo(o), a, v), C.eval.zr(L.lo(o), d, v), C.eval.zr(L.hi(o), c, v), C.eval.zr(L.hi(o), a, v), C.eval.zr(L.hi(o), d, v), y => ey => L.rg.ev(o, c, v, y, ey), y => ey => L.rg.ev(o, a, v, y, ey), y => ey => L.rg.ev(o, d, v, y, ey), u, e)
    case C.HFold{+z, +s}:
      match v:
        case C.ZvNil{}:
          L.rg.ev(o, z, C.ZvUnit{}, u, e)
        case C.ZvCons{+hd, +tl}:
          L.rg.bind(C.eval.zr(L.lo(o), t, tl), C.eval.zr(L.hi(o), t, tl), y => ey => L.rg.ev(o, t, tl, y, ey), q => C.eval.zr(L.lo(o), s, C.ZvPair{hd, q}), q => C.eval.zr(L.hi(o), s, C.ZvPair{hd, q}), y => w => ew => L.rg.ev(o, s, C.ZvPair{hd, y}, w, ew), u, e)
        case C.ZvNat{q}:
          e
        case C.ZvNeg{q}:
          e
        case C.ZvBool{q}:
          e
        case C.ZvUnit{}:
          e
        case C.ZvPair{q, r}:
          e
        case C.ZvInl{q}:
          e
        case C.ZvInr{q}:
          e
    case C.HUnit{}:
      e
    case C.HNil{}:
      e
    case C.HCons{+a, +b}:
      L.rg.cons(C.eval.zr(L.lo(o), a, v), C.eval.zr(L.lo(o), b, v), C.eval.zr(L.hi(o), a, v), C.eval.zr(L.hi(o), b, v), y => ey => L.rg.ev(o, a, v, y, ey), y => ey => L.rg.ev(o, b, v, y, ey), u, e)
    case C.HDist{}:
      e
    case C.HFoldE{+z, +s}:
      match v:
        case C.ZvPair{+w, l}:
          match l:
            case C.ZvNil{}:
              L.rg.ev(o, z, w, u, e)
            case C.ZvCons{+hd, +tl}:
              L.rg.bind(C.eval.zr(L.lo(o), t, C.ZvPair{w, tl}), C.eval.zr(L.hi(o), t, C.ZvPair{w, tl}), y => ey => L.rg.ev(o, t, C.ZvPair{w, tl}, y, ey), q => C.eval.zr(L.lo(o), s, C.ZvPair{w, C.ZvPair{hd, q}}), q => C.eval.zr(L.hi(o), s, C.ZvPair{w, C.ZvPair{hd, q}}), y => k => ek => L.rg.ev(o, s, C.ZvPair{w, C.ZvPair{hd, y}}, k, ek), u, e)
            case C.ZvNat{q}:
              e
            case C.ZvNeg{q}:
              e
            case C.ZvBool{q}:
              e
            case C.ZvUnit{}:
              e
            case C.ZvPair{q, r}:
              e
            case C.ZvInl{q}:
              e
            case C.ZvInr{q}:
              e
        case C.ZvNil{}:
          e
        case C.ZvCons{q, r}:
          e
        case C.ZvNat{q}:
          e
        case C.ZvNeg{q}:
          e
        case C.ZvBool{q}:
          e
        case C.ZvUnit{}:
          e
        case C.ZvInl{q}:
          e
        case C.ZvInr{q}:
          e
    case C.HErr{}:
      e
    case C.HCata{+s}:
      match v:
        case C.ZvPair{+sh, +ks}:
          L.rg.bind(C.eval.zr(L.lo(o), t, ks), C.eval.zr(L.hi(o), t, ks), y => ey => L.rg.ev(o, t, ks, y, ey), q => C.eval.zr(L.lo(o), s, C.ZvPair{sh, q}), q => C.eval.zr(L.hi(o), s, C.ZvPair{sh, q}), y => w => ew => L.rg.ev(o, s, C.ZvPair{sh, y}, w, ew), u, e)
        case C.ZvNil{}:
          e
        case C.ZvCons{+k, +ks}:
          L.rg.cons(C.eval.zr(L.lo(o), t, k), C.eval.zr(L.lo(o), t, ks), C.eval.zr(L.hi(o), t, k), C.eval.zr(L.hi(o), t, ks), y => ey => L.rg.ev(o, t, k, y, ey), y => ey => L.rg.ev(o, t, ks, y, ey), u, e)
        case C.ZvNat{q}:
          e
        case C.ZvNeg{q}:
          e
        case C.ZvBool{q}:
          e
        case C.ZvUnit{}:
          e
        case C.ZvInl{q}:
          e
        case C.ZvInr{q}:
          e

def P.range.int(m, h, v, u, e):
  L.rg.ev(LeInt{m}, h, v, u, e)

def P.range.z(m, h, v, u, e):
  L.rg.ev(LeAll{m}, h, v, u, e)

# GHC's Int answers u, as every integer does, and that is h at Natural's
# (section 6)
def P.agree.int(m, h, e, x, u, ei):
  Equal.trans(Maybe<&2, C.ZV>, C.eval.int(m, h, C.up(x)), Some{u}, C.upM(C.eval.h(h, x)), P.range.int(m, h, C.up(x), u, ei), Equal.trans(Maybe<&2, C.ZV>, Some{u}, C.eval.z(h, C.up(x)), C.upM(C.eval.h(h, x)), Equal.sym(Maybe<&2, C.ZV>, C.eval.z(h, C.up(x)), Some{u}, P.range.z(m, h, C.up(x), u, ei)), Equal.sym(Maybe<&2, C.ZV>, C.upM(C.eval.h(h, x)), C.eval.z(h, C.up(x)), L.agree(h, e, x))))

def P.agree.int64(h, e, x, u, ei):
  P.agree.int(C.int.max(), h, e, x, u, ei)

# x + x at 127 at Int8: 254 taken around, -2
def P.range.int8():
  {==}

def L.isnat(m: Maybe<&2, C.ZV>) -> Type:
  match m:
    case Some{C.ZvNat{n}}:
      Empty
    case _:
      Unit

def P.range.not(e):
  %e : L.isnat(_)
  Unit{}

# 9. Laziness

# an answer r == Some v, lazily
def L.lz.cong(-r: Maybe<&2, C.HV>, -v: C.HV, e: {r == Some{v} : Maybe<&2, C.HV>}) -> {C.lzM(r) == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  Equal.cong(Maybe<&2, C.HV>, Maybe<&2, C.LV>, C.lzM, r, Some{v}, e)

def L.lz.comp(r: Maybe<&2, C.HV>, -lr: Maybe<&2, C.LV>, hr: @y: C.HV -> {r == Some{y} : Maybe<&2, C.HV>} -> {lr == Some{C.lz(y)} : Maybe<&2, C.LV>}, -k: C.HV -> Maybe<&2, C.HV>, -kl: Maybe<&2, C.LV> -> Maybe<&2, C.LV>, hk: @y: C.HV -> @w: C.HV -> {k(y) == Some{w} : Maybe<&2, C.HV>} -> {kl(Some{C.lz(y)}) == Some{C.lz(w)} : Maybe<&2, C.LV>}, +v: C.HV, e: {Maybe.bind(&2, C.HV, C.HV, r, k) == Some{v} : Maybe<&2, C.HV>}) -> {kl(lr) == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match r:
    case None{}:
      Empty.absurd({kl(lr) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case Some{+y}:
      %Equal.sym(Maybe<&2, C.LV>, lr, Some{C.lz(y)}, hr(y, {==})) : {kl(_) == Some{C.lz(v)} : Maybe<&2, C.LV>}
      hk(y, v, e)

def L.lz.pair(r1: Maybe<&2, C.HV>, r2: Maybe<&2, C.HV>, -l1: Maybe<&2, C.LV>, -l2: Maybe<&2, C.LV>, h1: @y: C.HV -> {r1 == Some{y} : Maybe<&2, C.HV>} -> {l1 == Some{C.lz(y)} : Maybe<&2, C.LV>}, h2: @y: C.HV -> {r2 == Some{y} : Maybe<&2, C.HV>} -> {l2 == Some{C.lz(y)} : Maybe<&2, C.LV>}, +v: C.HV, e: {C.h.pair(r1, r2) == Some{v} : Maybe<&2, C.HV>}) -> {Some{C.LvPair{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match r1:
    case None{}:
      Empty.absurd({Some{C.LvPair{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case Some{+p}:
      match r2:
        case None{}:
          Empty.absurd({Some{C.LvPair{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case Some{+q}:
          %Equal.sym(Maybe<&2, C.LV>, l1, Some{C.lz(p)}, h1(p, {==})) : {Some{C.LvPair{_, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}
          %Equal.sym(Maybe<&2, C.LV>, l2, Some{C.lz(q)}, h2(q, {==})) : {Some{C.LvPair{Some{C.lz(p)}, _}} == Some{C.lz(v)} : Maybe<&2, C.LV>}
          L.lz.cong(Some{C.HvPair{p, q}}, v, e)

def L.lz.cons(r1: Maybe<&2, C.HV>, r2: Maybe<&2, C.HV>, -l1: Maybe<&2, C.LV>, -l2: Maybe<&2, C.LV>, h1: @y: C.HV -> {r1 == Some{y} : Maybe<&2, C.HV>} -> {l1 == Some{C.lz(y)} : Maybe<&2, C.LV>}, h2: @y: C.HV -> {r2 == Some{y} : Maybe<&2, C.HV>} -> {l2 == Some{C.lz(y)} : Maybe<&2, C.LV>}, +v: C.HV, e: {C.h.cons(r1, r2) == Some{v} : Maybe<&2, C.HV>}) -> {Some{C.LvCons{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match r1:
    case None{}:
      Empty.absurd({Some{C.LvCons{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case Some{+p}:
      match r2:
        case None{}:
          Empty.absurd({Some{C.LvCons{l1, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case Some{+q}:
          %Equal.sym(Maybe<&2, C.LV>, l1, Some{C.lz(p)}, h1(p, {==})) : {Some{C.LvCons{_, l2}} == Some{C.lz(v)} : Maybe<&2, C.LV>}
          %Equal.sym(Maybe<&2, C.LV>, l2, Some{C.lz(q)}, h2(q, {==})) : {Some{C.LvCons{Some{C.lz(p)}, _}} == Some{C.lz(v)} : Maybe<&2, C.LV>}
          L.lz.cong(Some{C.HvCons{p, q}}, v, e)

def L.lz.dist(x: C.HV, +v: C.HV, e: {C.h.dist(x) == Some{v} : Maybe<&2, C.HV>}) -> {C.l.dist(Some{C.lz(x)}) == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match x:
    case C.HvPair{p, q}:
      match q:
        case C.HvInl{a}:
          L.lz.cong(Some{C.HvInl{C.HvPair{p, a}}}, v, e)
        case C.HvInr{b}:
          L.lz.cong(Some{C.HvInr{C.HvPair{p, b}}}, v, e)
        case C.HvNat{n}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{b}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvPair{a, b}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{h, t}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvNat{n}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvBool{b}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvUnit{}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvInl{a}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvInr{b}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvNil{}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HvCons{h, t}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))

def L.lz.if(rc: Maybe<&2, C.HV>, ra: Maybe<&2, C.HV>, rd: Maybe<&2, C.HV>, -lc: Maybe<&2, C.LV>, -la: Maybe<&2, C.LV>, -ld: Maybe<&2, C.LV>, hc: @y: C.HV -> {rc == Some{y} : Maybe<&2, C.HV>} -> {lc == Some{C.lz(y)} : Maybe<&2, C.LV>}, ha: @y: C.HV -> {ra == Some{y} : Maybe<&2, C.HV>} -> {la == Some{C.lz(y)} : Maybe<&2, C.LV>}, hd: @y: C.HV -> {rd == Some{y} : Maybe<&2, C.HV>} -> {ld == Some{C.lz(y)} : Maybe<&2, C.LV>}, +v: C.HV, e: {C.h.if(rc, ra, rd) == Some{v} : Maybe<&2, C.HV>}) -> {C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match rc:
    case None{}:
      Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case Some{cv}:
      match cv:
        case C.HvBool{bb}:
          match bb:
            case True{}:
              %Equal.sym(Maybe<&2, C.LV>, lc, Some{C.LvBool{True{}}}, hc(C.HvBool{True{}}, {==})) : {C.l.if(_, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}
              ha(v, e)
            case False{}:
              %Equal.sym(Maybe<&2, C.LV>, lc, Some{C.LvBool{False{}}}, hc(C.HvBool{False{}}, {==})) : {C.l.if(_, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}
              hd(v, e)
        case C.HvNat{q}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvPair{q, r}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{q, r}:
          Empty.absurd({C.l.if(lc, la, ld) == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))

# a primitive looks at the same two numbers, lazily
def L.lz.nnb(a: Nat, b: C.HV) -> {C.h.nn(C.HvPair{C.HvNat{a}, b}) == C.l.nn(Some{C.lz(C.HvPair{C.HvNat{a}, b})}) : C.NN}:
  match b:
    case C.HvNat{j}:
      {==}
    case C.HvBool{q}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{q, r}:
      {==}
    case C.HvInl{q}:
      {==}
    case C.HvInr{q}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{q, r}:
      {==}

def L.lz.nn(x: C.HV) -> {C.h.nn(x) == C.l.nn(Some{C.lz(x)}) : C.NN}:
  match x:
    case C.HvPair{a, b}:
      match a:
        case C.HvNat{i}:
          L.lz.nnb(i, b)
        case C.HvBool{q}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{q, r}:
          {==}
        case C.HvInl{q}:
          {==}
        case C.HvInr{q}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{q, r}:
          {==}
    case C.HvNat{q}:
      {==}
    case C.HvBool{q}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvInl{q}:
      {==}
    case C.HvInr{q}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{q, r}:
      {==}

def L.lz.pv(v: C.PV, +w: C.HV, e: {C.h.pv(v) == Some{w} : Maybe<&2, C.HV>}) -> {C.l.pv(v) == Some{C.lz(w)} : Maybe<&2, C.LV>}:
  match v:
    case C.PvNat{n}:
      L.lz.cong(Some{C.HvNat{n}}, w, e)
    case C.PvBool{b}:
      L.lz.cong(Some{C.HvBool{b}}, w, e)
    case C.PvNo{}:
      Empty.absurd({None{} == Some{C.lz(w)} : Maybe<&2, C.LV>}, L.none.some.h(w, e))

def L.lz.prim(p: C.Prim, +x: C.HV, +w: C.HV, e: {C.h.prim(p, x) == Some{w} : Maybe<&2, C.HV>}) -> {C.l.pv(C.p.nn(p, C.l.nn(Some{C.lz(x)}))) == Some{C.lz(w)} : Maybe<&2, C.LV>}:
  %L.lz.nn(x) : {C.l.pv(C.p.nn(p, _)) == Some{C.lz(w)} : Maybe<&2, C.LV>}
  L.lz.pv(C.p.nn(p, C.h.nn(x)), w, e)

# h's strict answer is its lazy one, by induction on h (and, at a fold, on
# the list)
def L.lz.sq(+t: C.HTm, +x: C.HV, +v: C.HV, e: {C.eval.h(t, x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.lz(t, Some{C.lz(x)}) == Some{C.lz(v)} : Maybe<&2, C.LV>}:
  match t:
    case C.HId{}:
      L.lz.cong(Some{x}, v, e)
    case C.HComp{+g, +f}:
      L.lz.comp(C.eval.h(f, x), C.eval.lz(f, Some{C.lz(x)}), y => ey => L.lz.sq(f, x, y, ey), y => C.eval.h(g, y), q => C.eval.lz(g, q), y => w => ew => L.lz.sq(g, y, w, ew), v, e)
    case C.HFst{}:
      match x:
        case C.HvPair{a, b}:
          L.lz.cong(Some{a}, v, e)
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HSnd{}:
      match x:
        case C.HvPair{a, b}:
          L.lz.cong(Some{b}, v, e)
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HPr{+f, +g}:
      L.lz.pair(C.eval.h(f, x), C.eval.h(g, x), C.eval.lz(f, Some{C.lz(x)}), C.eval.lz(g, Some{C.lz(x)}), y => ey => L.lz.sq(f, x, y, ey), y => ey => L.lz.sq(g, x, y, ey), v, e)
    case C.HInl{}:
      L.lz.cong(Some{C.HvInl{x}}, v, e)
    case C.HInr{}:
      L.lz.cong(Some{C.HvInr{x}}, v, e)
    case C.HCase{+f, +g}:
      match x:
        case C.HvInl{a}:
          L.lz.sq(f, a, v, e)
        case C.HvInr{b}:
          L.lz.sq(g, b, v, e)
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvPair{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HLit{n}:
      L.lz.cong(Some{C.HvNat{n}}, v, e)
    case C.HPrim{p}:
      L.lz.prim(p, x, v, e)
    case C.HIf{+c, +a, +d}:
      L.lz.if(C.eval.h(c, x), C.eval.h(a, x), C.eval.h(d, x), C.eval.lz(c, Some{C.lz(x)}), C.eval.lz(a, Some{C.lz(x)}), C.eval.lz(d, Some{C.lz(x)}), y => ey => L.lz.sq(c, x, y, ey), y => ey => L.lz.sq(a, x, y, ey), y => ey => L.lz.sq(d, x, y, ey), v, e)
    case C.HFold{+z, +s}:
      match x:
        case C.HvNil{}:
          L.lz.sq(z, C.HvUnit{}, v, e)
        case C.HvCons{+hd, +tl}:
          L.lz.comp(C.eval.h(t, tl), C.eval.lz(t, Some{C.lz(tl)}), y => ey => L.lz.sq(t, tl, y, ey), r => C.eval.h(s, C.HvPair{hd, r}), q => C.eval.lz(s, Some{C.LvPair{Some{C.lz(hd)}, q}}), y => w => ew => L.lz.sq(s, C.HvPair{hd, y}, w, ew), v, e)
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvPair{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HUnit{}:
      L.lz.cong(Some{C.HvUnit{}}, v, e)
    case C.HNil{}:
      L.lz.cong(Some{C.HvNil{}}, v, e)
    case C.HCons{+a, +b}:
      L.lz.cons(C.eval.h(a, x), C.eval.h(b, x), C.eval.lz(a, Some{C.lz(x)}), C.eval.lz(b, Some{C.lz(x)}), y => ey => L.lz.sq(a, x, y, ey), y => ey => L.lz.sq(b, x, y, ey), v, e)
    case C.HDist{}:
      L.lz.dist(x, v, e)
    case C.HFoldE{+z, +s}:
      match x:
        case C.HvPair{+w, l}:
          match l:
            case C.HvNil{}:
              L.lz.sq(z, w, v, e)
            case C.HvCons{+hd, +tl}:
              L.lz.comp(C.eval.h(t, C.HvPair{w, tl}), C.eval.lz(t, Some{C.lz(C.HvPair{w, tl})}), y => ey => L.lz.sq(t, C.HvPair{w, tl}, y, ey), r => C.eval.h(s, C.HvPair{w, C.HvPair{hd, r}}), q => C.eval.lz(s, Some{C.LvPair{Some{C.lz(w)}, Some{C.LvPair{Some{C.lz(hd)}, q}}}}), y => k => ek => L.lz.sq(s, C.HvPair{w, C.HvPair{hd, y}}, k, ek), v, e)
            case C.HvNat{q}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
            case C.HvBool{q}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
            case C.HvUnit{}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
            case C.HvPair{q, r}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
            case C.HvInl{q}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
            case C.HvInr{q}:
              Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNil{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvCons{q, r}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HErr{}:
      Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
    case C.HCata{+s}:
      match x:
        case C.HvPair{+sh, +ks}:
          L.lz.comp(C.eval.h(t, ks), C.eval.lz(t, Some{C.lz(ks)}), y => ey => L.lz.sq(t, ks, y, ey), rs => C.eval.h(s, C.HvPair{sh, rs}), q => C.eval.lz(s, Some{C.LvPair{Some{C.lz(sh)}, q}}), y => w => ew => L.lz.sq(s, C.HvPair{sh, y}, w, ew), v, e)
        case C.HvNil{}:
          L.lz.cong(Some{C.HvNil{}}, v, e)
        case C.HvCons{+k, +ks}:
          L.lz.cons(C.eval.h(t, k), C.eval.h(t, ks), C.eval.lz(t, Some{C.lz(k)}), C.eval.lz(t, Some{C.lz(ks)}), y => ey => L.lz.sq(t, k, y, ey), y => ey => L.lz.sq(t, ks, y, ey), v, e)
        case C.HvNat{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvBool{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvUnit{}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInl{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))
        case C.HvInr{q}:
          Empty.absurd({None{} == Some{C.lz(v)} : Maybe<&2, C.LV>}, L.none.some.h(v, e))

def P.lazy.sq(t, x, v, e):
  L.lz.sq(t, x, v, e)

# F's Bend answers w at y: h answers dec w at dec y strictly (L.h.at), so
# lazily
def P.lazy.F(h, y, w, e):
  L.lz.sq(h, C.dec(y), C.dec(w), L.h.at(h, y, w, e))

def P.lazy.fe():
  {==}

def P.lazy.fe.F():
  {==}

# fst (1, failure): its Bend fails, and G's Haskell of it is 1, lazily
def L.bfe() -> C.BTm:
  C.BComp{C.BFst{}, C.BPr{C.BLit{1n}, C.BFail{}}}

def P.adj.FG.lazy.not(adj):
  L.none.some.b(C.BvNat{1n}, adj(C.HLit{1n}, L.bfe(), x => v => e => e, C.BvUnit{}, C.BvNat{1n}, {==}))

# 10. Int as HsInt

# a bind's functions equal at every value
def L.zz.bind(r: Maybe<&2, C.ZV>, -k1: C.ZV -> Maybe<&2, C.ZV>, -k2: C.ZV -> Maybe<&2, C.ZV>, ih: @v: C.ZV -> {k1(v) == k2(v) : Maybe<&2, C.ZV>}) -> {Maybe.bind(&2, C.ZV, C.ZV, r, k1) == Maybe.bind(&2, C.ZV, C.ZV, r, k2) : Maybe<&2, C.ZV>}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      ih(v)

def P.sq.F.z(r, t, v):
  match t:
    case C.HId{}:
      {==}
    case C.HComp{g, f}:
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(f), v), C.eval.zr(r, f, v), P.sq.F.z(r, f, v)) : {Maybe.bind(&2, C.ZV, C.ZV, _, y => C.eval.bz(r, C.F(g), y)) == Maybe.bind(&2, C.ZV, C.ZV, C.eval.zr(r, f, v), y => C.eval.zr(r, g, y)) : Maybe<&2, C.ZV>}
      L.zz.bind(C.eval.zr(r, f, v), y => C.eval.bz(r, C.F(g), y), y => C.eval.zr(r, g, y), y => P.sq.F.z(r, g, y))
    case C.HFst{}:
      {==}
    case C.HSnd{}:
      {==}
    case C.HPr{f, g}:
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(f), v), C.eval.zr(r, f, v), P.sq.F.z(r, f, v)) : {C.z.pair(_, C.eval.bz(r, C.F(g), v)) == C.z.pair(C.eval.zr(r, f, v), C.eval.zr(r, g, v)) : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(g), v), C.eval.zr(r, g, v), P.sq.F.z(r, g, v)) : {C.z.pair(C.eval.zr(r, f, v), _) == C.z.pair(C.eval.zr(r, f, v), C.eval.zr(r, g, v)) : Maybe<&2, C.ZV>}
      {==}
    case C.HInl{}:
      {==}
    case C.HInr{}:
      {==}
    case C.HCase{f, g}:
      match v:
        case C.ZvInl{a}:
          P.sq.F.z(r, f, a)
        case C.ZvInr{b}:
          P.sq.F.z(r, g, b)
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{b}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{a, b}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{h, tl}:
          {==}
    case C.HLit{n}:
      {==}
    case C.HPrim{p}:
      {==}
    case C.HIf{c, a, e}:
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(c), v), C.eval.zr(r, c, v), P.sq.F.z(r, c, v)) : {C.z.if(_, C.eval.bz(r, C.F(a), v), C.eval.bz(r, C.F(e), v)) == C.z.if(C.eval.zr(r, c, v), C.eval.zr(r, a, v), C.eval.zr(r, e, v)) : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(a), v), C.eval.zr(r, a, v), P.sq.F.z(r, a, v)) : {C.z.if(C.eval.zr(r, c, v), _, C.eval.bz(r, C.F(e), v)) == C.z.if(C.eval.zr(r, c, v), C.eval.zr(r, a, v), C.eval.zr(r, e, v)) : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(e), v), C.eval.zr(r, e, v), P.sq.F.z(r, e, v)) : {C.z.if(C.eval.zr(r, c, v), C.eval.zr(r, a, v), _) == C.z.if(C.eval.zr(r, c, v), C.eval.zr(r, a, v), C.eval.zr(r, e, v)) : Maybe<&2, C.ZV>}
      {==}
    case C.HFold{z, s}:
      match v:
        case C.ZvNil{}:
          P.sq.F.z(r, z, C.ZvUnit{})
        case C.ZvCons{hd, tl}:
          %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(t), tl), C.eval.zr(r, t, tl), P.sq.F.z(r, t, tl)) : {Maybe.bind(&2, C.ZV, C.ZV, _, q => C.eval.bz(r, C.F(s), C.ZvPair{hd, q})) == Maybe.bind(&2, C.ZV, C.ZV, C.eval.zr(r, t, tl), q => C.eval.zr(r, s, C.ZvPair{hd, q})) : Maybe<&2, C.ZV>}
          L.zz.bind(C.eval.zr(r, t, tl), q => C.eval.bz(r, C.F(s), C.ZvPair{hd, q}), q => C.eval.zr(r, s, C.ZvPair{hd, q}), q => P.sq.F.z(r, s, C.ZvPair{hd, q}))
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{b}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{a, b}:
          {==}
        case C.ZvInl{a}:
          {==}
        case C.ZvInr{b}:
          {==}
    case C.HUnit{}:
      {==}
    case C.HNil{}:
      {==}
    case C.HCons{a, b}:
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(a), v), C.eval.zr(r, a, v), P.sq.F.z(r, a, v)) : {C.z.cons(_, C.eval.bz(r, C.F(b), v)) == C.z.cons(C.eval.zr(r, a, v), C.eval.zr(r, b, v)) : Maybe<&2, C.ZV>}
      %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(b), v), C.eval.zr(r, b, v), P.sq.F.z(r, b, v)) : {C.z.cons(C.eval.zr(r, a, v), _) == C.z.cons(C.eval.zr(r, a, v), C.eval.zr(r, b, v)) : Maybe<&2, C.ZV>}
      {==}
    case C.HDist{}:
      {==}
    case C.HFoldE{z, s}:
      match v:
        case C.ZvPair{+w, l}:
          match l:
            case C.ZvNil{}:
              P.sq.F.z(r, z, w)
            case C.ZvCons{hd, tl}:
              %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(t), C.ZvPair{w, tl}), C.eval.zr(r, t, C.ZvPair{w, tl}), P.sq.F.z(r, t, C.ZvPair{w, tl})) : {Maybe.bind(&2, C.ZV, C.ZV, _, q => C.eval.bz(r, C.F(s), C.ZvPair{w, C.ZvPair{hd, q}})) == Maybe.bind(&2, C.ZV, C.ZV, C.eval.zr(r, t, C.ZvPair{w, tl}), q => C.eval.zr(r, s, C.ZvPair{w, C.ZvPair{hd, q}})) : Maybe<&2, C.ZV>}
              L.zz.bind(C.eval.zr(r, t, C.ZvPair{w, tl}), q => C.eval.bz(r, C.F(s), C.ZvPair{w, C.ZvPair{hd, q}}), q => C.eval.zr(r, s, C.ZvPair{w, C.ZvPair{hd, q}}), q => P.sq.F.z(r, s, C.ZvPair{w, C.ZvPair{hd, q}}))
            case C.ZvNat{n}:
              {==}
            case C.ZvNeg{n}:
              {==}
            case C.ZvBool{b}:
              {==}
            case C.ZvUnit{}:
              {==}
            case C.ZvPair{a, b}:
              {==}
            case C.ZvInl{a}:
              {==}
            case C.ZvInr{b}:
              {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{hd, tl}:
          {==}
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{b}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvInl{a}:
          {==}
        case C.ZvInr{b}:
          {==}
    case C.HErr{}:
      {==}
    case C.HCata{s}:
      match v:
        case C.ZvPair{sh, ks}:
          %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(t), ks), C.eval.zr(r, t, ks), P.sq.F.z(r, t, ks)) : {Maybe.bind(&2, C.ZV, C.ZV, _, q => C.eval.bz(r, C.F(s), C.ZvPair{sh, q})) == Maybe.bind(&2, C.ZV, C.ZV, C.eval.zr(r, t, ks), q => C.eval.zr(r, s, C.ZvPair{sh, q})) : Maybe<&2, C.ZV>}
          L.zz.bind(C.eval.zr(r, t, ks), q => C.eval.bz(r, C.F(s), C.ZvPair{sh, q}), q => C.eval.zr(r, s, C.ZvPair{sh, q}), q => P.sq.F.z(r, s, C.ZvPair{sh, q}))
        case C.ZvNil{}:
          {==}
        case C.ZvCons{k, ks}:
          %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(t), k), C.eval.zr(r, t, k), P.sq.F.z(r, t, k)) : {C.z.cons(_, C.eval.bz(r, C.F(t), ks)) == C.z.cons(C.eval.zr(r, t, k), C.eval.zr(r, t, ks)) : Maybe<&2, C.ZV>}
          %Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(t), ks), C.eval.zr(r, t, ks), P.sq.F.z(r, t, ks)) : {C.z.cons(C.eval.zr(r, t, k), _) == C.z.cons(C.eval.zr(r, t, k), C.eval.zr(r, t, ks)) : Maybe<&2, C.ZV>}
          {==}
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{b}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvInl{a}:
          {==}
        case C.ZvInr{b}:
          {==}

# F after G is the identity, so G's square is F's at G b
def L.FG.id(b: C.BTm) -> {C.F(C.G(b)) == b : C.BTm}:
  match b:
    case C.BId{}:
      {==}
    case C.BComp{g, f}:
      %L.FG.id(g) : {C.BComp{C.F(C.G(g)), C.F(C.G(f))} == C.BComp{_, f} : C.BTm}
      %L.FG.id(f) : {C.BComp{C.F(C.G(g)), C.F(C.G(f))} == C.BComp{C.F(C.G(g)), _} : C.BTm}
      {==}
    case C.BFst{}:
      {==}
    case C.BSnd{}:
      {==}
    case C.BPr{f, g}:
      %L.FG.id(f) : {C.BPr{C.F(C.G(f)), C.F(C.G(g))} == C.BPr{_, g} : C.BTm}
      %L.FG.id(g) : {C.BPr{C.F(C.G(f)), C.F(C.G(g))} == C.BPr{C.F(C.G(f)), _} : C.BTm}
      {==}
    case C.BInl{}:
      {==}
    case C.BInr{}:
      {==}
    case C.BCase{f, g}:
      %L.FG.id(f) : {C.BCase{C.F(C.G(f)), C.F(C.G(g))} == C.BCase{_, g} : C.BTm}
      %L.FG.id(g) : {C.BCase{C.F(C.G(f)), C.F(C.G(g))} == C.BCase{C.F(C.G(f)), _} : C.BTm}
      {==}
    case C.BLit{n}:
      {==}
    case C.BPrim{p}:
      {==}
    case C.BIf{c, a, e}:
      %L.FG.id(c) : {C.BIf{C.F(C.G(c)), C.F(C.G(a)), C.F(C.G(e))} == C.BIf{_, a, e} : C.BTm}
      %L.FG.id(a) : {C.BIf{C.F(C.G(c)), C.F(C.G(a)), C.F(C.G(e))} == C.BIf{C.F(C.G(c)), _, e} : C.BTm}
      %L.FG.id(e) : {C.BIf{C.F(C.G(c)), C.F(C.G(a)), C.F(C.G(e))} == C.BIf{C.F(C.G(c)), C.F(C.G(a)), _} : C.BTm}
      {==}
    case C.BFold{z, s}:
      %L.FG.id(z) : {C.BFold{C.F(C.G(z)), C.F(C.G(s))} == C.BFold{_, s} : C.BTm}
      %L.FG.id(s) : {C.BFold{C.F(C.G(z)), C.F(C.G(s))} == C.BFold{C.F(C.G(z)), _} : C.BTm}
      {==}
    case C.BUnit{}:
      {==}
    case C.BNil{}:
      {==}
    case C.BCons{f, g}:
      %L.FG.id(f) : {C.BCons{C.F(C.G(f)), C.F(C.G(g))} == C.BCons{_, g} : C.BTm}
      %L.FG.id(g) : {C.BCons{C.F(C.G(f)), C.F(C.G(g))} == C.BCons{C.F(C.G(f)), _} : C.BTm}
      {==}
    case C.BDist{}:
      {==}
    case C.BFoldE{z, s}:
      %L.FG.id(z) : {C.BFoldE{C.F(C.G(z)), C.F(C.G(s))} == C.BFoldE{_, s} : C.BTm}
      %L.FG.id(s) : {C.BFoldE{C.F(C.G(z)), C.F(C.G(s))} == C.BFoldE{C.F(C.G(z)), _} : C.BTm}
      {==}
    case C.BFail{}:
      {==}
    case C.BCata{s}:
      %L.FG.id(s) : {C.BCata{C.F(C.G(s))} == C.BCata{_} : C.BTm}
      {==}

def P.sq.G.z(r, b, v):
  %L.FG.id(b) : {C.eval.zr(r, C.G(b), v) == C.eval.bz(r, _, v) : Maybe<&2, C.ZV>}
  Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(C.G(b)), v), C.eval.zr(r, C.G(b), v), P.sq.F.z(r, C.G(b), v))

# an answer through an equation
def L.eqto(-p: Maybe<&2, C.ZV>, -q: Maybe<&2, C.ZV>, -u: C.ZV, e: {p == q : Maybe<&2, C.ZV>}, ep: {p == Some{u} : Maybe<&2, C.ZV>}) -> {q == Some{u} : Maybe<&2, C.ZV>}:
  %e : {_ == Some{u} : Maybe<&2, C.ZV>}
  ep

# F's Bend at v from h's answer there, and back; G's Haskell's from b's
def L.Fz.up(+r: C.Rg, +h: C.HTm, +v: C.ZV, -u: C.ZV, e: {C.eval.zr(r, h, v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.bz(r, C.F(h), v) == Some{u} : Maybe<&2, C.ZV>}:
  L.eqto(C.eval.zr(r, h, v), C.eval.bz(r, C.F(h), v), u, Equal.sym(Maybe<&2, C.ZV>, C.eval.bz(r, C.F(h), v), C.eval.zr(r, h, v), P.sq.F.z(r, h, v)), e)

def L.Fz.down(+r: C.Rg, +h: C.HTm, +v: C.ZV, -u: C.ZV, e: {C.eval.bz(r, C.F(h), v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.zr(r, h, v) == Some{u} : Maybe<&2, C.ZV>}:
  L.eqto(C.eval.bz(r, C.F(h), v), C.eval.zr(r, h, v), u, P.sq.F.z(r, h, v), e)

def L.Gz.up(+r: C.Rg, +b: C.BTm, +v: C.ZV, -u: C.ZV, e: {C.eval.bz(r, b, v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.zr(r, C.G(b), v) == Some{u} : Maybe<&2, C.ZV>}:
  L.eqto(C.eval.bz(r, b, v), C.eval.zr(r, C.G(b), v), u, Equal.sym(Maybe<&2, C.ZV>, C.eval.zr(r, C.G(b), v), C.eval.bz(r, b, v), P.sq.G.z(r, b, v)), e)

def L.Gz.down(+r: C.Rg, +b: C.BTm, +v: C.ZV, -u: C.ZV, e: {C.eval.zr(r, C.G(b), v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.bz(r, b, v) == Some{u} : Maybe<&2, C.ZV>}:
  L.eqto(C.eval.zr(r, C.G(b), v), C.eval.bz(r, b, v), u, P.sq.G.z(r, b, v), e)

def L.FGz.l(+r: C.Rg, +h: C.HTm, +b: C.BTm, le: P.Le.z(v => C.eval.bz(r, C.F(h), v), v => C.eval.bz(r, b, v)), +v: C.ZV, +u: C.ZV, e: {C.eval.zr(r, h, v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.zr(r, C.G(b), v) == Some{u} : Maybe<&2, C.ZV>}:
  L.Gz.up(r, b, v, u, le(v, u, L.Fz.up(r, h, v, u, e)))

def P.adj.FG.z.l(r, h, b, le):
  v => u => e => L.FGz.l(r, h, b, le, v, u, e)

def L.FGz.r(+r: C.Rg, +h: C.HTm, +b: C.BTm, le: P.Le.z(v => C.eval.zr(r, h, v), v => C.eval.zr(r, C.G(b), v)), +v: C.ZV, +u: C.ZV, e: {C.eval.bz(r, C.F(h), v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.bz(r, b, v) == Some{u} : Maybe<&2, C.ZV>}:
  L.Gz.down(r, b, v, u, le(v, u, L.Fz.down(r, h, v, u, e)))

def P.adj.FG.z.r(r, h, b, le):
  v => u => e => L.FGz.r(r, h, b, le, v, u, e)

def L.GFz.l(+r: C.Rg, +h: C.HTm, +b: C.BTm, le: P.Le.z(v => C.eval.zr(r, C.G(b), v), v => C.eval.zr(r, h, v)), +v: C.ZV, +u: C.ZV, e: {C.eval.bz(r, b, v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.bz(r, C.F(h), v) == Some{u} : Maybe<&2, C.ZV>}:
  L.Fz.up(r, h, v, u, le(v, u, L.Gz.up(r, b, v, u, e)))

def P.adj.GF.z.l(r, h, b, le):
  v => u => e => L.GFz.l(r, h, b, le, v, u, e)

def L.GFz.r(+r: C.Rg, +h: C.HTm, +b: C.BTm, le: P.Le.z(v => C.eval.bz(r, b, v), v => C.eval.bz(r, C.F(h), v)), +v: C.ZV, +u: C.ZV, e: {C.eval.zr(r, C.G(b), v) == Some{u} : Maybe<&2, C.ZV>}) -> {C.eval.zr(r, h, v) == Some{u} : Maybe<&2, C.ZV>}:
  L.Fz.down(r, h, v, u, le(v, u, L.Gz.down(r, b, v, u, e)))

def P.adj.GF.z.r(r, h, b, le):
  v => u => e => L.GFz.r(r, h, b, le, v, u, e)

def P.hsint.int(m, h, v, u, e):
  P.range.int(m, h, v, u, L.Fz.down(C.RgIn{m}, h, v, u, e))

def P.hsint.all(m, h, v, u, e):
  L.Fz.up(C.RgAll{}, h, v, u, P.range.z(m, h, v, u, L.Fz.down(C.RgIn{m}, h, v, u, e)))

def P.hsint.not(e):
  %e : L.isnat(_)
  Unit{}

# 11. Variables

# a let's value after its environment
def L.cc.let(m: Maybe<&2, C.HV>, -env: C.HV, -k: C.HV -> Maybe<&2, C.HV>) -> {Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{env}, m), k) == Maybe.bind(&2, C.HV, C.HV, m, v => k(C.HvPair{env, v})) : Maybe<&2, C.HV>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a bind's functions equal at every value
def L.hh.bind(r: Maybe<&2, C.HV>, -k1: C.HV -> Maybe<&2, C.HV>, -k2: C.HV -> Maybe<&2, C.HV>, ih: @v: C.HV -> {k1(v) == k2(v) : Maybe<&2, C.HV>}) -> {Maybe.bind(&2, C.HV, C.HV, r, k1) == Maybe.bind(&2, C.HV, C.HV, r, k2) : Maybe<&2, C.HV>}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      ih(v)

def L.cc.var(i: Nat, env: C.HV) -> {C.eval.h(C.cc.var(i), env) == C.ev.look(i, env) : Maybe<&2, C.HV>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      L.hh.bind(C.h.fst(env), e => C.eval.h(C.cc.var(j), e), e => C.ev.look(j, e), e => L.cc.var(j, e))

def P.cc.ok(t, env):
  match t:
    case C.EVar{i}:
      L.cc.var(i, env)
    case C.ELit{n}:
      {==}
    case C.EUnit{}:
      {==}
    case C.EPair{a, b}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {C.h.pair(_, C.eval.h(C.cc(b), env)) == C.h.pair(C.ev(a, env), C.ev(b, env)) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(b), env), C.ev(b, env), P.cc.ok(b, env)) : {C.h.pair(C.ev(a, env), _) == C.h.pair(C.ev(a, env), C.ev(b, env)) : Maybe<&2, C.HV>}
      {==}
    case C.EFst{a}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, _, y => C.h.fst(y)) == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => C.h.fst(v)) : Maybe<&2, C.HV>}
      {==}
    case C.ESnd{a}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, _, y => C.h.snd(y)) == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => C.h.snd(v)) : Maybe<&2, C.HV>}
      {==}
    case C.EInl{a}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, _, y => Some{C.HvInl{y}}) == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => Some{C.HvInl{v}}) : Maybe<&2, C.HV>}
      {==}
    case C.EInr{a}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, _, y => Some{C.HvInr{y}}) == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => Some{C.HvInr{v}}) : Maybe<&2, C.HV>}
      {==}
    case C.ENil{}:
      {==}
    case C.ECons{a, b}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {C.h.cons(_, C.eval.h(C.cc(b), env)) == C.h.cons(C.ev(a, env), C.ev(b, env)) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(b), env), C.ev(b, env), P.cc.ok(b, env)) : {C.h.cons(C.ev(a, env), _) == C.h.cons(C.ev(a, env), C.ev(b, env)) : Maybe<&2, C.HV>}
      {==}
    case C.EPrim{p, a, b}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, C.h.pair(_, C.eval.h(C.cc(b), env)), y => C.h.prim(p, y)) == Maybe.bind(&2, C.HV, C.HV, C.h.pair(C.ev(a, env), C.ev(b, env)), v => C.h.prim(p, v)) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(b), env), C.ev(b, env), P.cc.ok(b, env)) : {Maybe.bind(&2, C.HV, C.HV, C.h.pair(C.ev(a, env), _), y => C.h.prim(p, y)) == Maybe.bind(&2, C.HV, C.HV, C.h.pair(C.ev(a, env), C.ev(b, env)), v => C.h.prim(p, v)) : Maybe<&2, C.HV>}
      {==}
    case C.EIf{c, a, e}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(c), env), C.ev(c, env), P.cc.ok(c, env)) : {C.h.if(_, C.eval.h(C.cc(a), env), C.eval.h(C.cc(e), env)) == C.h.if(C.ev(c, env), C.ev(a, env), C.ev(e, env)) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {C.h.if(C.ev(c, env), _, C.eval.h(C.cc(e), env)) == C.h.if(C.ev(c, env), C.ev(a, env), C.ev(e, env)) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(e), env), C.ev(e, env), P.cc.ok(e, env)) : {C.h.if(C.ev(c, env), C.ev(a, env), _) == C.h.if(C.ev(c, env), C.ev(a, env), C.ev(e, env)) : Maybe<&2, C.HV>}
      {==}
    case C.ELet{a, b}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(a), env), C.ev(a, env), P.cc.ok(a, env)) : {Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{env}, _), y => C.eval.h(C.cc(b), y)) == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => C.ev(b, C.HvPair{env, v})) : Maybe<&2, C.HV>}
      %Equal.sym(Maybe<&2, C.HV>, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{env}, C.ev(a, env)), y => C.eval.h(C.cc(b), y)), Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => C.eval.h(C.cc(b), C.HvPair{env, v})), L.cc.let(C.ev(a, env), env, y => C.eval.h(C.cc(b), y))) : {_ == Maybe.bind(&2, C.HV, C.HV, C.ev(a, env), v => C.ev(b, C.HvPair{env, v})) : Maybe<&2, C.HV>}
      L.hh.bind(C.ev(a, env), v => C.eval.h(C.cc(b), C.HvPair{env, v}), v => C.ev(b, C.HvPair{env, v}), v => P.cc.ok(b, C.HvPair{env, v}))
    case C.ECase{l, r}:
      match env:
        case C.HvPair{e, q}:
          match q:
            case C.HvInl{a}:
              P.cc.ok(l, C.HvPair{e, a})
            case C.HvInr{b}:
              P.cc.ok(r, C.HvPair{e, b})
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
        case C.HvCons{h, tl}:
          {==}
    case C.EFold{z, s}:
      match env:
        case C.HvPair{+e, l}:
          match l:
            case C.HvNil{}:
              P.cc.ok(z, e)
            case C.HvCons{+hd, tl}:
              %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc(t), C.HvPair{e, tl}), C.ev(t, C.HvPair{e, tl}), P.cc.ok(t, C.HvPair{e, tl})) : {Maybe.bind(&2, C.HV, C.HV, _, q => C.eval.h(C.cc(s), C.HvPair{C.HvPair{e, hd}, q})) == Maybe.bind(&2, C.HV, C.HV, C.ev(t, C.HvPair{e, tl}), q => C.ev(s, C.HvPair{C.HvPair{e, hd}, q})) : Maybe<&2, C.HV>}
              L.hh.bind(C.ev(t, C.HvPair{e, tl}), q => C.eval.h(C.cc(s), C.HvPair{C.HvPair{e, hd}, q}), q => C.ev(s, C.HvPair{C.HvPair{e, hd}, q}), q => P.cc.ok(s, C.HvPair{C.HvPair{e, hd}, q}))
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
        case C.HvCons{h, tl}:
          {==}
    case C.EErr{}:
      {==}

def P.cc.def.ok(t, x):
  P.cc.ok(t, C.HvPair{C.HvUnit{}, x})

def P.cc.F(t, x):
  %P.cc.def.ok(t, x) : {C.encM(_) == C.eval.b(C.F(C.cc.def(t)), C.enc(x)) : Maybe<&2, C.BV>}
  P.sq.F(C.cc.def(t), x)

# the def's answer is its program's
def L.ex.to(+t: C.Ex, +x: C.HV, -v: C.HV, e: {C.ev.def(t, x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.cc.def(t), x) == Some{v} : Maybe<&2, C.HV>}:
  %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.cc.def(t), x), C.ev.def(t, x), P.cc.def.ok(t, x)) : {_ == Some{v} : Maybe<&2, C.HV>}
  e

def L.ex.of(+t: C.Ex, +x: C.HV, -v: C.HV, e: {C.eval.h(C.cc.def(t), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.ev.def(t, x) == Some{v} : Maybe<&2, C.HV>}:
  %P.cc.def.ok(t, x) : {_ == Some{v} : Maybe<&2, C.HV>}
  e

def L.FGx.l(+t: C.Ex, +b: C.BTm, le: P.Le.b(C.F(C.cc.def(t)), b), +x: C.HV, +v: C.HV, e: {C.ev.def(t, x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}:
  L.adj.l(C.cc.def(t), b, le, x, v, L.ex.to(t, x, v, e))

def P.adj.FG.ex.l(t, b, le):
  x => v => e => L.FGx.l(t, b, le, x, v, e)

def L.FGx.le(+t: C.Ex, +b: C.BTm, le: P.Le.ex.l(t, b), +x: C.HV, +v: C.HV, e: {C.eval.h(C.cc.def(t), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}:
  le(x, v, L.ex.of(t, x, v, e))

def P.adj.FG.ex.r(t, b, le):
  P.adj.FG.r(C.cc.def(t), b, x => v => e => L.FGx.le(t, b, le, x, v, e))

def L.GFx.le(+t: C.Ex, +b: C.BTm, le: P.Le.ex.r(b, t), +x: C.HV, +v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.h(C.cc.def(t), x) == Some{v} : Maybe<&2, C.HV>}:
  L.ex.to(t, x, v, le(x, v, e))

def P.adj.GF.ex.l(t, b, le):
  P.adj.GF.l(C.cc.def(t), b, x => v => e => L.GFx.le(t, b, le, x, v, e))

def L.GFx.r(+t: C.Ex, +b: C.BTm, le: P.Le.b(b, C.F(C.cc.def(t))), +x: C.HV, +v: C.HV, e: {C.eval.h(C.G(b), x) == Some{v} : Maybe<&2, C.HV>}) -> {C.ev.def(t, x) == Some{v} : Maybe<&2, C.HV>}:
  L.ex.of(t, x, v, L.adj2.r(C.cc.def(t), b, le, x, v, e))

def P.adj.GF.ex.r(t, b, le):
  x => v => e => L.GFx.r(t, b, le, x, v, e)

# 12. Subtraction a test makes safe

# at two numbers, the test's answer c (Nat.is_lt(m, n)) decides both
# Haskell's and Bend's (-)
def L.gp.fc(c: Bool, +m: Nat, +n: Nat, +v: C.HV, th: Maybe<&2, C.HV>, +d: C.HTm) -> {C.encM(C.h.if(Some{C.HvBool{c}}, th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, C.h.pv(C.p.of(C.p.lt.at(c, m, n)))), w => C.eval.h(d, w)))) == C.b.if(Some{C.BvBool{c}}, C.encM(th), Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Some{C.BvNat{Nat.sub(m, n)}}), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}:
  match c:
    case True{}:
      {==}
    case False{}:
      P.sq.F(d, C.HvPair{v, C.HvNat{Nat.sub(m, n)}})

def L.gp.f2(a: C.HV, b: C.HV, +v: C.HV, +th: Maybe<&2, C.HV>, +d: C.HTm) -> {C.encM(C.h.if(Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{a}, Some{b}), w => C.h.prim(C.PLt{}, w)), th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{a}, Some{b}), w => C.h.prim(C.PSub{}, w))), w => C.eval.h(d, w)))) == C.b.if(Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(Some{a}), C.encM(Some{b})), w => C.b.prim(C.PLt{}, w)), C.encM(th), Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(Some{a}), C.encM(Some{b})), w => C.b.prim(C.PSubT{}, w))), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}:
  match a:
    case C.HvNat{+m}:
      match b:
        case C.HvNat{+n}:
          L.gp.fc(Nat.is_lt(m, n), m, n, v, th, d)
        case C.HvBool{q}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{p, q}:
          {==}
        case C.HvInl{q}:
          {==}
        case C.HvInr{q}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{p, q}:
          {==}
    case C.HvBool{q}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{p, q}:
      {==}
    case C.HvInl{q}:
      {==}
    case C.HvInr{q}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{p, q}:
      {==}

def L.gp.f(X: Maybe<&2, C.HV>, Y: Maybe<&2, C.HV>, +v: C.HV, +th: Maybe<&2, C.HV>, +d: C.HTm) -> {C.encM(C.h.if(Maybe.bind(&2, C.HV, C.HV, C.h.pair(X, Y), w => C.h.prim(C.PLt{}, w)), th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, Maybe.bind(&2, C.HV, C.HV, C.h.pair(X, Y), w => C.h.prim(C.PSub{}, w))), w => C.eval.h(d, w)))) == C.b.if(Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(X), C.encM(Y)), w => C.b.prim(C.PLt{}, w)), C.encM(th), Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(X), C.encM(Y)), w => C.b.prim(C.PSubT{}, w))), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}:
  match X:
    case None{}:
      {==}
    case Some{a}:
      match Y:
        case None{}:
          {==}
        case Some{b}:
          L.gp.f2(a, b, v, th, d)

def P.gap.F(x, y, t, d, v):
  %P.sq.F(x, v) : {C.encM(C.eval.h(C.h.gap(x, y, t, d), v)) == C.b.if(Maybe.bind(&2, C.BV, C.BV, C.b.pair(_, C.eval.b(C.F(y), C.enc(v))), w => C.b.prim(C.PLt{}, w)), C.eval.b(C.F(t), C.enc(v)), Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Maybe.bind(&2, C.BV, C.BV, C.b.pair(_, C.eval.b(C.F(y), C.enc(v))), w => C.b.prim(C.PSubT{}, w))), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}
  %P.sq.F(y, v) : {C.encM(C.eval.h(C.h.gap(x, y, t, d), v)) == C.b.if(Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(C.eval.h(x, v)), _), w => C.b.prim(C.PLt{}, w)), C.eval.b(C.F(t), C.enc(v)), Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(C.eval.h(x, v)), _), w => C.b.prim(C.PSubT{}, w))), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}
  %P.sq.F(t, v) : {C.encM(C.eval.h(C.h.gap(x, y, t, d), v)) == C.b.if(Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(C.eval.h(x, v)), C.encM(C.eval.h(y, v))), w => C.b.prim(C.PLt{}, w)), _, Maybe.bind(&2, C.BV, C.BV, C.b.pair(Some{C.enc(v)}, Maybe.bind(&2, C.BV, C.BV, C.b.pair(C.encM(C.eval.h(x, v)), C.encM(C.eval.h(y, v))), w => C.b.prim(C.PSubT{}, w))), w => C.eval.b(C.F(d), w))) : Maybe<&2, C.BV>}
  L.gp.f(C.eval.h(x, v), C.eval.h(y, v), v, C.eval.h(t, v), d)

def L.gp.zc(c: Bool, +m: Nat, +n: Nat, +v: C.HV, th: Maybe<&2, C.HV>, +d: C.HTm, ad: P.Agree(d, w => C.eval.z(d, w))) -> {C.z.if(Some{C.ZvBool{c}}, C.upM(th), Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Some{C.z.minus.at(c, m, n)}), w => C.eval.z(d, w))) == C.upM(C.h.if(Some{C.HvBool{c}}, th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, C.h.pv(C.p.of(C.p.lt.at(c, m, n)))), w => C.eval.h(d, w)))) : Maybe<&2, C.ZV>}:
  match c:
    case True{}:
      {==}
    case False{}:
      ad(C.HvPair{v, C.HvNat{Nat.sub(m, n)}})

def L.gp.z2(a: C.HV, b: C.HV, +v: C.HV, +th: Maybe<&2, C.HV>, +d: C.HTm, ad: P.Agree(d, w => C.eval.z(d, w))) -> {C.z.if(Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(Some{a}), C.upM(Some{b})), w => C.z.prim(C.PLt{}, w)), C.upM(th), Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(Some{a}), C.upM(Some{b})), w => C.z.prim(C.PSub{}, w))), w => C.eval.z(d, w))) == C.upM(C.h.if(Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{a}, Some{b}), w => C.h.prim(C.PLt{}, w)), th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{a}, Some{b}), w => C.h.prim(C.PSub{}, w))), w => C.eval.h(d, w)))) : Maybe<&2, C.ZV>}:
  match a:
    case C.HvNat{+m}:
      match b:
        case C.HvNat{+n}:
          L.gp.zc(Nat.is_lt(m, n), m, n, v, th, d, ad)
        case C.HvBool{q}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvPair{p, q}:
          {==}
        case C.HvInl{q}:
          {==}
        case C.HvInr{q}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{p, q}:
          {==}
    case C.HvBool{q}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvPair{p, q}:
      {==}
    case C.HvInl{q}:
      {==}
    case C.HvInr{q}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{p, q}:
      {==}

def L.gp.z(X: Maybe<&2, C.HV>, Y: Maybe<&2, C.HV>, +v: C.HV, +th: Maybe<&2, C.HV>, +d: C.HTm, ad: P.Agree(d, w => C.eval.z(d, w))) -> {C.z.if(Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(X), C.upM(Y)), w => C.z.prim(C.PLt{}, w)), C.upM(th), Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(X), C.upM(Y)), w => C.z.prim(C.PSub{}, w))), w => C.eval.z(d, w))) == C.upM(C.h.if(Maybe.bind(&2, C.HV, C.HV, C.h.pair(X, Y), w => C.h.prim(C.PLt{}, w)), th, Maybe.bind(&2, C.HV, C.HV, C.h.pair(Some{v}, Maybe.bind(&2, C.HV, C.HV, C.h.pair(X, Y), w => C.h.prim(C.PSub{}, w))), w => C.eval.h(d, w)))) : Maybe<&2, C.ZV>}:
  match X:
    case None{}:
      {==}
    case Some{a}:
      match Y:
        case None{}:
          {==}
        case Some{b}:
          L.gp.z2(a, b, v, th, d, ad)

def L.gp.ag(+x: C.HTm, +y: C.HTm, +t: C.HTm, +d: C.HTm, +ex: {C.nosub(x) == True{} : Bool}, +ey: {C.nosub(y) == True{} : Bool}, at: P.Agree(t, w => C.eval.z(t, w)), ad: P.Agree(d, w => C.eval.z(d, w)), +v: C.HV) -> {C.eval.z(C.h.gap(x, y, t, d), C.up(v)) == C.upM(C.eval.h(C.h.gap(x, y, t, d), v)) : Maybe<&2, C.ZV>}:
  %L.agree(x, ex, v) : {C.z.if(Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(_, C.eval.z(y, C.up(v))), w => C.z.prim(C.PLt{}, w)), C.eval.z(t, C.up(v)), Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(_, C.eval.z(y, C.up(v))), w => C.z.prim(C.PSub{}, w))), w => C.eval.z(d, w))) == C.upM(C.eval.h(C.h.gap(x, y, t, d), v)) : Maybe<&2, C.ZV>}
  %L.agree(y, ey, v) : {C.z.if(Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(C.eval.h(x, v)), _), w => C.z.prim(C.PLt{}, w)), C.eval.z(t, C.up(v)), Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(C.eval.h(x, v)), _), w => C.z.prim(C.PSub{}, w))), w => C.eval.z(d, w))) == C.upM(C.eval.h(C.h.gap(x, y, t, d), v)) : Maybe<&2, C.ZV>}
  %Equal.sym(Maybe<&2, C.ZV>, C.eval.z(t, C.up(v)), C.upM(C.eval.h(t, v)), at(v)) : {C.z.if(Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(C.eval.h(x, v)), C.upM(C.eval.h(y, v))), w => C.z.prim(C.PLt{}, w)), _, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(Some{C.up(v)}, Maybe.bind(&2, C.ZV, C.ZV, C.z.pair(C.upM(C.eval.h(x, v)), C.upM(C.eval.h(y, v))), w => C.z.prim(C.PSub{}, w))), w => C.eval.z(d, w))) == C.upM(C.eval.h(C.h.gap(x, y, t, d), v)) : Maybe<&2, C.ZV>}
  L.gp.z(C.eval.h(x, v), C.eval.h(y, v), v, C.eval.h(t, v), d, ad)

def P.gap.agree(x, y, t, d, ex, ey, at, ad):
  v => L.gp.ag(x, y, t, d, ex, ey, at, ad, v)

# at w = enc(dec(w)): both are Haskell's meaning of the program at dec(w)
def P.gap.same(x, y, t, d, w):
  %P.enc.dec(w) : {C.eval.b(C.F(C.h.gap(x, y, t, d)), _) == C.eval.b(C.F.gap(x, y, t, d), _) : Maybe<&2, C.BV>}
  %P.sq.F(C.h.gap(x, y, t, d), C.dec(w)) : {_ == C.eval.b(C.F.gap(x, y, t, d), C.enc(C.dec(w))) : Maybe<&2, C.BV>}
  P.gap.F(x, y, t, d, C.dec(w))

def L.gp.to(+x: C.HTm, +y: C.HTm, +t: C.HTm, +d: C.HTm, +w: C.BV, -u: C.BV, e: {C.eval.b(C.F(C.h.gap(x, y, t, d)), w) == Some{u} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F.gap(x, y, t, d), w) == Some{u} : Maybe<&2, C.BV>}:
  %P.gap.same(x, y, t, d, w) : {_ == Some{u} : Maybe<&2, C.BV>}
  e

def L.gp.of(+x: C.HTm, +y: C.HTm, +t: C.HTm, +d: C.HTm, +w: C.BV, -u: C.BV, e: {C.eval.b(C.F.gap(x, y, t, d), w) == Some{u} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F(C.h.gap(x, y, t, d)), w) == Some{u} : Maybe<&2, C.BV>}:
  %Equal.sym(Maybe<&2, C.BV>, C.eval.b(C.F(C.h.gap(x, y, t, d)), w), C.eval.b(C.F.gap(x, y, t, d), w), P.gap.same(x, y, t, d, w)) : {_ == Some{u} : Maybe<&2, C.BV>}
  e

def L.gp.gl(+x: C.HTm, +y: C.HTm, +t: C.HTm, +d: C.HTm, +ex: {C.nosub(x) == True{} : Bool}, +ey: {C.nosub(y) == True{} : Bool}, at: P.Agree(t, w => C.eval.z(t, w)), ad: P.Agree(d, w => C.eval.z(d, w)), +b: C.BTm, le: P.Le.z(z => C.gz(b, z), w => C.eval.z(C.h.gap(x, y, t, d), w)), +w: C.BV, +u: C.BV, e: {C.eval.b(b, w) == Some{u} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F.gap(x, y, t, d), w) == Some{u} : Maybe<&2, C.BV>}:
  L.gp.to(x, y, t, d, w, u, P.adj.GF.int.l(C.h.gap(x, y, t, d), b, v => C.eval.z(C.h.gap(x, y, t, d), v), P.gap.agree(x, y, t, d, ex, ey, at, ad), le, w, u, e))

def P.adj.GF.gap.l(x, y, t, d, ex, ey, at, ad, b, le):
  w => u => e => L.gp.gl(x, y, t, d, ex, ey, at, ad, b, le, w, u, e)

def L.gp.le(+x: C.HTm, +y: C.HTm, +t: C.HTm, +d: C.HTm, +b: C.BTm, le: P.Le.b(b, C.F.gap(x, y, t, d)), +w: C.BV, +u: C.BV, e: {C.eval.b(b, w) == Some{u} : Maybe<&2, C.BV>}) -> {C.eval.b(C.F(C.h.gap(x, y, t, d)), w) == Some{u} : Maybe<&2, C.BV>}:
  L.gp.of(x, y, t, d, w, u, le(w, u, e))

def P.adj.GF.gap.r(x, y, t, d, ex, ey, at, ad, b, le):
  P.adj.GF.int.r(C.h.gap(x, y, t, d), b, v => C.eval.z(C.h.gap(x, y, t, d), v), P.gap.agree(x, y, t, d, ex, ey, at, ad), w => u => e => L.gp.le(x, y, t, d, b, le, w, u, e))

def P.gap.not():
  {==}

def P.gap.not.F():
  {==}

# 13. data types and their catamorphisms

# h : t's cata, once its tail's is m
def L.fc(m: Maybe<&2, C.HV>, +h: C.HV, +z: C.HTm, +s: C.HTm) -> {Maybe.bind(&2, C.HV, C.HV, m, r => C.eval.h(s, C.HvPair{h, r})) == Maybe.bind(&2, C.HV, C.HV, C.h.cons(m, Some{C.HvNil{}}), rs => C.eval.h(C.lalg(z, s), C.HvPair{C.HvInr{h}, rs})) : Maybe<&2, C.HV>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      {==}

def P.foldr.cata(z, s, x):
  match x:
    case C.HvNil{}:
      {==}
    case C.HvCons{h, t}:
      %Equal.sym(Maybe<&2, C.HV>, C.eval.h(C.HFold{z, s}, t), C.eval.h(C.HCata{C.lalg(z, s)}, C.lrose(t)), P.foldr.cata(z, s, t)) : {Maybe.bind(&2, C.HV, C.HV, _, r => C.eval.h(s, C.HvPair{h, r})) == C.eval.h(C.HCata{C.lalg(z, s)}, C.lrose(C.HvCons{h, t})) : Maybe<&2, C.HV>}
      L.fc(C.eval.h(C.HCata{C.lalg(z, s)}, C.lrose(t)), h, z, s)
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

# 14. Definitions that call each other, and functions as values

def P.F.r.comp(g, f):
  {==}

def P.F.r.call(i):
  {==}

def P.F.r.app():
  {==}

def P.F.r.clo(i):
  {==}

def P.F.r.link(ds, es):
  match ds:
    case C.HdNil{}:
      {==}
    case C.HdCons{t, d, fs}:
      %P.F.r.link(fs, es) : {C.BdCons{C.F.hr(t), C.enc(d), C.F.hd(C.hd.app(fs, es))} == C.BdCons{C.F.hr(t), C.enc(d), _} : C.BD}
      {==}

def P.G.r.comp(g, f):
  {==}

def P.G.r.clo(i):
  {==}

def P.G.r.link(ds, es):
  match ds:
    case C.BdNil{}:
      {==}
    case C.BdCons{t, d, fs}:
      %P.G.r.link(fs, es) : {C.HdCons{C.G.br(t), C.dec(d), C.G.bd(C.bd.app(fs, es))} == C.HdCons{C.G.br(t), C.dec(d), _} : C.HD}
      {==}

def P.curry.app(n, ds, i, e, a):
  {==}

def P.F.malg(s1, s2):
  {==}

def P.mcata.l(s1, s2, l, ks):
  {==}

def P.mcata.r(s1, s2, l, ks):
  {==}

# a definition's translation, and its default's
def L.hd.F(ds: C.HD, i: Nat) -> {C.F.hr(C.hd.at(ds, i)) == C.bd.at(C.F.hd(ds), i) : C.BR}:
  match ds i:
    case C.HdNil{} _:
      {==}
    case C.HdCons{t, d, es} 0n:
      {==}
    case C.HdCons{t, d, es} 1n+j:
      L.hd.F(es, j)

# agreement of a run and an answer (L.agR), through what puts runs together
def L.ag.bind(R: C.Run, -m: Maybe<&2, C.BV>, -kh: C.HV -> C.Run, -kb: C.BV -> Maybe<&2, C.BV>, a: L.agR(R, m), ih: @v: C.HV -> L.agR(kh(v), kb(C.enc(v)))) -> L.agR(C.r.bind(R, kh), Maybe.bind(&2, C.BV, C.BV, m, kb)):
  match R:
    case C.ROut{}:
      Unit{}
    case C.RDone{r}:
      match r:
        case None{}:
          %a : {None{} == Maybe.bind(&2, C.BV, C.BV, _, kb) : Maybe<&2, C.BV>}
          {==}
        case Some{v}:
          %a : L.agR(kh(v), Maybe.bind(&2, C.BV, C.BV, _, kb))
          ih(v)

def L.pair.none(m: Maybe<&2, C.BV>) -> {None{} == C.b.pair(None{}, m) : Maybe<&2, C.BV>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def L.cons.none(m: Maybe<&2, C.BV>) -> {None{} == C.b.cons(None{}, m) : Maybe<&2, C.BV>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def L.ag.pair(R1: C.Run, R2: C.Run, -m1: Maybe<&2, C.BV>, m2: Maybe<&2, C.BV>, a1: L.agR(R1, m1), a2: L.agR(R2, m2)) -> L.agR(C.r.pair(R1, R2), C.b.pair(m1, m2)):
  match R1:
    case C.ROut{}:
      Unit{}
    case C.RDone{r}:
      match r:
        case None{}:
          %a1 : {None{} == C.b.pair(_, m2) : Maybe<&2, C.BV>}
          L.pair.none(m2)
        case Some{u}:
          match R2:
            case C.ROut{}:
              Unit{}
            case C.RDone{w}:
              %a1 : {C.encM(C.h.pair(Some{u}, w)) == C.b.pair(_, m2) : Maybe<&2, C.BV>}
              %a2 : {C.encM(C.h.pair(Some{u}, w)) == C.b.pair(Some{C.enc(u)}, _) : Maybe<&2, C.BV>}
              L.pair.F(Some{u}, w)

def L.ag.cons(R1: C.Run, R2: C.Run, -m1: Maybe<&2, C.BV>, m2: Maybe<&2, C.BV>, a1: L.agR(R1, m1), a2: L.agR(R2, m2)) -> L.agR(C.r.cons(R1, R2), C.b.cons(m1, m2)):
  match R1:
    case C.ROut{}:
      Unit{}
    case C.RDone{r}:
      match r:
        case None{}:
          %a1 : {None{} == C.b.cons(_, m2) : Maybe<&2, C.BV>}
          L.cons.none(m2)
        case Some{u}:
          match R2:
            case C.ROut{}:
              Unit{}
            case C.RDone{w}:
              %a1 : {C.encM(C.h.cons(Some{u}, w)) == C.b.cons(_, m2) : Maybe<&2, C.BV>}
              %a2 : {C.encM(C.h.cons(Some{u}, w)) == C.b.cons(Some{C.enc(u)}, _) : Maybe<&2, C.BV>}
              L.cons.F(Some{u}, w)

def L.ag.if(Rc: C.Run, -Ra: C.Run, -Re: C.Run, -mc: Maybe<&2, C.BV>, -ma: Maybe<&2, C.BV>, -me: Maybe<&2, C.BV>, ac: L.agR(Rc, mc), aa: L.agR(Ra, ma), ae: L.agR(Re, me)) -> L.agR(C.r.if(Rc, Ra, Re), C.b.if(mc, ma, me)):
  match Rc:
    case C.ROut{}:
      Unit{}
    case C.RDone{r}:
      match r:
        case None{}:
          %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
          {==}
        case Some{v}:
          match v:
            case C.HvBool{b}:
              match b:
                case True{}:
                  %ac : L.agR(Ra, C.b.if(_, ma, me))
                  aa
                case False{}:
                  %ac : L.agR(Re, C.b.if(_, ma, me))
                  ae
            case C.HvNat{q}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvUnit{}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvPair{p, q}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvInl{p}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvInr{p}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvNil{}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}
            case C.HvCons{p, q}:
              %ac : {None{} == C.b.if(_, ma, me) : Maybe<&2, C.BV>}
              {==}

# what a body's construct computes to, whatever the depth
def L.hr.tm(n: Nat, +ds: C.HD, u: C.HTm, +x: C.HV) -> {C.RDone{C.eval.h(u, x)} == C.eval.hr(n, ds, C.HrTm{u}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.hr.comp(n: Nat, +ds: C.HD, g: C.HR, f: C.HR, +x: C.HV) -> {C.r.bind(C.eval.hr(n, ds, f, x), y => C.eval.hr(n, ds, g, y)) == C.eval.hr(n, ds, C.HrComp{g, f}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.hr.pr(n: Nat, +ds: C.HD, f: C.HR, g: C.HR, +x: C.HV) -> {C.r.pair(C.eval.hr(n, ds, f, x), C.eval.hr(n, ds, g, x)) == C.eval.hr(n, ds, C.HrPr{f, g}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.hr.case(n: Nat, +ds: C.HD, f: C.HR, g: C.HR, +x: C.HV) -> {C.r.case(x, a => C.eval.hr(n, ds, f, a), b => C.eval.hr(n, ds, g, b)) == C.eval.hr(n, ds, C.HrCase{f, g}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.hr.if(n: Nat, +ds: C.HD, c: C.HR, a: C.HR, e: C.HR, +x: C.HV) -> {C.r.if(C.eval.hr(n, ds, c, x), C.eval.hr(n, ds, a, x), C.eval.hr(n, ds, e, x)) == C.eval.hr(n, ds, C.HrIf{c, a, e}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.hr.cons(n: Nat, +ds: C.HD, a: C.HR, b: C.HR, +x: C.HV) -> {C.r.cons(C.eval.hr(n, ds, a, x), C.eval.hr(n, ds, b, x)) == C.eval.hr(n, ds, C.HrCons{a, b}, x) : C.Run}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.tm(n: Nat, +ds: C.BD, u: C.BTm, +y: C.BV) -> {C.eval.b(u, y) == C.eval.br(n, ds, C.BrTm{u}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.comp(n: Nat, +ds: C.BD, g: C.BR, f: C.BR, +y: C.BV) -> {Maybe.bind(&2, C.BV, C.BV, C.eval.br(n, ds, f, y), z => C.eval.br(n, ds, g, z)) == C.eval.br(n, ds, C.BrComp{g, f}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.pr(n: Nat, +ds: C.BD, f: C.BR, g: C.BR, +y: C.BV) -> {C.b.pair(C.eval.br(n, ds, f, y), C.eval.br(n, ds, g, y)) == C.eval.br(n, ds, C.BrPr{f, g}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.case(n: Nat, +ds: C.BD, f: C.BR, g: C.BR, +y: C.BV) -> {C.m.case(y, a => C.eval.br(n, ds, f, a), b => C.eval.br(n, ds, g, b)) == C.eval.br(n, ds, C.BrCase{f, g}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.if(n: Nat, +ds: C.BD, c: C.BR, a: C.BR, e: C.BR, +y: C.BV) -> {C.b.if(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y)) == C.eval.br(n, ds, C.BrIf{c, a, e}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.br.cons(n: Nat, +ds: C.BD, a: C.BR, b: C.BR, +y: C.BV) -> {C.b.cons(C.eval.br(n, ds, a, y), C.eval.br(n, ds, b, y)) == C.eval.br(n, ds, C.BrCons{a, b}, y) : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

# a case, and an application, agree where their parts do
def L.ag.case(x: C.HV, -f: C.HV -> C.Run, -g: C.HV -> C.Run, -f2: C.BV -> Maybe<&2, C.BV>, -g2: C.BV -> Maybe<&2, C.BV>, af: @a: C.HV -> L.agR(f(a), f2(C.enc(a))), ag: @b: C.HV -> L.agR(g(b), g2(C.enc(b)))) -> L.agR(C.r.case(x, f, g), C.m.case(C.enc(x), f2, g2)):
  match x:
    case C.HvInl{a}:
      af(a)
    case C.HvInr{b}:
      ag(b)
    case C.HvNat{q}:
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

def L.ag.app(x: C.HV, -k: Nat -> C.HV -> C.Run, -k2: Nat -> C.BV -> Maybe<&2, C.BV>, ak: @+i: Nat -> @v: C.HV -> L.agR(k(i, v), k2(i, C.enc(v)))) -> L.agR(C.r.app(x, k), C.m.app(C.enc(x), k2)):
  match x:
    case C.HvPair{p, a}:
      match p:
        case C.HvPair{c, e}:
          match c:
            case C.HvNat{i}:
              ak(i, C.HvPair{e, a})
            case C.HvBool{b}:
              {==}
            case C.HvUnit{}:
              {==}
            case C.HvPair{q, r}:
              {==}
            case C.HvInl{q}:
              {==}
            case C.HvInr{q}:
              {==}
            case C.HvNil{}:
              {==}
            case C.HvCons{q, r}:
              {==}
        case C.HvNat{q}:
          {==}
        case C.HvBool{b}:
          {==}
        case C.HvUnit{}:
          {==}
        case C.HvInl{q}:
          {==}
        case C.HvInr{q}:
          {==}
        case C.HvNil{}:
          {==}
        case C.HvCons{q, r}:
          {==}
    case C.HvNat{q}:
      {==}
    case C.HvBool{b}:
      {==}
    case C.HvUnit{}:
      {==}
    case C.HvInl{q}:
      {==}
    case C.HvInr{q}:
      {==}
    case C.HvNil{}:
      {==}
    case C.HvCons{q, r}:
      {==}

# an application out of depth agrees with any answer
def L.ag.app0(x: C.HV, -k2: Nat -> C.BV -> Maybe<&2, C.BV>) -> L.agR(C.r.app(x, i => y => C.ROut{}), C.m.app(C.enc(x), k2)):
  L.ag.app(x, i => y => C.ROut{}, k2, i => v => Unit{})

def L.rec.at(-j: Nat, -m: Nat, +ds: C.HD, i: Nat, -v: C.HV, a: L.agR(C.eval.hr(j, ds, C.hd.at(ds, i), v), C.eval.br(m, C.F.hd(ds), C.F.hr(C.hd.at(ds, i)), C.enc(v)))) -> L.agR(C.eval.hr(j, ds, C.hd.at(ds, i), v), C.eval.br(m, C.F.hd(ds), C.bd.at(C.F.hd(ds), i), C.enc(v))):
  %L.hd.F(ds, i) : L.agR(C.eval.hr(j, ds, C.hd.at(ds, i), v), C.eval.br(m, C.F.hd(ds), _, C.enc(v)))
  a

# F's program agrees with h's, by induction on the depth of calls and the
# program
def L.rec.F(k: Nat, n: Nat, +ds: C.HD, t: C.HR, +x: C.HV, +le: {C.le(k, n) == True{} : Bool}) -> L.agR(C.eval.hr(k, ds, t, x), C.eval.br(n, C.F.hd(ds), C.F.hr(t), C.enc(x))):
  match k n t:
    case k n C.HrTm{+u}:
      %L.hr.tm(k, ds, u, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrTm{C.F(u)}, C.enc(x)))
      %L.br.tm(n, C.F.hd(ds), C.F(u), C.enc(x)) : L.agR(C.RDone{C.eval.h(u, x)}, _)
      P.sq.F(u, x)
    case +k +n C.HrComp{+g, +f}:
      %L.hr.comp(k, ds, g, f, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrComp{C.F.hr(g), C.F.hr(f)}, C.enc(x)))
      %L.br.comp(n, C.F.hd(ds), C.F.hr(g), C.F.hr(f), C.enc(x)) : L.agR(C.r.bind(C.eval.hr(k, ds, f, x), y => C.eval.hr(k, ds, g, y)), _)
      L.ag.bind(C.eval.hr(k, ds, f, x), C.eval.br(n, C.F.hd(ds), C.F.hr(f), C.enc(x)), y => C.eval.hr(k, ds, g, y), z => C.eval.br(n, C.F.hd(ds), C.F.hr(g), z), L.rec.F(k, n, ds, f, x, le), v => L.rec.F(k, n, ds, g, v, le))
    case +k +n C.HrPr{+f, +g}:
      %L.hr.pr(k, ds, f, g, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrPr{C.F.hr(f), C.F.hr(g)}, C.enc(x)))
      %L.br.pr(n, C.F.hd(ds), C.F.hr(f), C.F.hr(g), C.enc(x)) : L.agR(C.r.pair(C.eval.hr(k, ds, f, x), C.eval.hr(k, ds, g, x)), _)
      L.ag.pair(C.eval.hr(k, ds, f, x), C.eval.hr(k, ds, g, x), C.eval.br(n, C.F.hd(ds), C.F.hr(f), C.enc(x)), C.eval.br(n, C.F.hd(ds), C.F.hr(g), C.enc(x)), L.rec.F(k, n, ds, f, x, le), L.rec.F(k, n, ds, g, x, le))
    case +k +n C.HrCase{+f, +g}:
      %L.hr.case(k, ds, f, g, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrCase{C.F.hr(f), C.F.hr(g)}, C.enc(x)))
      %L.br.case(n, C.F.hd(ds), C.F.hr(f), C.F.hr(g), C.enc(x)) : L.agR(C.r.case(x, a => C.eval.hr(k, ds, f, a), b => C.eval.hr(k, ds, g, b)), _)
      L.ag.case(x, a => C.eval.hr(k, ds, f, a), b => C.eval.hr(k, ds, g, b), a => C.eval.br(n, C.F.hd(ds), C.F.hr(f), a), b => C.eval.br(n, C.F.hd(ds), C.F.hr(g), b), a => L.rec.F(k, n, ds, f, a, le), b => L.rec.F(k, n, ds, g, b, le))
    case +k +n C.HrIf{+c, +a, +e}:
      %L.hr.if(k, ds, c, a, e, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrIf{C.F.hr(c), C.F.hr(a), C.F.hr(e)}, C.enc(x)))
      %L.br.if(n, C.F.hd(ds), C.F.hr(c), C.F.hr(a), C.F.hr(e), C.enc(x)) : L.agR(C.r.if(C.eval.hr(k, ds, c, x), C.eval.hr(k, ds, a, x), C.eval.hr(k, ds, e, x)), _)
      L.ag.if(C.eval.hr(k, ds, c, x), C.eval.hr(k, ds, a, x), C.eval.hr(k, ds, e, x), C.eval.br(n, C.F.hd(ds), C.F.hr(c), C.enc(x)), C.eval.br(n, C.F.hd(ds), C.F.hr(a), C.enc(x)), C.eval.br(n, C.F.hd(ds), C.F.hr(e), C.enc(x)), L.rec.F(k, n, ds, c, x, le), L.rec.F(k, n, ds, a, x, le), L.rec.F(k, n, ds, e, x, le))
    case +k +n C.HrCons{+a, +b}:
      %L.hr.cons(k, ds, a, b, x) : L.agR(_, C.eval.br(n, C.F.hd(ds), C.BrCons{C.F.hr(a), C.F.hr(b)}, C.enc(x)))
      %L.br.cons(n, C.F.hd(ds), C.F.hr(a), C.F.hr(b), C.enc(x)) : L.agR(C.r.cons(C.eval.hr(k, ds, a, x), C.eval.hr(k, ds, b, x)), _)
      L.ag.cons(C.eval.hr(k, ds, a, x), C.eval.hr(k, ds, b, x), C.eval.br(n, C.F.hd(ds), C.F.hr(a), C.enc(x)), C.eval.br(n, C.F.hd(ds), C.F.hr(b), C.enc(x)), L.rec.F(k, n, ds, a, x, le), L.rec.F(k, n, ds, b, x, le))
    case 0n _ C.HrCall{i}:
      Unit{}
    case 1n+j 0n C.HrCall{i}:
      Empty.absurd(L.agR(C.eval.hr(1n+j, ds, C.HrCall{i}, x), C.eval.br(0n, C.F.hd(ds), C.BrCall{i}, C.enc(x))), L.ft(le))
    case 1n+j 1n+m C.HrCall{+i}:
      %L.hd.F(ds, i) : L.agR(C.eval.hr(j, ds, C.hd.at(ds, i), x), C.eval.br(m, C.F.hd(ds), _, C.enc(x)))
      L.rec.F(j, m, ds, C.hd.at(ds, i), x, le)
    case 0n 0n C.HrApp{}:
      L.ag.app0(x, i => z => Some{C.bd.dv(C.F.hd(ds), i)})
    case 0n 1n+m C.HrApp{}:
      L.ag.app0(x, i => z => C.eval.br(m, C.F.hd(ds), C.bd.at(C.F.hd(ds), i), z))
    case 1n+j 0n C.HrApp{}:
      Empty.absurd(L.agR(C.eval.hr(1n+j, ds, C.HrApp{}, x), C.eval.br(0n, C.F.hd(ds), C.BrApp{}, C.enc(x))), L.ft(le))
    case 1n+j 1n+m C.HrApp{}:
      L.ag.app(x, i => y => C.eval.hr(j, ds, C.hd.at(ds, i), y), i => z => C.eval.br(m, C.F.hd(ds), C.bd.at(C.F.hd(ds), i), z), +i => v => L.rec.at(j, m, ds, i, v, L.rec.F(j, m, ds, C.hd.at(ds, i), v, le)))

def P.sq.F.r(k, n, ds, t, x, r, e, le):
  L.agR.done(C.eval.hr(k, ds, t, x), C.eval.br(n, C.F.hd(ds), C.F.hr(t), C.enc(x)), r, e, L.rec.F(k, n, ds, t, x, le))

# the same for G: equal, whatever the fuel
def L.bd.G(ds: C.BD, i: Nat) -> {C.G.br(C.bd.at(ds, i)) == C.hd.at(C.G.bd(ds), i) : C.HR}:
  match ds i:
    case C.BdNil{} _:
      {==}
    case C.BdCons{t, d, es} 0n:
      {==}
    case C.BdCons{t, d, es} 1n+j:
      L.bd.G(es, j)

def L.dv.G(ds: C.BD, i: Nat) -> {C.dec(C.bd.dv(ds, i)) == C.hd.dv(C.G.bd(ds), i) : C.HV}:
  match ds i:
    case C.BdNil{} _:
      {==}
    case C.BdCons{t, d, es} 0n:
      {==}
    case C.BdCons{t, d, es} 1n+j:
      L.dv.G(es, j)

def L.gr.tm(n: Nat, +ds: C.HD, u: C.HTm, +x: C.HV) -> {C.eval.h(u, x) == C.eval.gr(n, ds, C.HrTm{u}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.gr.comp(n: Nat, +ds: C.HD, g: C.HR, f: C.HR, +x: C.HV) -> {Maybe.bind(&2, C.HV, C.HV, C.eval.gr(n, ds, f, x), y => C.eval.gr(n, ds, g, y)) == C.eval.gr(n, ds, C.HrComp{g, f}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.gr.pr(n: Nat, +ds: C.HD, f: C.HR, g: C.HR, +x: C.HV) -> {C.h.pair(C.eval.gr(n, ds, f, x), C.eval.gr(n, ds, g, x)) == C.eval.gr(n, ds, C.HrPr{f, g}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.gr.case(n: Nat, +ds: C.HD, f: C.HR, g: C.HR, +x: C.HV) -> {C.g.case(x, a => C.eval.gr(n, ds, f, a), b => C.eval.gr(n, ds, g, b)) == C.eval.gr(n, ds, C.HrCase{f, g}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.gr.if(n: Nat, +ds: C.HD, c: C.HR, a: C.HR, e: C.HR, +x: C.HV) -> {C.h.if(C.eval.gr(n, ds, c, x), C.eval.gr(n, ds, a, x), C.eval.gr(n, ds, e, x)) == C.eval.gr(n, ds, C.HrIf{c, a, e}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.gr.cons(n: Nat, +ds: C.HD, a: C.HR, b: C.HR, +x: C.HV) -> {C.h.cons(C.eval.gr(n, ds, a, x), C.eval.gr(n, ds, b, x)) == C.eval.gr(n, ds, C.HrCons{a, b}, x) : Maybe<&2, C.HV>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def L.case.G(y: C.BV, -f: C.BV -> Maybe<&2, C.BV>, -g: C.BV -> Maybe<&2, C.BV>, -f2: C.HV -> Maybe<&2, C.HV>, -g2: C.HV -> Maybe<&2, C.HV>, af: @a: C.BV -> {C.decM(f(a)) == f2(C.dec(a)) : Maybe<&2, C.HV>}, ag: @b: C.BV -> {C.decM(g(b)) == g2(C.dec(b)) : Maybe<&2, C.HV>}) -> {C.decM(C.m.case(y, f, g)) == C.g.case(C.dec(y), f2, g2) : Maybe<&2, C.HV>}:
  match y:
    case C.BvInl{a}:
      af(a)
    case C.BvInr{b}:
      ag(b)
    case C.BvNat{q}:
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

def L.app.G(y: C.BV, -k: Nat -> C.BV -> Maybe<&2, C.BV>, -k2: Nat -> C.HV -> Maybe<&2, C.HV>, ak: @+i: Nat -> @v: C.BV -> {C.decM(k(i, v)) == k2(i, C.dec(v)) : Maybe<&2, C.HV>}) -> {C.decM(C.m.app(y, k)) == C.g.app(C.dec(y), k2) : Maybe<&2, C.HV>}:
  match y:
    case C.BvPair{p, a}:
      match p:
        case C.BvPair{c, e}:
          match c:
            case C.BvNat{i}:
              ak(i, C.BvPair{e, a})
            case C.BvBool{b}:
              {==}
            case C.BvUnit{}:
              {==}
            case C.BvPair{q, r}:
              {==}
            case C.BvInl{q}:
              {==}
            case C.BvInr{q}:
              {==}
            case C.BvNil{}:
              {==}
            case C.BvCons{q, r}:
              {==}
        case C.BvNat{q}:
          {==}
        case C.BvBool{b}:
          {==}
        case C.BvUnit{}:
          {==}
        case C.BvInl{q}:
          {==}
        case C.BvInr{q}:
          {==}
        case C.BvNil{}:
          {==}
        case C.BvCons{q, r}:
          {==}
    case C.BvNat{q}:
      {==}
    case C.BvBool{b}:
      {==}
    case C.BvUnit{}:
      {==}
    case C.BvInl{q}:
      {==}
    case C.BvInr{q}:
      {==}
    case C.BvNil{}:
      {==}
    case C.BvCons{q, r}:
      {==}

def L.rec.atG(-m: Nat, +ds: C.BD, +i: Nat, -z: C.BV, a: {C.decM(C.eval.br(m, ds, C.bd.at(ds, i), z)) == C.eval.gr(m, C.G.bd(ds), C.G.br(C.bd.at(ds, i)), C.dec(z)) : Maybe<&2, C.HV>}) -> {C.decM(C.eval.br(m, ds, C.bd.at(ds, i), z)) == C.eval.gr(m, C.G.bd(ds), C.hd.at(C.G.bd(ds), i), C.dec(z)) : Maybe<&2, C.HV>}:
  %L.bd.G(ds, i) : {C.decM(C.eval.br(m, ds, C.bd.at(ds, i), z)) == C.eval.gr(m, C.G.bd(ds), _, C.dec(z)) : Maybe<&2, C.HV>}
  a

def L.dvM.G(ds: C.BD, i: Nat) -> {C.decM(Some{C.bd.dv(ds, i)}) == Some{C.hd.dv(C.G.bd(ds), i)} : Maybe<&2, C.HV>}:
  %L.dv.G(ds, i) : {Some{C.dec(C.bd.dv(ds, i))} == Some{_} : Maybe<&2, C.HV>}
  {==}

def P.sq.G.r(n, ds, t, y):
  match n t:
    case n C.BrTm{+u}:
      %L.br.tm(n, ds, u, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrTm{C.G(u)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.tm(n, C.G.bd(ds), C.G(u), C.dec(y)) : {C.decM(C.eval.b(u, y)) == _ : Maybe<&2, C.HV>}
      P.sq.G(u, y)
    case +n C.BrComp{+g, +f}:
      %L.br.comp(n, ds, g, f, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrComp{C.G.br(g), C.G.br(f)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.comp(n, C.G.bd(ds), C.G.br(g), C.G.br(f), C.dec(y)) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.br(n, ds, f, y), z => C.eval.br(n, ds, g, z))) == _ : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, f, y) : {C.decM(Maybe.bind(&2, C.BV, C.BV, C.eval.br(n, ds, f, y), z => C.eval.br(n, ds, g, z))) == Maybe.bind(&2, C.HV, C.HV, _, x => C.eval.gr(n, C.G.bd(ds), C.G.br(g), x)) : Maybe<&2, C.HV>}
      L.bind.G(C.eval.br(n, ds, f, y), z => C.eval.br(n, ds, g, z), x => C.eval.gr(n, C.G.bd(ds), C.G.br(g), x), w => P.sq.G.r(n, ds, g, w))
    case +n C.BrPr{+f, +g}:
      %L.br.pr(n, ds, f, g, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrPr{C.G.br(f), C.G.br(g)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.pr(n, C.G.bd(ds), C.G.br(f), C.G.br(g), C.dec(y)) : {C.decM(C.b.pair(C.eval.br(n, ds, f, y), C.eval.br(n, ds, g, y))) == _ : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, f, y) : {C.decM(C.b.pair(C.eval.br(n, ds, f, y), C.eval.br(n, ds, g, y))) == C.h.pair(_, C.eval.gr(n, C.G.bd(ds), C.G.br(g), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, g, y) : {C.decM(C.b.pair(C.eval.br(n, ds, f, y), C.eval.br(n, ds, g, y))) == C.h.pair(C.decM(C.eval.br(n, ds, f, y)), _) : Maybe<&2, C.HV>}
      L.pair.G(C.eval.br(n, ds, f, y), C.eval.br(n, ds, g, y))
    case +n C.BrCase{+f, +g}:
      %L.br.case(n, ds, f, g, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrCase{C.G.br(f), C.G.br(g)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.case(n, C.G.bd(ds), C.G.br(f), C.G.br(g), C.dec(y)) : {C.decM(C.m.case(y, a => C.eval.br(n, ds, f, a), b => C.eval.br(n, ds, g, b))) == _ : Maybe<&2, C.HV>}
      L.case.G(y, a => C.eval.br(n, ds, f, a), b => C.eval.br(n, ds, g, b), a => C.eval.gr(n, C.G.bd(ds), C.G.br(f), a), b => C.eval.gr(n, C.G.bd(ds), C.G.br(g), b), a => P.sq.G.r(n, ds, f, a), b => P.sq.G.r(n, ds, g, b))
    case +n C.BrIf{+c, +a, +e}:
      %L.br.if(n, ds, c, a, e, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrIf{C.G.br(c), C.G.br(a), C.G.br(e)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.if(n, C.G.bd(ds), C.G.br(c), C.G.br(a), C.G.br(e), C.dec(y)) : {C.decM(C.b.if(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y))) == _ : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, c, y) : {C.decM(C.b.if(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y))) == C.h.if(_, C.eval.gr(n, C.G.bd(ds), C.G.br(a), C.dec(y)), C.eval.gr(n, C.G.bd(ds), C.G.br(e), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, a, y) : {C.decM(C.b.if(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y))) == C.h.if(C.decM(C.eval.br(n, ds, c, y)), _, C.eval.gr(n, C.G.bd(ds), C.G.br(e), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, e, y) : {C.decM(C.b.if(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y))) == C.h.if(C.decM(C.eval.br(n, ds, c, y)), C.decM(C.eval.br(n, ds, a, y)), _) : Maybe<&2, C.HV>}
      L.if.G(C.eval.br(n, ds, c, y), C.eval.br(n, ds, a, y), C.eval.br(n, ds, e, y))
    case +n C.BrCons{+a, +b}:
      %L.br.cons(n, ds, a, b, y) : {C.decM(_) == C.eval.gr(n, C.G.bd(ds), C.HrCons{C.G.br(a), C.G.br(b)}, C.dec(y)) : Maybe<&2, C.HV>}
      %L.gr.cons(n, C.G.bd(ds), C.G.br(a), C.G.br(b), C.dec(y)) : {C.decM(C.b.cons(C.eval.br(n, ds, a, y), C.eval.br(n, ds, b, y))) == _ : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, a, y) : {C.decM(C.b.cons(C.eval.br(n, ds, a, y), C.eval.br(n, ds, b, y))) == C.h.cons(_, C.eval.gr(n, C.G.bd(ds), C.G.br(b), C.dec(y))) : Maybe<&2, C.HV>}
      %P.sq.G.r(n, ds, b, y) : {C.decM(C.b.cons(C.eval.br(n, ds, a, y), C.eval.br(n, ds, b, y))) == C.h.cons(C.decM(C.eval.br(n, ds, a, y)), _) : Maybe<&2, C.HV>}
      L.cons.G(C.eval.br(n, ds, a, y), C.eval.br(n, ds, b, y))
    case 0n C.BrCall{i}:
      L.dvM.G(ds, i)
    case 1n+m C.BrCall{+i}:
      L.rec.atG(m, ds, i, y, P.sq.G.r(m, ds, C.bd.at(ds, i), y))
    case 0n C.BrApp{}:
      L.app.G(y, i => z => Some{C.bd.dv(ds, i)}, i => x => Some{C.hd.dv(C.G.bd(ds), i)}, +i => z => L.dvM.G(ds, i))
    case 1n+m C.BrApp{}:
      L.app.G(y, i => z => C.eval.br(m, ds, C.bd.at(ds, i), z), i => x => C.eval.gr(m, C.G.bd(ds), C.hd.at(C.G.bd(ds), i), x), +i => z => L.rec.atG(m, ds, i, z, P.sq.G.r(m, ds, C.bd.at(ds, i), z)))

def L.det.v(r: Maybe<&2, C.HV>, +v: C.HV, e: {C.encM(r) == Some{C.enc(v)} : Maybe<&2, C.BV>}) -> {r == Some{v} : Maybe<&2, C.HV>}:
  %P.dec.enc(v) : {r == Some{_} : Maybe<&2, C.HV>}
  L.encM.inj(r, C.enc(v), e)

# h's answer is one: at the larger of the two depths F's program answers
# both
def L.max(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      b
    case 1n+i 0n:
      1n+i
    case 1n+i 1n+j:
      1n+L.max(i, j)

def L.le.maxl(a: Nat, b: Nat) -> {C.le(a, L.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+i 0n:
      L.le.refl(i)
    case 1n+i 1n+j:
      L.le.maxl(i, j)

def L.le.maxr(a: Nat, b: Nat) -> {C.le(b, L.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      L.le.refl(b)
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      L.le.maxr(i, j)

def P.det.r(k, k2, ds, t, x, v, r, e, f):
  L.det.v(r, v, Equal.trans(Maybe<&2, C.BV>, C.encM(r), C.eval.br(L.max(k, k2), C.F.hd(ds), C.F.hr(t), C.enc(x)), Some{C.enc(v)}, P.sq.F.r(k2, L.max(k, k2), ds, t, x, r, f, L.le.maxr(k, k2)), Equal.sym(Maybe<&2, C.BV>, Some{C.enc(v)}, C.eval.br(L.max(k, k2), C.F.hd(ds), C.F.hr(t), C.enc(x)), P.sq.F.r(k, L.max(k, k2), ds, t, x, Some{v}, e, L.le.maxl(k, k2)))))

# F -| G on the programs that stop within the fuel

def L.hp.F(+k: Nat, +n: Nat, h: C.HPg, +x: C.HV, -r: Maybe<&2, C.HV>, e: {C.eval.hp(k, h, x) == C.RDone{r} : C.Run}, +le: {C.le(k, n) == True{} : Bool}) -> {C.encM(r) == C.eval.bp(C.F.pn(n, h), C.enc(x)) : Maybe<&2, C.BV>}:
  match h:
    case C.HPg{ds, t}:
      P.sq.F.r(k, n, ds, t, x, r, e, le)

def L.bp.G(b: C.BPg, +y: C.BV) -> {C.decM(C.eval.bp(b, y)) == C.eval.gp(C.G.p(b), C.dec(y)) : Maybe<&2, C.HV>}:
  match b:
    case C.BPg{n, ds, t}:
      P.sq.G.r(n, ds, t, y)

def L.hp.det(+k: Nat, +k2: Nat, h: C.HPg, +x: C.HV, +v: C.HV, +r: Maybe<&2, C.HV>, e: {C.eval.hp(k, h, x) == C.RDone{Some{v}} : C.Run}, f: {C.eval.hp(k2, h, x) == C.RDone{r} : C.Run}) -> {r == Some{v} : Maybe<&2, C.HV>}:
  match h:
    case C.HPg{ds, t}:
      P.det.r(k, k2, ds, t, x, v, r, e, f)

# F's program answers h's answer, through enc, where h ends within its fuel
def L.rec.F.at(+n: Nat, +h: C.HPg, +x: C.HV, -v: C.HV, -a: Maybe<&2, C.HV>, eR: {C.eval.hp(n, h, x) == C.RDone{a} : C.Run}, ea: {a == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.bp(C.F.pn(n, h), C.enc(x)) == Some{C.enc(v)} : Maybe<&2, C.BV>}:
  %ea : {C.eval.bp(C.F.pn(n, h), C.enc(x)) == C.encM(_) : Maybe<&2, C.BV>}
  Equal.sym(Maybe<&2, C.BV>, C.encM(a), C.eval.bp(C.F.pn(n, h), C.enc(x)), L.hp.F(n, n, h, x, a, eR, L.le.refl(n)))

def L.rec.l(+n: Nat, +h: C.HPg, +b: C.BPg, le: P.Le.bp(C.F.pn(n, h), b), +x: C.HV, +v: C.HV, -a: Maybe<&2, C.HV>, eR: {C.eval.hp(n, h, x) == C.RDone{a} : C.Run}, ea: {a == Some{v} : Maybe<&2, C.HV>}) -> {C.eval.gp(C.G.p(b), x) == Some{v} : Maybe<&2, C.HV>}:
  %P.dec.enc(x) : {C.eval.gp(C.G.p(b), _) == Some{v} : Maybe<&2, C.HV>}
  %L.bp.G(b, C.enc(x)) : {_ == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(Maybe<&2, C.BV>, C.eval.bp(b, C.enc(x)), Some{C.enc(v)}, le(C.enc(x), C.enc(v), L.rec.F.at(n, h, x, v, a, eR, ea))) : {C.decM(_) == Some{v} : Maybe<&2, C.HV>}
  %Equal.sym(C.HV, C.dec(C.enc(v)), v, P.dec.enc(v)) : {Some{_} == Some{v} : Maybe<&2, C.HV>}
  {==}

# h's run at x, R: it ends (Stops), so with h's answer
def L.rec.l.at(+n: Nat, +h: C.HPg, +b: C.BPg, st: P.Stops.r(h, n), le: P.Le.bp(C.F.pn(n, h), b), +x: C.HV, +v: C.HV, +k: Nat, e: {C.eval.hp(k, h, x) == C.RDone{Some{v}} : C.Run}, R: C.Run, +eR: {C.eval.hp(n, h, x) == R : C.Run}) -> {C.eval.gp(C.G.p(b), x) == Some{v} : Maybe<&2, C.HV>}:
  match R:
    case C.ROut{}:
      Empty.absurd({C.eval.gp(C.G.p(b), x) == Some{v} : Maybe<&2, C.HV>}, st(x, eR))
    case C.RDone{+a}:
      L.rec.l(n, h, b, le, x, v, a, eR, L.hp.det(k, n, h, x, v, a, e, eR))

def L.rec.l.go(+n: Nat, +h: C.HPg, +b: C.BPg, st: P.Stops.r(h, n), le: P.Le.bp(C.F.pn(n, h), b), +x: C.HV, +v: C.HV, +k: Nat, e: {C.eval.hp(k, h, x) == C.RDone{Some{v}} : C.Run}) -> {C.eval.gp(C.G.p(b), x) == Some{v} : Maybe<&2, C.HV>}:
  L.rec.l.at(n, h, b, st, le, x, v, k, e, C.eval.hp(n, h, x), {==})

def P.adj.FG.rec.l(n, h, b, st, le):
  x => v => k => e => L.rec.l.go(n, h, b, st, le, x, v, k, e)

# h's answer at dec y, where F's program answers w at y
def L.rec.sqy(+n: Nat, +h: C.HPg, +y: C.BV, -a: Maybe<&2, C.HV>, eR: {C.eval.hp(n, h, C.dec(y)) == C.RDone{a} : C.Run}) -> {C.encM(a) == C.eval.bp(C.F.pn(n, h), y) : Maybe<&2, C.BV>}:
  %P.enc.dec(y) : {C.encM(a) == C.eval.bp(C.F.pn(n, h), _) : Maybe<&2, C.BV>}
  L.hp.F(n, n, h, C.dec(y), a, eR, L.le.refl(n))

def L.rec.eR(+n: Nat, +h: C.HPg, +y: C.BV, +w: C.BV, +a: Maybe<&2, C.HV>, +eR: {C.eval.hp(n, h, C.dec(y)) == C.RDone{a} : C.Run}, e: {C.eval.bp(C.F.pn(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.hp(n, h, C.dec(y)) == C.RDone{Some{C.dec(w)}} : C.Run}:
  %L.encM.inj(a, w, Equal.trans(Maybe<&2, C.BV>, C.encM(a), C.eval.bp(C.F.pn(n, h), y), Some{w}, L.rec.sqy(n, h, y, a, eR), e)) : {C.eval.hp(n, h, C.dec(y)) == C.RDone{_} : C.Run}
  eR

def L.rec.r(+n: Nat, +h: C.HPg, +b: C.BPg, le: P.Le.hp(h, C.G.p(b)), +y: C.BV, +w: C.BV, a: Maybe<&2, C.HV>, eR: {C.eval.hp(n, h, C.dec(y)) == C.RDone{a} : C.Run}, e: {C.eval.bp(C.F.pn(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.bp(b, y) == Some{w} : Maybe<&2, C.BV>}:
  %P.enc.dec(w) : {C.eval.bp(b, y) == Some{_} : Maybe<&2, C.BV>}
  L.decM.inj(C.eval.bp(b, y), C.dec(w), Equal.trans(Maybe<&2, C.HV>, C.decM(C.eval.bp(b, y)), C.eval.gp(C.G.p(b), C.dec(y)), Some{C.dec(w)}, L.bp.G(b, y), le(C.dec(y), C.dec(w), n, L.rec.eR(n, h, y, w, a, eR, e))))

def L.rec.r.at(+n: Nat, +h: C.HPg, +b: C.BPg, st: P.Stops.r(h, n), le: P.Le.hp(h, C.G.p(b)), +y: C.BV, +w: C.BV, e: {C.eval.bp(C.F.pn(n, h), y) == Some{w} : Maybe<&2, C.BV>}, R: C.Run, eR: {C.eval.hp(n, h, C.dec(y)) == R : C.Run}) -> {C.eval.bp(b, y) == Some{w} : Maybe<&2, C.BV>}:
  match R:
    case C.ROut{}:
      Empty.absurd({C.eval.bp(b, y) == Some{w} : Maybe<&2, C.BV>}, st(C.dec(y), eR))
    case C.RDone{a}:
      L.rec.r(n, h, b, le, y, w, a, eR, e)

def L.rec.r.go(+n: Nat, +h: C.HPg, +b: C.BPg, st: P.Stops.r(h, n), le: P.Le.hp(h, C.G.p(b)), +y: C.BV, +w: C.BV, e: {C.eval.bp(C.F.pn(n, h), y) == Some{w} : Maybe<&2, C.BV>}) -> {C.eval.bp(b, y) == Some{w} : Maybe<&2, C.BV>}:
  L.rec.r.at(n, h, b, st, le, y, w, e, C.eval.hp(n, h, C.dec(y)), {==})

def P.adj.FG.rec.r(n, h, b, st, le):
  y => w => e => L.rec.r.go(n, h, b, st, le, y, w, e)

def P.adj.FG.recf.l(h, b, st, le):
  P.adj.FG.rec.l(C.fuel(), h, b, st, le)

def P.adj.FG.recf.r(h, b, st, le):
  P.adj.FG.rec.r(C.fuel(), h, b, st, le)

# f x = f x never stops, and F's program of it answers its default
def L.hnr.out(k: Nat, +x: C.HV) -> {C.eval.hp(k, P.hnr(), x) == C.ROut{} : C.Run}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.hnr.out(j, x)

def L.hnr.def(n: Nat) -> {C.eval.bp(C.F.pn(n, P.hnr()), C.BvNat{0n}) == Some{C.BvNat{0n}} : Maybe<&2, C.BV>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      L.hnr.def(j)

def L.hnr.le(+x: C.HV, -v: C.HV, +k: Nat, e: {C.eval.hp(k, P.hnr(), x) == C.RDone{Some{v}} : C.Run}) -> {C.eval.gp(C.G.p(P.bn7r()), x) == Some{v} : Maybe<&2, C.HV>}:
  Empty.absurd({C.eval.gp(C.G.p(P.bn7r()), x) == Some{v} : Maybe<&2, C.HV>}, L.out.done(Some{v}, Equal.trans(C.Run, C.ROut{}, C.eval.hp(k, P.hnr(), x), C.RDone{Some{v}}, Equal.sym(C.Run, C.eval.hp(k, P.hnr(), x), C.ROut{}, L.hnr.out(k, x)), e)))

def P.adj.FG.rec.not(n, adj):
  %adj(P.hnr(), P.bn7r(), x => v => k => e => L.hnr.le(x, v, k, e), C.BvNat{0n}, C.BvNat{0n}, L.hnr.def(n)) : L.is7(_)
  Unit{}

# a loop's run is its definition's: c and m are p's and s's answers at x
def L.unt(k: Nat, +p: C.HTm, +s: C.HTm, x: C.HV, c: Maybe<&2, C.HV>, m: Maybe<&2, C.HV>) -> C.Run:
  match k:
    case 0n:
      C.ROut{}
    case 1n+j:
      C.r.if(C.RDone{c}, C.RDone{Some{x}}, C.r.bind(C.RDone{m}, y => C.eval.hr(j, C.until.ds(p, s), C.HrCall{0n}, y)))

def L.unt.at(j: Nat, +p: C.HTm, +s: C.HTm, +x: C.HV) -> {L.unt(1n+j, p, s, x, C.eval.h(p, x), C.eval.h(s, x)) == C.eval.hr(1n+j, C.until.ds(p, s), C.HrCall{0n}, x) : C.Run}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      {==}

def L.unt.eq(k: Nat, +p: C.HTm, +s: C.HTm, +x: C.HV) -> {L.unt(k, p, s, x, C.eval.h(p, x), C.eval.h(s, x)) == C.eval.hr(k, C.until.ds(p, s), C.HrCall{0n}, x) : C.Run}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.unt.at(j, p, s, x)

def L.until(k: Nat, +p: C.HTm, +s: C.HTm, +x: C.HV, c: Maybe<&2, C.HV>, m: Maybe<&2, C.HV>) -> {C.run.h(k, p, s, x, c, m) == L.unt(k, p, s, x, c, m) : C.Run}:
  match k:
    case 0n:
      {==}
    case 1n+j:
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
                      +j = j
                      Equal.trans(C.Run, C.run.h(j, p, s, y, C.eval.h(p, y), C.eval.h(s, y)), L.unt(j, p, s, y, C.eval.h(p, y), C.eval.h(s, y)), C.eval.hr(j, C.until.ds(p, s), C.HrCall{0n}, y), L.until(j, p, s, y, C.eval.h(p, y), C.eval.h(s, y)), L.unt.eq(j, p, s, y))
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

def P.until.rec(k, p, s, x):
  +k = k
  Equal.trans(C.Run, C.run.h(k, p, s, x, C.eval.h(p, x), C.eval.h(s, x)), L.unt(k, p, s, x, C.eval.h(p, x), C.eval.h(s, x)), C.eval.hr(k, C.until.ds(p, s), C.HrCall{0n}, x), L.until(k, p, s, x, C.eval.h(p, x), C.eval.h(s, x)), L.unt.eq(k, p, s, x))
