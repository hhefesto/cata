# The prelude's own HsInt (HsInt.bend, written by hsint.zsh from what cata
# writes into HsPrelude.bend) is the model's Int: HsInt.add, sub and is_lt,
# and HsNum.idiv and imod (failure values at 0), are Core.bend's z.add,
# z.sub, z.lt, z.div and z.mod, at every pair of numbers, not on a grid.
# So section 10's eval.bz is Bend's meaning with the prelude's own integers.
# Int's range stays outside: HsInt has every integer (RgAll).

import Base
import ./Core.bend as C
import ./HsInt.bend as H

# the HsInt of one of the model's Int's numbers: ZvNat{n} is n, ZvNeg{n} is
# -(n+1)
def hz(v: C.ZV) -> Maybe<&2, H.HsInt>:
  match v:
    case C.ZvNat{n}:
      Some{H.HsInt.Pos{n}}
    case C.ZvNeg{n}:
      Some{H.HsInt.Neg{1n+n}}
    case _:
      None{}

def hzM(m: Maybe<&2, C.ZV>) -> Maybe<&2, H.HsInt>:
  match m:
    case Some{v}:
      hz(v)
    case None{}:
      None{}

def hbM(m: Maybe<&2, C.ZV>) -> Maybe<&2, Bool>:
  match m:
    case Some{C.ZvBool{b}}:
      Some{b}
    case _:
      None{}

# a failure value is None
def eM(e: Either<&2, &2, List<&2, Char>, H.HsInt>) -> Maybe<&2, H.HsInt>:
  match e:
    case Inl{m}:
      None{}
    case Inr{x}:
      Some{x}

# the prelude's operations at two numbers (None at anything else)
def h.add(x: Maybe<&2, H.HsInt>, y: Maybe<&2, H.HsInt>) -> Maybe<&2, H.HsInt>:
  match x:
    case None{}:
      None{}
    case Some{u}:
      match y:
        case None{}:
          None{}
        case Some{w}:
          Some{H.HsInt.add(u, w)}

def h.sub(x: Maybe<&2, H.HsInt>, y: Maybe<&2, H.HsInt>) -> Maybe<&2, H.HsInt>:
  match x:
    case None{}:
      None{}
    case Some{u}:
      match y:
        case None{}:
          None{}
        case Some{w}:
          Some{H.HsInt.sub(u, w)}

def h.lt(x: Maybe<&2, H.HsInt>, y: Maybe<&2, H.HsInt>) -> Maybe<&2, Bool>:
  match x:
    case None{}:
      None{}
    case Some{u}:
      match y:
        case None{}:
          None{}
        case Some{w}:
          Some{H.HsInt.is_lt(u, w)}

def h.div(x: Maybe<&2, H.HsInt>, y: Maybe<&2, H.HsInt>) -> Maybe<&2, H.HsInt>:
  match x:
    case None{}:
      None{}
    case Some{u}:
      match y:
        case None{}:
          None{}
        case Some{w}:
          eM(H.HsNum.idiv(u, w))

def h.mod(x: Maybe<&2, H.HsInt>, y: Maybe<&2, H.HsInt>) -> Maybe<&2, H.HsInt>:
  match x:
    case None{}:
      None{}
    case Some{u}:
      match y:
        case None{}:
          None{}
        case Some{w}:
          eM(H.HsNum.imod(u, w))

# the laws, at every pair of the model's values (two numbers, or both sides
# None)

law hs.add:
  for a: C.ZV
  for b: C.ZV
  {h.add(hz(a), hz(b)) == hzM(C.z.add(a, b)) : Maybe<&2, H.HsInt>}

law hs.sub:
  for a: C.ZV
  for b: C.ZV
  {h.sub(hz(a), hz(b)) == hzM(C.z.sub(a, b)) : Maybe<&2, H.HsInt>}

law hs.lt:
  for a: C.ZV
  for b: C.ZV
  {h.lt(hz(a), hz(b)) == hbM(C.z.lt(a, b)) : Maybe<&2, Bool>}

law hs.div:
  for +a: C.ZV
  for +b: C.ZV
  {h.div(hz(a), hz(b)) == hzM(C.z.div(a, b)) : Maybe<&2, H.HsInt>}

law hs.mod:
  for +a: C.ZV
  for +b: C.ZV
  {h.mod(hz(a), hz(b)) == hzM(C.z.mod(a, b)) : Maybe<&2, H.HsInt>}

# arithmetic -----------------------------------------------------------------------

def L.add0(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %L.add0(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def L.addS(n: Nat, +m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %L.addS(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def L.sub0(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def L.minusS(c: Bool, -i: Nat, -j: Nat) -> {hz(C.z.minus.at(c, i, j)) == hz(C.z.minus.at(c, 1n+i, 1n+j)) : Maybe<&2, H.HsInt>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# m - n as the prelude's nsub and the model's minus
def L.nsub(+m: Nat, +n: Nat) -> {Some{H.HsInt.nsub(m, n)} == hz(C.z.minus(m, n)) : Maybe<&2, H.HsInt>}:
  match m:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+k:
          %Equal.sym(Nat, Nat.sub(k, 0n), k, L.sub0(k)) : {Some{H.HsInt.Neg{1n+k}} == Some{H.HsInt.Neg{1n+_}} : Maybe<&2, H.HsInt>}
          {==}
    case 1n+i:
      match n:
        case 0n:
          {==}
        case 1n+j:
          %L.minusS(Nat.is_lt(i, j), i, j) : {Some{H.HsInt.nsub(i, j)} == _ : Maybe<&2, H.HsInt>}
          L.nsub(i, j)

def hs.add(a, b):
  match a:
    case C.ZvNat{m}:
      match b:
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          L.nsub(m, 1n+n)
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvNeg{m}:
      match b:
        case C.ZvNat{n}:
          L.nsub(n, 1n+m)
        case C.ZvNeg{n}:
          %Equal.sym(Nat, Nat.add(m, 1n+n), 1n+Nat.add(m, n), L.addS(m, n)) : {Some{H.HsInt.Neg{1n+_}} == Some{H.HsInt.Neg{2n+Nat.add(m, n)}} : Maybe<&2, H.HsInt>}
          {==}
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvBool{q}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{p, q}:
      {==}
    case C.ZvInl{q}:
      {==}
    case C.ZvInr{q}:
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{p, q}:
      {==}

def L.nsub0(m: Nat) -> {Some{H.HsInt.Pos{m}} == hz(C.z.minus(m, 0n)) : Maybe<&2, H.HsInt>}:
  match m:
    case 0n:
      {==}
    case 1n+i:
      {==}

# -(m+1) - n
def L.subneg(+m: Nat, n: Nat) -> {Some{H.HsInt.add(H.HsInt.Neg{1n+m}, H.HsInt.neg.of(n))} == Some{H.HsInt.Neg{1n+Nat.add(m, n)}} : Maybe<&2, H.HsInt>}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(m, 0n), m, L.add0(m)) : {Some{H.HsInt.nsub(0n, 1n+m)} == Some{H.HsInt.Neg{1n+_}} : Maybe<&2, H.HsInt>}
      {==}
    case 1n+k:
      {==}

def L.negof(k: Nat) -> {H.HsInt.neg.of(1n+k) == H.HsInt.Neg{1n+k} : H.HsInt}:
  {==}

# a Nat and the negation of a Nat
def L.subn(+m: Nat, n: Nat) -> {Some{H.HsInt.add(H.HsInt.Pos{m}, H.HsInt.neg.of(n))} == hz(C.z.minus(m, n)) : Maybe<&2, H.HsInt>}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(m, 0n), m, L.add0(m)) : {Some{H.HsInt.Pos{_}} == hz(C.z.minus(m, 0n)) : Maybe<&2, H.HsInt>}
      L.nsub0(m)
    case 1n+k:
      L.nsub(m, 1n+k)

def hs.sub(a, b):
  match a:
    case C.ZvNat{m}:
      match b:
        case C.ZvNat{n}:
          L.subn(m, n)
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvNeg{m}:
      match b:
        case C.ZvNat{n}:
          L.subneg(m, n)
        case C.ZvNeg{n}:
          L.nsub(n, m)
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvBool{q}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{p, q}:
      {==}
    case C.ZvInl{q}:
      {==}
    case C.ZvInr{q}:
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{p, q}:
      {==}

def hs.lt(a, b):
  match a:
    case C.ZvNat{m}:
      match b:
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvNeg{m}:
      match b:
        case C.ZvNat{n}:
          {==}
        case C.ZvNeg{n}:
          {==}
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvBool{q}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{p, q}:
      {==}
    case C.ZvInl{q}:
      {==}
    case C.ZvInr{q}:
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{p, q}:
      {==}

# division --------------------------------------------------------------------------

def L.andF(c: Bool) -> {Bool.and(c, False{}) == False{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a pick whose condition ends in False
def L.pickF(+c: Bool, -x: H.HsInt, -y: H.HsInt) -> {Bool.pick(H.HsInt, Bool.and(c, False{}), x, y) == y : H.HsInt}:
  %Equal.sym(Bool, Bool.and(c, False{}), False{}, L.andF(c)) : {Bool.pick(H.HsInt, _, x, y) == y : H.HsInt}
  {==}

# of signs that differ, q = |a| div |b| and r = |a| mod |b|: -q when r is
# 0, else -q - 1
def h.divx(+q: Nat, +rr: H.HsInt) -> H.HsInt:
  Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(rr, H.HsInt.Pos{0n})), True{}), H.HsInt.sub(H.HsInt.neg.of(q), H.HsInt.Pos{1n}), H.HsInt.neg.of(q))

def L.negq(q: Nat) -> {Some{H.HsInt.neg.of(q)} == hz(C.z.negn(q)) : Maybe<&2, H.HsInt>}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def L.negq1(+q: Nat) -> {Some{H.HsInt.sub(H.HsInt.neg.of(q), H.HsInt.Pos{1n})} == Some{H.HsInt.Neg{1n+q}} : Maybe<&2, H.HsInt>}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+Nat.add(p, 0n), L.addS(p, 0n)) : {Some{H.HsInt.Neg{1n+_}} == Some{H.HsInt.Neg{2n+p}} : Maybe<&2, H.HsInt>}
      %Equal.sym(Nat, Nat.add(p, 0n), p, L.add0(p)) : {Some{H.HsInt.Neg{2n+_}} == Some{H.HsInt.Neg{2n+p}} : Maybe<&2, H.HsInt>}
      {==}

# the remainder of a non-negative number, and of a negative one
def L.divp(+q: Nat, r: Nat) -> {Some{h.divx(q, H.HsInt.Pos{r})} == hz(C.z.divx(q, r)) : Maybe<&2, H.HsInt>}:
  match r:
    case 0n:
      L.negq(q)
    case 1n+k:
      L.negq1(q)

def L.divn(+q: Nat, r: Nat) -> {Some{h.divx(q, H.HsInt.neg.of(r))} == hz(C.z.divx(q, r)) : Maybe<&2, H.HsInt>}:
  match r:
    case 0n:
      L.negq(q)
    case 1n+k:
      L.negq1(q)

def L.divpp(+m: Nat, +q: Nat) -> {Some{H.HsInt.div(H.HsInt.Pos{m}, H.HsInt.Pos{1n+q})} == Some{H.HsInt.Pos{Nat.div(m, 1n+q)}} : Maybe<&2, H.HsInt>}:
  %Equal.sym(H.HsInt, Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{0n})), False{}), H.HsInt.sub(H.HsInt.Pos{Nat.div(m, 1n+q)}, H.HsInt.Pos{1n}), H.HsInt.Pos{Nat.div(m, 1n+q)}), H.HsInt.Pos{Nat.div(m, 1n+q)}, L.pickF(Bool.not(H.HsInt.is_eq(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{0n})), H.HsInt.sub(H.HsInt.Pos{Nat.div(m, 1n+q)}, H.HsInt.Pos{1n}), H.HsInt.Pos{Nat.div(m, 1n+q)})) : {Some{_} == Some{H.HsInt.Pos{Nat.div(m, 1n+q)}} : Maybe<&2, H.HsInt>}
  {==}

def L.divnn(+m: Nat, +n: Nat) -> {Some{H.HsInt.div(H.HsInt.Neg{1n+m}, H.HsInt.Neg{1n+n})} == Some{H.HsInt.Pos{Nat.div(1n+m, 1n+n)}} : Maybe<&2, H.HsInt>}:
  %Equal.sym(H.HsInt, Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.neg.of(Nat.mod(1n+m, 1n+n)), H.HsInt.Pos{0n})), False{}), H.HsInt.sub(H.HsInt.Pos{Nat.div(1n+m, 1n+n)}, H.HsInt.Pos{1n}), H.HsInt.Pos{Nat.div(1n+m, 1n+n)}), H.HsInt.Pos{Nat.div(1n+m, 1n+n)}, L.pickF(Bool.not(H.HsInt.is_eq(H.HsInt.neg.of(Nat.mod(1n+m, 1n+n)), H.HsInt.Pos{0n})), H.HsInt.sub(H.HsInt.Pos{Nat.div(1n+m, 1n+n)}, H.HsInt.Pos{1n}), H.HsInt.Pos{Nat.div(1n+m, 1n+n)})) : {Some{_} == Some{H.HsInt.Pos{Nat.div(1n+m, 1n+n)}} : Maybe<&2, H.HsInt>}
  {==}

def hs.div(a, b):
  match a:
    case C.ZvNat{m}:
      match b:
        case C.ZvNat{n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              L.divpp(m, q)
        case C.ZvNeg{n}:
          L.divp(Nat.div(m, 1n+n), Nat.mod(m, 1n+n))
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvNeg{m}:
      match b:
        case C.ZvNat{n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              L.divn(Nat.div(1n+m, 1n+q), Nat.mod(1n+m, 1n+q))
        case C.ZvNeg{n}:
          L.divnn(m, n)
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvBool{q}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{p, q}:
      {==}
    case C.ZvInl{q}:
      {==}
    case C.ZvInr{q}:
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{p, q}:
      {==}

# the remainder is below the divisor: divmod's countdown m and remainder r
# add up to the divisor less one, at every step
def L.wm(n: Nat, +m: Nat, +r: Nat) -> Nat:
  match n:
    case 0n:
      m
    case 1n+np:
      match m:
        case 0n:
          L.wm(np, r, 0n)
        case 1n+mp:
          L.wm(np, mp, 1n+r)

def L.inv(n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.add(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), L.wm(n, m, r)) == Nat.add(r, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          Equal.trans(Nat, Nat.add(Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), L.wm(np, r, 0n)), r, Nat.add(r, 0n), L.inv(np, r, 1n+d, 0n), Equal.sym(Nat, Nat.add(r, 0n), r, L.add0(r)))
        case 1n+mp:
          Equal.trans(Nat, Nat.add(Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), L.wm(np, mp, 1n+r)), 1n+Nat.add(r, mp), Nat.add(r, 1n+mp), L.inv(np, mp, d, 1n+r), Equal.sym(Nat, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), L.addS(r, mp)))

def L.nsublt(k: Nat, +s: Nat) -> {Some{H.HsInt.nsub(k, 1n+Nat.add(k, s))} == Some{H.HsInt.Neg{1n+Nat.sub(Nat.add(k, s), k)}} : Maybe<&2, H.HsInt>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.sub(s, 0n), s, L.sub0(s)) : {Some{H.HsInt.Neg{1n+s}} == Some{H.HsInt.Neg{1n+_}} : Maybe<&2, H.HsInt>}
      {==}
    case 1n+j:
      L.nsublt(j, s)

def L.nsubge(k: Nat, +s: Nat) -> {Some{H.HsInt.nsub(1n+Nat.add(k, s), k)} == Some{H.HsInt.Pos{Nat.sub(1n+Nat.add(k, s), k)}} : Maybe<&2, H.HsInt>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.nsubge(j, s)

# a >= 0 and b < 0: r when it is 0, else r + b
def L.modn(+n: Nat, r: Nat, +s: Nat, e: {Nat.add(r, s) == n : Nat}) -> {Some{Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.Pos{r}, H.HsInt.Pos{0n})), True{}), H.HsInt.add(H.HsInt.Pos{r}, H.HsInt.Neg{1n+n}), H.HsInt.Pos{r})} == hz(C.z.modn(n, r)) : Maybe<&2, H.HsInt>}:
  match r:
    case 0n:
      {==}
    case 1n+k:
      %e : {Some{H.HsInt.nsub(k, _)} == Some{H.HsInt.Neg{1n+Nat.sub(_, 1n+k)}} : Maybe<&2, H.HsInt>}
      L.nsublt(k, s)

# a < 0 and b > 0
def L.modp(+q: Nat, r: Nat, +s: Nat, e: {Nat.add(r, s) == q : Nat}) -> {Some{Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.neg.of(r), H.HsInt.Pos{0n})), Bool.xor(H.HsInt.isneg(H.HsInt.neg.of(r)), False{})), H.HsInt.add(H.HsInt.neg.of(r), H.HsInt.Pos{1n+q}), H.HsInt.neg.of(r))} == hz(C.z.modp(1n+q, r)) : Maybe<&2, H.HsInt>}:
  match r:
    case 0n:
      {==}
    case 1n+k:
      %e : {Some{H.HsInt.nsub(_, k)} == Some{H.HsInt.Pos{Nat.sub(_, k)}} : Maybe<&2, H.HsInt>}
      L.nsubge(k, s)

# both below 0
def L.modnn(-n: Nat, r: Nat) -> {Some{Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.neg.of(r), H.HsInt.Pos{0n})), Bool.xor(H.HsInt.isneg(H.HsInt.neg.of(r)), True{})), H.HsInt.add(H.HsInt.neg.of(r), H.HsInt.Neg{1n+n}), H.HsInt.neg.of(r))} == hz(C.z.negn(r)) : Maybe<&2, H.HsInt>}:
  match r:
    case 0n:
      {==}
    case 1n+k:
      {==}

def L.modpp(+m: Nat, +q: Nat) -> {Some{H.HsInt.mod(H.HsInt.Pos{m}, H.HsInt.Pos{1n+q})} == Some{H.HsInt.Pos{Nat.mod(m, 1n+q)}} : Maybe<&2, H.HsInt>}:
  %Equal.sym(H.HsInt, Bool.pick(H.HsInt, Bool.and(Bool.not(H.HsInt.is_eq(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{0n})), False{}), H.HsInt.add(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{1n+q}), H.HsInt.Pos{Nat.mod(m, 1n+q)}), H.HsInt.Pos{Nat.mod(m, 1n+q)}, L.pickF(Bool.not(H.HsInt.is_eq(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{0n})), H.HsInt.add(H.HsInt.Pos{Nat.mod(m, 1n+q)}, H.HsInt.Pos{1n+q}), H.HsInt.Pos{Nat.mod(m, 1n+q)})) : {Some{_} == Some{H.HsInt.Pos{Nat.mod(m, 1n+q)}} : Maybe<&2, H.HsInt>}
  {==}

def hs.mod(a, b):
  match a:
    case C.ZvNat{m}:
      match b:
        case C.ZvNat{n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              L.modpp(m, q)
        case C.ZvNeg{n}:
          L.modn(n, Nat.mod(m, 1n+n), L.wm(m, n, 0n), L.inv(m, n, 0n, 0n))
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvNeg{m}:
      match b:
        case C.ZvNat{n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              L.modp(q, Nat.mod(1n+m, 1n+q), L.wm(1n+m, q, 0n), L.inv(1n+m, q, 0n, 0n))
        case C.ZvNeg{n}:
          L.modnn(n, Nat.mod(1n+m, 1n+n))
        case C.ZvBool{q}:
          {==}
        case C.ZvUnit{}:
          {==}
        case C.ZvPair{p, q}:
          {==}
        case C.ZvInl{q}:
          {==}
        case C.ZvInr{q}:
          {==}
        case C.ZvNil{}:
          {==}
        case C.ZvCons{p, q}:
          {==}
    case C.ZvBool{q}:
      {==}
    case C.ZvUnit{}:
      {==}
    case C.ZvPair{p, q}:
      {==}
    case C.ZvInl{q}:
      {==}
    case C.ZvInr{q}:
      {==}
    case C.ZvNil{}:
      {==}
    case C.ZvCons{p, q}:
      {==}
