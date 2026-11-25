# The balanced trees of prelude/run/HsMapTree.bend against HsPrelude's lists:
# the same toList after the same operations on random keys (run.zsh).
import Base
import ./List.bend as L
import ./Tree.bend as T

def cmp(a: Nat, b: Nat) -> Cmp:
  Nat.cmp(a, b)

def eqn(a: Nat, b: Nat) -> Bool:
  Nat.is_eq(a, b)

def eqp(p: Sigma<&2, &2, Nat, _ => Nat>, q: Sigma<&2, &2, Nat, _ => Nat>) -> Bool:
  match p q:
    case Tuple{a, b} Tuple{c, d}:
      Bool.and(Nat.is_eq(a, c), Nat.is_eq(b, d))

def eqps(xs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, ys: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> t y <> u:
      Bool.and(eqp(x, y), eqps(t, u))
    case _ _:
      False{}

def eqns(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> t y <> u:
      Bool.and(Nat.is_eq(x, y), eqns(t, u))
    case _ _:
      False{}

def eqm(m: Maybe<&2, Nat>, n: Maybe<&2, Nat>) -> Bool:
  match m n:
    case None{} None{}:
      True{}
    case Some{a} Some{b}:
      Nat.is_eq(a, b)
    case _ _:
      False{}

def rnd(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def key(s: U32) -> Nat:
  U32.to_nat(U32.mod(U32.shrn(s, 16n), 97))

type Two is Data:
  Two{l: L.HsMap<Nat, Nat>, t: T.HsMap<Nat, Nat>}

def add(n: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.mul(a, 3n), b)

def op(w: U32, +k: Nat, +v: Nat, l: L.HsMap<Nat, Nat>, t: T.HsMap<Nat, Nat>) -> Two:
  match w:
    case 0:
      Two{L.HsMap.delete(~Nat, ~Nat, ~cmp, k, l), T.HsMap.delete(~Nat, ~Nat, ~cmp, k, t)}
    case 1:
      Two{L.HsMap.insertWith(~Nat, ~Nat, ~cmp, a => b => Nat.add(Nat.mul(a, 3n), b), k, v, l), T.HsMap.insertWith(~Nat, ~Nat, ~cmp, a => b => Nat.add(Nat.mul(a, 3n), b), k, v, t)}
    case 2:
      Two{L.HsMap.adjust(~Nat, ~Nat, ~cmp, a => Nat.add(a, 1n), k, l), T.HsMap.adjust(~Nat, ~Nat, ~cmp, a => Nat.add(a, 1n), k, t)}
    case _:
      Two{L.HsMap.insert(~Nat, ~Nat, ~cmp, k, v, l), T.HsMap.insert(~Nat, ~Nat, ~cmp, k, v, t)}

def opt(+s: U32, w: Two) -> Two:
  match w:
    case Two{l, t}:
      op(U32.mod(U32.shrn(s, 8n), 6), key(s), key(rnd(s)), l, t)

def build(n: Nat, +s: U32, w: Two) -> Two:
  match n:
    case 0n:
      w
    case 1n+p:
      build(p, rnd(s), opt(s, w))

# the tree's balance and sizes
def bal(t: T.HsMap<Nat, Nat>) -> Bool:
  match t:
    case T.HsMap.Tip{}:
      True{}
    case T.HsMap.Bin{s, k, v, +l, +r}:
      +sl = T.HsMap.sz(Nat, Nat, l)
      +sr = T.HsMap.sz(Nat, Nat, r)
      Bool.and(U32.is_eq(s, U32.inc(U32.add(sl, sr))), Bool.and(Bool.or(U32.is_lt(U32.add(sl, sr), 2), Bool.and(U32.is_le(sl, U32.mul(3, sr)), U32.is_le(sr, U32.mul(3, sl)))), Bool.and(bal(l), bal(r))))

def same(+l: L.HsMap<Nat, Nat>, +t: T.HsMap<Nat, Nat>) -> Bool:
  Bool.and(eqps(L.HsMap.toList(~Nat, ~Nat, l), T.HsMap.toList(~Nat, ~Nat, t)), Bool.and(Nat.is_eq(L.HsMap.size(~Nat, ~Nat, l), T.HsMap.size(~Nat, ~Nat, t)), bal(t)))

def sames(l: L.HsSet<Nat>, t: T.HsSet<Nat>) -> Bool:
  eqns(L.HsSet.toList(~Nat, l), T.HsSet.toList(~Nat, t))

def pairs(p: Sigma<&2, &2, L.HsMap<Nat, Nat>, _ => L.HsMap<Nat, Nat>>, q: Sigma<&2, &2, T.HsMap<Nat, Nat>, _ => T.HsMap<Nat, Nat>>) -> Bool:
  match p q:
    case Tuple{a, b} Tuple{c, d}:
      Bool.and(same(a, c), same(b, d))

def all(xs: List<&1, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case b <> t:
      Bool.and(b, all(t))

def two(a: Two, b: Two) -> Bool:
  match a b:
    case Two{+la, +ta} Two{+lb, +tb}:
      all([same(la, ta), same(lb, tb), same(L.HsMap.union(~Nat, ~Nat, ~cmp, la, lb), T.HsMap.union(~Nat, ~Nat, ~cmp, ta, tb)), same(L.HsMap.unionWith(~Nat, ~Nat, ~cmp, ~(a => b => Nat.add(Nat.mul(a, 3n), b)), la, lb), T.HsMap.unionWith(~Nat, ~Nat, ~cmp, ~(a => b => Nat.add(Nat.mul(a, 3n), b)), ta, tb)), same(L.HsMap.unionWithKey(~Nat, ~Nat, ~cmp, ~(k => a => b => Nat.add(k, Nat.add(Nat.mul(a, 3n), b))), la, lb), T.HsMap.unionWithKey(~Nat, ~Nat, ~cmp, ~(k => a => b => Nat.add(k, Nat.add(Nat.mul(a, 3n), b))), ta, tb)), same(L.HsMap.difference(~Nat, ~Nat, ~Nat, ~cmp, la, lb), T.HsMap.difference(~Nat, ~Nat, ~Nat, ~cmp, ta, tb)), same(L.HsMap.intersectionWith(~Nat, ~Nat, ~Nat, ~Nat, ~cmp, ~(a => b => Nat.add(Nat.mul(a, 3n), b)), la, lb), T.HsMap.intersectionWith(~Nat, ~Nat, ~Nat, ~Nat, ~cmp, ~(a => b => Nat.add(Nat.mul(a, 3n), b)), ta, tb)), same(L.HsMap.filter(~Nat, ~Nat, ~(v => Nat.is_lt(v, 40n)), la), T.HsMap.filter(~Nat, ~Nat, ~(v => Nat.is_lt(v, 40n)), ta)), same(L.HsMap.map(~Nat, ~Nat, ~Nat, ~(v => Nat.add(v, 1n)), la), T.HsMap.map(~Nat, ~Nat, ~Nat, ~(v => Nat.add(v, 1n)), ta)), same(L.HsMap.mapWithKey(~Nat, ~Nat, ~Nat, ~(k => v => Nat.add(v, k)), la), T.HsMap.mapWithKey(~Nat, ~Nat, ~Nat, ~(k => v => Nat.add(v, k)), ta)), pairs(L.HsMap.split(~Nat, ~Nat, ~cmp, 40n, la), T.HsMap.split(~Nat, ~Nat, ~cmp, 40n, ta)), sames(L.HsMap.keysSet(~Nat, ~Nat, la), T.HsMap.keysSet(~Nat, ~Nat, ta)), same(L.HsMap.restrictKeys(~Nat, ~Nat, ~cmp, la, L.HsMap.keysSet(~Nat, ~Nat, lb)), T.HsMap.restrictKeys(~Nat, ~Nat, ~cmp, ta, T.HsMap.keysSet(~Nat, ~Nat, tb))), same(L.HsMap.withoutKeys(~Nat, ~Nat, ~cmp, la, L.HsMap.keysSet(~Nat, ~Nat, lb)), T.HsMap.withoutKeys(~Nat, ~Nat, ~cmp, ta, T.HsMap.keysSet(~Nat, ~Nat, tb))), sames(L.HsSet.union(~Nat, ~cmp, L.HsMap.keysSet(~Nat, ~Nat, la), L.HsMap.keysSet(~Nat, ~Nat, lb)), T.HsSet.union(~Nat, ~cmp, T.HsMap.keysSet(~Nat, ~Nat, ta), T.HsMap.keysSet(~Nat, ~Nat, tb))), sames(L.HsSet.difference(~Nat, ~cmp, L.HsMap.keysSet(~Nat, ~Nat, la), L.HsMap.keysSet(~Nat, ~Nat, lb)), T.HsSet.difference(~Nat, ~cmp, T.HsMap.keysSet(~Nat, ~Nat, ta), T.HsMap.keysSet(~Nat, ~Nat, tb))), sames(L.HsSet.intersection(~Nat, ~cmp, L.HsMap.keysSet(~Nat, ~Nat, la), L.HsMap.keysSet(~Nat, ~Nat, lb)), T.HsSet.intersection(~Nat, ~cmp, T.HsMap.keysSet(~Nat, ~Nat, ta), T.HsMap.keysSet(~Nat, ~Nat, tb))), sames(L.HsSet.map(~Nat, ~Nat, ~cmp, ~(k => Nat.div(k, 3n)), L.HsMap.keysSet(~Nat, ~Nat, la)), T.HsSet.map(~Nat, ~Nat, ~cmp, ~(k => Nat.div(k, 3n)), T.HsMap.keysSet(~Nat, ~Nat, ta))), eqm(L.HsMap.lookup(~Nat, ~Nat, ~cmp, 41n, la), T.HsMap.lookup(~Nat, ~Nat, ~cmp, 41n, ta)), eqns(L.HsMap.elems(~Nat, ~Nat, la), T.HsMap.elems(~Nat, ~Nat, ta)), Nat.is_eq(L.HsMap.foldrWithKey(~Nat, ~Nat, ~Nat, ~(k => v => z => Nat.mod(Nat.add(Nat.mul(z, 7n), Nat.add(k, v)), 1009n)), 1n, la), T.HsMap.foldrWithKey(~Nat, ~Nat, ~Nat, ~(k => v => z => Nat.mod(Nat.add(Nat.mul(z, 7n), Nat.add(k, v)), 1009n)), 1n, ta))])

def run(n: Nat, +s: U32, +bad: Nat) -> Nat:
  match n:
    case 0n:
      bad
    case 1n+(+p):
      +a = build(Nat.mul(p, 3n), s, Two{L.HsMap.Tip{}, T.HsMap.Tip{}})
      +b = build(Nat.mod(Nat.mul(p, 7n), 90n), rnd(s), Two{L.HsMap.Tip{}, T.HsMap.Tip{}})
      run(p, U32.add(rnd(rnd(s)), 7), Bool.pick(Nat, two(a, b), bad, 1n+bad))

def main() -> IO(Unit):
  IO.print(Nat.show(run(120n, 12345, 0n)) ++ " of 120 pairs of maps differ")
