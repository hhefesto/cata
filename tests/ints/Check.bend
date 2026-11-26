# The integers past 2^48 of prelude/run/HsIntBig.bend (B) against the Nat
# integers HsPrelude ran on before (N, HsMapTree.bend's nsub) below 2^48,
# and past it against bc (run.zsh): main prints how many of the pairs below
# 2^48 differ, 2^130 - 1 and the steps (n - 1) div 2 takes it back to 0, then
# a line per big case, its inputs and B's answers, which run.zsh has bc work
# out again.
import Base
import ./Nat.bend as N
import ./Big.bend as B

def rnd(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def nat(s: U32) -> Nat:
  U32.to_nat(s)

# a size from s, by the kind k: below 100, below 2^32, below 2^46, or in
# [2^47, 2^47 + 2^46)
def size(k: Nat, +s: U32) -> Nat:
  match k:
    case 0n:
      Nat.mod(nat(s), 100n)
    case 1n:
      nat(s)
    case 2n:
      Nat.add(Nat.mul(nat(s), 16384n), Nat.mod(nat(rnd(s)), 16384n))
    case _:
      Nat.add(Nat.mul(8388608n, 16777216n), Nat.add(Nat.mul(nat(s), 8192n), Nat.mod(nat(rnd(s)), 8192n)))

def nint(neg: Bool, n: Nat) -> N.HsInt:
  N.HsInt.mul.sign(neg, n)

def bint(neg: Bool, n: Nat) -> B.HsInt:
  B.HsInt.mul.sign(neg, n)

# bit 16 of s (an LCG's low bits cycle)
def odd(s: U32) -> Bool:
  Nat.is_eq(Nat.mod(Nat.div(nat(s), 65536n), 2n), 1n)

def eqs(xs: List<&2, Char>, ys: List<&2, Char>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> t y <> u:
      Bool.and(Char.is_eq(x, y), eqs(t, u))
    case _ _:
      False{}

def cmpn(c: Cmp) -> Nat:
  match c:
    case LT{}:
      0n
    case EQ{}:
      1n
    case GT{}:
      2n

def all(xs: List<&1, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case b <> t:
      Bool.and(b, all(t))

# one pair below 2^48 (a any kind, b no bigger than 2^46, d not 0; m, n
# below 2^16 and 2^31, their product through B's limbs)
def same(+ga: Bool, +a: Nat, +gb: Bool, +b: Nat, +d: Nat, +m: Nat, +n: Nat) -> Bool:
  +na = nint(ga, a)
  +nb = nint(gb, b)
  +ba = bint(ga, a)
  +bb = bint(gb, b)
  +nd = nint(gb, d)
  +bd = bint(gb, d)
  all([eqs(N.HsInt.show(N.HsInt.add(na, nb)), B.HsInt.show(B.HsInt.add(ba, bb))), eqs(N.HsInt.show(N.HsInt.sub(na, nb)), B.HsInt.show(B.HsInt.sub(ba, bb))), eqs(N.HsInt.show(N.HsInt.sub(nb, na)), B.HsInt.show(B.HsInt.sub(bb, ba))), Nat.is_eq(cmpn(N.HsInt.cmp(na, nb)), cmpn(B.HsInt.cmp(ba, bb))), Nat.is_eq(cmpn(N.HsInt.cmp(nb, na)), cmpn(B.HsInt.cmp(bb, ba))), eqs(N.HsInt.show(N.HsInt.negate(na)), B.HsInt.show(B.HsInt.negate(ba))), eqs(N.HsInt.show(N.HsInt.abs(na)), B.HsInt.show(B.HsInt.abs(ba))), eqs(N.HsInt.show(N.HsInt.signum(na)), B.HsInt.show(B.HsInt.signum(ba))), eqs(N.HsInt.show(N.HsInt.quot(na, nd)), B.HsInt.show(B.HsInt.quot(ba, bd))), eqs(N.HsInt.show(N.HsInt.rem(na, nd)), B.HsInt.show(B.HsInt.rem(ba, bd))), eqs(N.HsInt.show(N.HsInt.div(na, nd)), B.HsInt.show(B.HsInt.div(ba, bd))), eqs(N.HsInt.show(N.HsInt.mod(na, nd)), B.HsInt.show(B.HsInt.mod(ba, bd))), eqs(N.HsInt.show(N.HsInt.mul(nint(ga, m), nint(gb, n))), B.HsInt.show(B.HsInt.mul(bint(ga, m), bint(gb, n)))), eqs(N.HsInt.show(N.HsInt.mul(nint(gb, Nat.mod(a, 16777216n)), nint(ga, Nat.mod(b, 16777216n)))), B.HsInt.show(B.HsInt.mul(bint(gb, Nat.mod(a, 16777216n)), bint(ga, Nat.mod(b, 16777216n))))), Nat.is_eq(N.HsInt.mag(na), B.HsInt.mag(ba)), Nat.is_eq(N.HsInt.count(nb), B.HsInt.count(bb))])

def small(n: Nat, +s: U32, +bad: Nat) -> Nat:
  match n:
    case 0n:
      bad
    case 1n+(+p):
      +s1 = rnd(s)
      +s2 = rnd(s1)
      +s3 = rnd(s2)
      +s4 = rnd(s3)
      +s5 = rnd(s4)
      +a = size(Nat.mod(p, 4n), s1)
      +b = size(Nat.mod(Nat.div(p, 4n), 3n), s2)
      small(p, rnd(s5), Bool.pick(Nat, same(odd(s3), a, odd(s4), b, 1n+b, Nat.mod(a, 65536n), Nat.mod(b, 2147483648n)), bad, 1n+bad))

def sp(xs: List<&2, Char>) -> List<&2, Char>:
  ' ' <> xs

# each after a space
def joins(xs: List<&2, List<&2, Char>>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      ' ' <> List.append(&2, Char, x, joins(t))

def shn(+g: Bool, n: Nat) -> List<&2, Char>:
  B.HsInt.show(bint(g, n))

# x = a*b*c and y = d*e (e 1 now and then, so y below 2^32), their sum,
# difference, product, quot, rem, div, mod, and x's comparison with y
def big(+g: Bool, +a: Nat, +b: Nat, +c: Nat, +h: Bool, +d: Nat, +e: Nat) -> List<&2, Char>:
  +x = B.HsInt.mul(B.HsInt.mul(bint(g, a), B.HsInt.Pos{b}), B.HsInt.Pos{c})
  +y = B.HsInt.mul(bint(h, d), B.HsInt.Pos{e})
  +ins = List.append(&2, Char, shn(g, a), sp(List.append(&2, Char, shn(False{}, b), sp(List.append(&2, Char, shn(False{}, c), sp(List.append(&2, Char, shn(h, d), sp(shn(False{}, e)))))))))
  List.append(&2, Char, ins, List.append(&2, Char, [' ', ':'], List.append(&2, Char, joins([B.HsInt.show(x), B.HsInt.show(y), B.HsInt.show(B.HsInt.add(x, y)), B.HsInt.show(B.HsInt.sub(x, y)), B.HsInt.show(B.HsInt.mul(x, y)), B.HsInt.show(B.HsInt.quot(x, y)), B.HsInt.show(B.HsInt.rem(x, y)), B.HsInt.show(B.HsInt.div(x, y)), B.HsInt.show(B.HsInt.mod(x, y)), String.to_list(Nat.show(cmpn(B.HsInt.cmp(x, y))))]), ['\n'])))

def bigs(n: Nat, +s: U32) -> List<&2, Char>:
  match n:
    case 0n:
      Nil{}
    case 1n+(+p):
      +s1 = rnd(s)
      +s2 = rnd(s1)
      +s3 = rnd(s2)
      +s4 = rnd(s3)
      +s5 = rnd(s4)
      +s6 = rnd(s5)
      +e = Bool.pick(Nat, Nat.is_eq(Nat.mod(p, 3n), 0n), 1n, 1n+nat(s6))
      List.append(&2, Char, big(odd(s1), 1n+nat(s1), nat(s2), 1n+nat(s3), odd(s4), 1n+Nat.mod(nat(s4), Bool.pick(Nat, Nat.is_eq(Nat.mod(p, 2n), 0n), 4294967295n, 65536n)), e), bigs(p, rnd(s6)))

# 2n + 1 k times from 0, then (n - 1) div 2 back (telomare's inputPath):
# how many steps back reach 0
def up(k: Nat, n: B.HsInt) -> B.HsInt:
  match k:
    case 0n:
      n
    case 1n+p:
      up(p, B.HsInt.add(B.HsInt.mul(n, B.HsInt.Pos{2n}), B.HsInt.Pos{1n}))

def down(k: Nat, +n: B.HsInt, +c: Nat) -> Nat:
  match k:
    case 0n:
      c
    case 1n+p:
      Bool.pick(Nat, B.HsInt.is_eq(n, B.HsInt.Pos{0n}), c, down(p, B.HsInt.div(B.HsInt.sub(n, B.HsInt.Pos{1n}), B.HsInt.Pos{2n}), 1n+c))

def main() -> IO(Unit):
  +p = up(130n, B.HsInt.Pos{0n})
  IO.print(String.from_list(List.append(&2, Char, String.to_list(Nat.show(small(400n, 4242, 0n))), List.append(&2, Char, String.to_list(" of 400 pairs below 2^48 differ\n2^130 - 1 = "), List.append(&2, Char, B.HsInt.show(p), List.append(&2, Char, String.to_list(", back to 0 in "), List.append(&2, Char, String.to_list(Nat.show(down(200n, p, 0n))), List.append(&2, Char, String.to_list(" steps\n"), bigs(150n, 777)))))))))
