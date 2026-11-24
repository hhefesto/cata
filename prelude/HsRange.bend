# GHC.Enum's [a .. b] at Nat (Int, Integer and Natural in a module alone) and
# at Char, and [a, b .. c] at Nat and at HsInt, a and b different (Fold.bend's
# fd.range and fd.range3: the fold writes it at two different literals, so it
# ends)
def HsList.range.go(n: Nat, +a: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      a <> HsList.range.go(p, 1n+a)

def HsList.range(+a: Nat, b: Nat) -> List<&2, Nat>:
  HsList.range.go(Nat.sub(1n+b, a), a)

def HsList.rangeChar.go(n: Nat, +a: U32) -> List<&2, Char>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Char.from_u32(a) <> HsList.rangeChar.go(p, U32.add(a, 1))

def HsList.rangeChar.at(+a: U32, +b: U32) -> List<&2, Char>:
  HsList.rangeChar.go(Bool.pick(Nat, U32.is_le(a, b), U32.to_nat(U32.add(U32.sub(b, a), 1)), 0n), a)

def HsList.rangeChar(a: Char, b: Char) -> List<&2, Char>:
  HsList.rangeChar.at(Char.to_u32(a), Char.to_u32(b))

def HsList.rangeUp(n: Nat, +a: Nat, +d: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      a <> HsList.rangeUp(p, Nat.add(a, d), d)

def HsList.rangeDown(n: Nat, +a: Nat, +d: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      a <> HsList.rangeDown(p, Nat.sub(a, d), d)

# how many steps of d there are in n, and the first (0 when none: n < m)
def HsList.rangeBy.n(+m: Nat, +n: Nat, d: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(m, n), 1n+Nat.div(Nat.sub(n, m), d), 0n)

def HsList.rangeBy(+a: Nat, +b: Nat, +c: Nat) -> List<&2, Nat>:
  +up = Nat.sub(b, a)
  +dn = Nat.sub(a, b)
  HsBool.if(List<&2, Nat>, Nat.is_lt(a, b), _ => HsList.rangeUp(HsList.rangeBy.n(a, c, up), a, up), _ => HsList.rangeDown(HsList.rangeBy.n(c, a, dn), a, dn))

def HsInt.rangeBy.go(n: Nat, +a: HsInt, +d: HsInt) -> List<&2, HsInt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      a <> HsInt.rangeBy.go(p, HsInt.add(a, d), d)

# the steps of d (its size) in the count of c - a toward it
def HsInt.rangeBy.n(+m: HsInt, d: Nat) -> Nat:
  Bool.pick(Nat, HsInt.isneg(m), 0n, 1n+Nat.div(HsInt.mag(m), d))

def HsInt.rangeBy(+a: HsInt, +b: HsInt, +c: HsInt) -> List<&2, HsInt>:
  +d = HsInt.sub(b, a)
  +m = Bool.pick(HsInt, HsInt.isneg(d), HsInt.sub(a, c), HsInt.sub(c, a))
  HsInt.rangeBy.go(HsInt.rangeBy.n(m, HsInt.mag(d)), a, d)

# even and odd at Nat
def HsNum.even(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.not(HsNum.even(p))

def HsNum.odd(n: Nat) -> Bool:
  Bool.not(HsNum.even(n))
