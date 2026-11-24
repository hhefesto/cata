# Written by adj/hsint.zsh from bend/Fold.bend and prelude/HsPartial.bend.
import Base

# Haskell's Int and Integer as an integer: Pos{n} is n, Neg{n} is -n (n at
# least 1), so each integer is one term.  (Int's 64-bit wrap-around is not
# modelled: an Int that would overflow is out of this translation's reach.)
type HsInt is Data:
  HsInt.Pos{n: Nat}
  HsInt.Neg{n: Nat}

def HsInt.of(n: Nat) -> HsInt:
  HsInt.Pos{n}

# -n for a Nat n
def HsInt.neg.of(n: Nat) -> HsInt:
  match n:
    case Zero{}:
      HsInt.Pos{Zero{}}
    case Succ{p}:
      HsInt.Neg{Succ{p}}

def HsInt.negate(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{n}:
      HsInt.neg.of(n)
    case HsInt.Neg{n}:
      HsInt.Pos{n}

# a - b for Nats, as an integer
def HsInt.nsub(a: Nat, b: Nat) -> HsInt:
  match a b:
    case Zero{} m:
      HsInt.neg.of(m)
    case n Zero{}:
      HsInt.Pos{n}
    case Succ{p} Succ{q}:
      HsInt.nsub(p, q)

def HsInt.add(a: HsInt, b: HsInt) -> HsInt:
  match a b:
    case HsInt.Pos{m} HsInt.Pos{n}:
      HsInt.Pos{Nat.add(m, n)}
    case HsInt.Neg{m} HsInt.Neg{n}:
      HsInt.Neg{Nat.add(m, n)}
    case HsInt.Pos{m} HsInt.Neg{n}:
      HsInt.nsub(m, n)
    case HsInt.Neg{m} HsInt.Pos{n}:
      HsInt.nsub(n, m)

def HsInt.sub(a: HsInt, b: HsInt) -> HsInt:
  HsInt.add(a, HsInt.negate(b))

def HsInt.mul.sign(neg: Bool, n: Nat) -> HsInt:
  match neg:
    case True{}:
      HsInt.neg.of(n)
    case False{}:
      HsInt.Pos{n}

def HsInt.mul(a: HsInt, b: HsInt) -> HsInt:
  match a b:
    case HsInt.Pos{m} HsInt.Pos{n}:
      HsInt.Pos{Nat.mul(m, n)}
    case HsInt.Neg{m} HsInt.Neg{n}:
      HsInt.Pos{Nat.mul(m, n)}
    case HsInt.Pos{m} HsInt.Neg{n}:
      HsInt.neg.of(Nat.mul(m, n))
    case HsInt.Neg{m} HsInt.Pos{n}:
      HsInt.neg.of(Nat.mul(m, n))

def HsInt.abs(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{n}:
      HsInt.Pos{n}
    case HsInt.Neg{n}:
      HsInt.Pos{n}

def HsInt.signum(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{Zero{}}:
      HsInt.Pos{Zero{}}
    case HsInt.Pos{Succ{p}}:
      HsInt.Pos{1n}
    case HsInt.Neg{n}:
      HsInt.Neg{1n}

def HsInt.cmp(a: HsInt, b: HsInt) -> Cmp:
  match a b:
    case HsInt.Pos{m} HsInt.Pos{n}:
      Nat.cmp(m, n)
    case HsInt.Neg{m} HsInt.Neg{n}:
      Nat.cmp(n, m)
    case HsInt.Pos{m} HsInt.Neg{n}:
      GT{}
    case HsInt.Neg{m} HsInt.Pos{n}:
      LT{}

def HsInt.is_eq(a: HsInt, b: HsInt) -> Bool:
  Cmp.is_eq(HsInt.cmp(a, b))

def HsInt.is_ne(a: HsInt, b: HsInt) -> Bool:
  Bool.not(Cmp.is_eq(HsInt.cmp(a, b)))

def HsInt.is_lt(a: HsInt, b: HsInt) -> Bool:
  Cmp.is_lt(HsInt.cmp(a, b))

def HsInt.is_le(a: HsInt, b: HsInt) -> Bool:
  Cmp.is_le(HsInt.cmp(a, b))

def HsInt.is_gt(a: HsInt, b: HsInt) -> Bool:
  Cmp.is_gt(HsInt.cmp(a, b))

def HsInt.is_ge(a: HsInt, b: HsInt) -> Bool:
  Cmp.is_ge(HsInt.cmp(a, b))

def HsInt.max(+a: HsInt, +b: HsInt) -> HsInt:
  Bool.pick(HsInt, Cmp.is_ge(HsInt.cmp(a, b)), a, b)

def HsInt.min(+a: HsInt, +b: HsInt) -> HsInt:
  Bool.pick(HsInt, Cmp.is_le(HsInt.cmp(a, b)), a, b)

def HsInt.mag(a: HsInt) -> Nat:
  match a:
    case HsInt.Pos{n}:
      n
    case HsInt.Neg{n}:
      n

def HsInt.isneg(a: HsInt) -> Bool:
  match a:
    case HsInt.Pos{n}:
      False{}
    case HsInt.Neg{n}:
      True{}

# quot and rem truncate toward zero; div and mod round toward minus
# infinity (Haskell's)
def HsInt.quot(+a: HsInt, +b: HsInt) -> HsInt:
  HsInt.mul.sign(Bool.xor(HsInt.isneg(a), HsInt.isneg(b)), Nat.div(HsInt.mag(a), HsInt.mag(b)))

def HsInt.rem(+a: HsInt, +b: HsInt) -> HsInt:
  HsInt.mul.sign(HsInt.isneg(a), Nat.mod(HsInt.mag(a), HsInt.mag(b)))

def HsInt.div(+a: HsInt, +b: HsInt) -> HsInt:
  +q = HsInt.quot(a, b)
  +r = HsInt.rem(a, b)
  Bool.pick(HsInt, Bool.and(Bool.not(HsInt.is_eq(r, HsInt.Pos{0n})), Bool.xor(HsInt.isneg(a), HsInt.isneg(b))), HsInt.sub(q, HsInt.Pos{1n}), q)

def HsInt.mod(+a: HsInt, +b: HsInt) -> HsInt:
  +r = HsInt.rem(a, b)
  Bool.pick(HsInt, Bool.and(Bool.not(HsInt.is_eq(r, HsInt.Pos{0n})), Bool.xor(HsInt.isneg(r), HsInt.isneg(b))), HsInt.add(r, b), r)

def HsInt.pow.go(+a: HsInt, n: Nat) -> HsInt:
  match n:
    case Zero{}:
      HsInt.Pos{1n}
    case Succ{p}:
      HsInt.mul(a, HsInt.pow.go(a, p))

# a ^ e (e at least 0)
def HsInt.pow(+a: HsInt, e: HsInt) -> HsInt:
  HsInt.pow.go(a, HsInt.mag(e))

def HsInt.succ(a: HsInt) -> HsInt:
  HsInt.add(a, HsInt.Pos{1n})

def HsInt.pred(a: HsInt) -> HsInt:
  HsInt.sub(a, HsInt.Pos{1n})

# show: the digits, after a minus when negative
def HsInt.show(a: HsInt) -> List<&2, Char>:
  match a:
    case HsInt.Pos{n}:
      String.to_list(Nat.show(n))
    case HsInt.Neg{n}:
      '-' <> String.to_list(Nat.show(n))

def HsInt.count(a: HsInt) -> Nat:
  match a:
    case HsInt.Pos{n}:
      n
    case HsInt.Neg{n}:
      0n

# [a .. b]
def HsInt.range.go(n: Nat, +a: HsInt) -> List<&2, HsInt>:
  match n:
    case Zero{}:
      Nil{}
    case Succ{p}:
      a <> HsInt.range.go(p, HsInt.succ(a))

def HsInt.range(+a: HsInt, +b: HsInt) -> List<&2, HsInt>:
  HsInt.range.go(HsInt.count(HsInt.sub(HsInt.succ(b), a)), a)

def HsNum.idiv(a: HsInt, b: HsInt) -> Either<&2, &2, List<&2, Char>, HsInt>:
  match b:
    case HsInt.Pos{0n}:
      Inl{String.to_list("divide by zero")}
    case c:
      Inr{HsInt.div(a, c)}

def HsNum.imod(a: HsInt, b: HsInt) -> Either<&2, &2, List<&2, Char>, HsInt>:
  match b:
    case HsInt.Pos{0n}:
      Inl{String.to_list("divide by zero")}
    case c:
      Inr{HsInt.mod(a, c)}

def HsNum.iquot(a: HsInt, b: HsInt) -> Either<&2, &2, List<&2, Char>, HsInt>:
  match b:
    case HsInt.Pos{0n}:
      Inl{String.to_list("divide by zero")}
    case c:
      Inr{HsInt.quot(a, c)}

def HsNum.irem(a: HsInt, b: HsInt) -> Either<&2, &2, List<&2, Char>, HsInt>:
  match b:
    case HsInt.Pos{0n}:
      Inl{String.to_list("divide by zero")}
    case c:
      Inr{HsInt.rem(a, c)}
