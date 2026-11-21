# Haskell's Rational (Data.Ratio's Ratio Integer) as GHC keeps it: a
# fraction num / den in lowest terms with den at least 1, so each rational
# is one term and two are equal when their fields are. A zero denominator
# (x / 0, n % 0) is GHC's error "Ratio has zero denominator"; here it
# answers 0, the type's default, as a fuelled def does at the end of its
# fuel (an error is out of this translation's reach).
type HsRational is Data:
  HsRational{num: HsInt, den: Nat}

# Euclid's gcd, fuelled by b + 1: each step's b is smaller than the last
def HsRational.gcd.go(fuel: Nat, a: Nat, b: Nat) -> Nat:
  match fuel b:
    case 0n _:
      a
    case _ 0n:
      a
    case 1n+p 1n+(+q):
      HsRational.gcd.go(p, 1n+q, Nat.mod(a, 1n+q))

def HsRational.gcd(+a: Nat, +b: Nat) -> Nat:
  HsRational.gcd.go(1n+b, a, b)

def HsRational.zero() -> HsRational:
  HsRational{HsInt.Pos{0n}, 1n}

def HsRational.mk.at(+g: Nat, +n: HsInt, +d: Nat) -> HsRational:
  match g:
    case 0n:
      HsRational.zero()
    case 1n+k:
      HsRational{HsInt.mul.sign(HsInt.isneg(n), Nat.div(HsInt.mag(n), g)), Nat.div(d, g)}

# n / d in lowest terms (GHC's reduce)
def HsRational.mk(+n: HsInt, +d: Nat) -> HsRational:
  match d:
    case 0n:
      HsRational.zero()
    case 1n+k:
      HsRational.mk.at(HsRational.gcd(HsInt.mag(n), d), n, d)

def HsRational.of(n: HsInt) -> HsRational:
  HsRational{n, 1n}

def HsRational.numerator(r: HsRational) -> HsInt:
  match r:
    case HsRational{p, q}:
      p

def HsRational.denominator(r: HsRational) -> HsInt:
  match r:
    case HsRational{p, q}:
      HsInt.Pos{q}

def HsRational.add(a: HsRational, b: HsRational) -> HsRational:
  match a b:
    case HsRational{p, +q} HsRational{r, +s}:
      HsRational.mk(HsInt.add(HsInt.mul(p, HsInt.Pos{s}), HsInt.mul(r, HsInt.Pos{q})), Nat.mul(q, s))

def HsRational.negate(a: HsRational) -> HsRational:
  match a:
    case HsRational{p, q}:
      HsRational{HsInt.negate(p), q}

def HsRational.sub(a: HsRational, b: HsRational) -> HsRational:
  HsRational.add(a, HsRational.negate(b))

def HsRational.mul(a: HsRational, b: HsRational) -> HsRational:
  match a b:
    case HsRational{p, q} HsRational{r, s}:
      HsRational.mk(HsInt.mul(p, r), Nat.mul(q, s))

# (p / q) / (r / s) = p s / q r, the sign r's
def HsRational.div(a: HsRational, b: HsRational) -> HsRational:
  match a b:
    case HsRational{p, q} HsRational{+r, s}:
      HsRational.mk(HsInt.mul(HsInt.mul(p, HsInt.Pos{s}), HsInt.signum(r)), Nat.mul(q, HsInt.mag(r)))

def HsRational.abs(a: HsRational) -> HsRational:
  match a:
    case HsRational{p, q}:
      HsRational{HsInt.abs(p), q}

def HsRational.signum(a: HsRational) -> HsRational:
  match a:
    case HsRational{p, q}:
      HsRational{HsInt.signum(p), 1n}

# p / q against r / s: p s against r q (q, s at least 1)
def HsRational.cmp(a: HsRational, b: HsRational) -> Cmp:
  match a b:
    case HsRational{p, q} HsRational{r, s}:
      HsInt.cmp(HsInt.mul(p, HsInt.Pos{s}), HsInt.mul(r, HsInt.Pos{q}))

def HsRational.is_eq(a: HsRational, b: HsRational) -> Bool:
  Cmp.is_eq(HsRational.cmp(a, b))

def HsRational.is_ne(a: HsRational, b: HsRational) -> Bool:
  Bool.not(Cmp.is_eq(HsRational.cmp(a, b)))

def HsRational.is_lt(a: HsRational, b: HsRational) -> Bool:
  Cmp.is_lt(HsRational.cmp(a, b))

def HsRational.is_le(a: HsRational, b: HsRational) -> Bool:
  Cmp.is_le(HsRational.cmp(a, b))

def HsRational.is_gt(a: HsRational, b: HsRational) -> Bool:
  Cmp.is_gt(HsRational.cmp(a, b))

def HsRational.is_ge(a: HsRational, b: HsRational) -> Bool:
  Cmp.is_ge(HsRational.cmp(a, b))

def HsRational.max(+a: HsRational, +b: HsRational) -> HsRational:
  Bool.pick(HsRational, Cmp.is_ge(HsRational.cmp(a, b)), a, b)

def HsRational.min(+a: HsRational, +b: HsRational) -> HsRational:
  Bool.pick(HsRational, Cmp.is_le(HsRational.cmp(a, b)), a, b)

# GHC.Real's showsPrec: showParen (d > 7) (showsPrec 8 p . (" % " ++) .
# showsPrec 8 q)
def HsRational.shows(+d: HsInt, x: HsRational, r: List<&2, Char>) -> List<&2, Char>:
  match x:
    case HsRational{p, q}:
      HsShow.paren(HsInt.is_gt(d, HsInt.Pos{7n}), s => HsShow.int(HsInt.Pos{8n}, p, List.append(&2, Char, String.to_list(" % "), HsShow.int(HsInt.Pos{8n}, HsInt.Pos{q}, s))), r)

def HsRational.show(x: HsRational) -> List<&2, Char>:
  HsRational.shows(HsInt.Pos{0n}, x, Nil{})

# Data.Ratio's n % d, the sign on the numerator
def HsInt.ratio(+a: HsInt, +b: HsInt) -> HsRational:
  HsRational.mk(HsInt.mul.sign(Bool.xor(HsInt.isneg(a), HsInt.isneg(b)), HsInt.mag(a)), HsInt.mag(b))

def HsInt.gcd(+a: HsInt, +b: HsInt) -> HsInt:
  HsInt.Pos{HsRational.gcd(HsInt.mag(a), HsInt.mag(b))}

def HsInt.lcm.at(+g: Nat, +a: Nat, +b: Nat) -> HsInt:
  match g:
    case 0n:
      HsInt.Pos{0n}
    case 1n+k:
      HsInt.Pos{Nat.mul(Nat.div(a, g), b)}

def HsInt.lcm(+a: HsInt, +b: HsInt) -> HsInt:
  HsInt.lcm.at(HsRational.gcd(HsInt.mag(a), HsInt.mag(b)), HsInt.mag(a), HsInt.mag(b))
