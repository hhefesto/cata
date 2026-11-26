#@after HsCmp.char
# Haskell's Int and Integer as an integer past 2^48: what a translated program
# runs on. Bend's machine holds a Nat in one word and stops a program whose Nat
# goes past 2^48 - 1 ("a Nat past largest immediate"); telomare's Size numbers
# the input's positions 2n + 1 and 2n + 2 as an Integer, past 2^48 in a deep
# input. Pos{n} and Neg{n} are HsPrelude's (n below 2^48, Neg's at least 1);
# Big is an integer of size 2^48 or more: its limbs, base 2^24, lowest first,
# at least three, the last not 0. So each integer is still one term, and below
# 2^48 every def here answers what HsPrelude's does (tests/ints).
# HsPrelude's own HsInt (Pos and Neg alone) is what the laws are told on;
# tools/run-prelude.zsh puts these in its place in a package that is to run.
# A Nat of an integer past 2^48 (mag, count) still stops the machine, as any
# Nat past 2^48 does.
type HsInt is Data:
  HsInt.Pos{n: Nat}
  HsInt.Neg{n: Nat}
  HsInt.Big{neg: Bool, ls: List<&2, Nat>}

# a quotient and a remainder, each as limbs
type HsInt.L.QR is Data:
  HsInt.L.QR{q: List<&2, Nat>, r: List<&2, Nat>}

# 2^47: two sizes below it add below 2^48
def HsInt.L.half() -> Nat:
  Nat.mul(8388608n, 16777216n)

def HsInt.L.lt47(+m: Nat, +n: Nat) -> Bool:
  Bool.and(Nat.is_lt(m, HsInt.L.half()), Nat.is_lt(n, HsInt.L.half()))

# two sizes below 2^24 multiply below 2^48
def HsInt.L.lt24(+m: Nat, +n: Nat) -> Bool:
  Bool.and(Nat.is_lt(m, 16777216n), Nat.is_lt(n, 16777216n))

# x below the limbs r (no high 0 limb): nothing when both are 0
def HsInt.L.cons(x: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match x r:
    case 0n Nil{}:
      Nil{}
    case x r:
      x <> r

# limbs without their high 0 limbs
def HsInt.L.norm(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      HsInt.L.cons(x, HsInt.L.norm(t))

# the limbs of a Nat below 2^48
def HsInt.L.of(+n: Nat) -> List<&2, Nat>:
  HsInt.L.cons(Nat.mod(n, 16777216n), HsInt.L.cons(Nat.div(n, 16777216n), Nil{}))

# the Nat of limbs (past 2^48 - 1 the machine stops)
def HsInt.L.nat(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(x, Nat.mul(HsInt.L.nat(t), 16777216n))

def HsInt.L.len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      1n+HsInt.L.len(t)

def HsInt.L.small(a: HsInt) -> Bool:
  match a:
    case HsInt.Big{g, ls}:
      False{}
    case a:
      True{}

# is it below 0 (HsInt.isneg, before it)
def HsInt.L.sgn(a: HsInt) -> Bool:
  match a:
    case HsInt.Pos{n}:
      False{}
    case HsInt.Neg{n}:
      True{}
    case HsInt.Big{g, ls}:
      g

# an integer's size as limbs
def HsInt.L.mag(a: HsInt) -> List<&2, Nat>:
  match a:
    case HsInt.Pos{n}:
      HsInt.L.of(n)
    case HsInt.Neg{n}:
      HsInt.L.of(n)
    case HsInt.Big{g, ls}:
      ls

# xs + c (c below 2^48)
def HsInt.L.inc(xs: List<&2, Nat>, c: Nat) -> List<&2, Nat>:
  match xs c:
    case xs 0n:
      xs
    case Nil{} c:
      HsInt.L.of(c)
    case x <> t c:
      +s = Nat.add(x, c)
      Nat.mod(s, 16777216n) <> HsInt.L.inc(t, Nat.div(s, 16777216n))

# xs + ys + c (c 0 or 1)
def HsInt.L.add(xs: List<&2, Nat>, ys: List<&2, Nat>, c: Nat) -> List<&2, Nat>:
  match xs ys:
    case Nil{} ys:
      HsInt.L.inc(ys, c)
    case xs Nil{}:
      HsInt.L.inc(xs, c)
    case x <> xt y <> yt:
      +s = Nat.add(Nat.add(x, y), c)
      Nat.mod(s, 16777216n) <> HsInt.L.add(xt, yt, Nat.div(s, 16777216n))

# xs - b (b 0 or 1, xs at least b)
def HsInt.L.dec(xs: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match xs b:
    case xs 0n:
      xs
    case Nil{} b:
      Nil{}
    case x <> t b:
      +s = Nat.sub(Nat.add(x, 16777216n), b)
      Nat.mod(s, 16777216n) <> HsInt.L.dec(t, Nat.sub(1n, Nat.div(s, 16777216n)))

# xs - ys - b (b 0 or 1, xs at least ys + b); it may have high 0 limbs
def HsInt.L.sub(xs: List<&2, Nat>, ys: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match xs ys:
    case Nil{} ys:
      Nil{}
    case xs Nil{}:
      HsInt.L.dec(xs, b)
    case x <> xt y <> yt:
      +s = Nat.sub(Nat.add(x, 16777216n), Nat.add(y, b))
      Nat.mod(s, 16777216n) <> HsInt.L.sub(xt, yt, Nat.sub(1n, Nat.div(s, 16777216n)))

def HsInt.L.cmp.at(c: Cmp, acc: Cmp) -> Cmp:
  match c:
    case EQ{}:
      acc
    case c:
      c

# compare limbs (no high 0 limbs), acc the comparison of the limbs below
def HsInt.L.cmp(xs: List<&2, Nat>, ys: List<&2, Nat>, acc: Cmp) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      acc
    case Nil{} _:
      LT{}
    case _ Nil{}:
      GT{}
    case x <> xt y <> yt:
      HsInt.L.cmp(xt, yt, HsInt.L.cmp.at(Nat.cmp(x, y), acc))

# ys * x + c (x and c below 2^24)
def HsInt.L.scale(ys: List<&2, Nat>, +x: Nat, c: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      HsInt.L.of(c)
    case y <> yt:
      +s = Nat.add(Nat.mul(y, x), c)
      Nat.mod(s, 16777216n) <> HsInt.L.scale(yt, x, Nat.div(s, 16777216n))

def HsInt.L.mul(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> xt:
      HsInt.L.add(HsInt.L.scale(ys, x, 0n), HsInt.L.cons(0n, HsInt.L.norm(HsInt.L.mul(xt, ys))), 0n)

def HsInt.L.rev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      HsInt.L.rev(t, x <> acc)

# ms (highest limb first) over d (1 to 2^24 - 1): r the remainder so far
# (below d), q the quotient's limbs so far (lowest first)
def HsInt.L.divs(ms: List<&2, Nat>, +d: Nat, r: Nat, q: List<&2, Nat>) -> HsInt.L.QR:
  match ms:
    case Nil{}:
      HsInt.L.QR{HsInt.L.norm(q), HsInt.L.of(r)}
    case m <> t:
      +s = Nat.add(Nat.mul(r, 16777216n), m)
      HsInt.L.divs(t, d, Nat.mod(s, d), Nat.div(s, d) <> q)

# the k lowest bits of x, highest first, before acc
def HsInt.L.bits.of(k: Nat, +x: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      acc
    case 1n+p:
      HsInt.L.bits.of(p, Nat.div(x, 2n), Nat.mod(x, 2n) <> acc)

# the bits of limbs xs (lowest first), highest first, before acc
def HsInt.L.bits(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      HsInt.L.bits(t, HsInt.L.bits.of(24n, x, acc))

# long division a bit at a time: bs the dividend's bits (highest first), d
# the divisor (no high 0 limb, not 0), q and r so far
def HsInt.L.divb(bs: List<&2, Nat>, +d: List<&2, Nat>, q: List<&2, Nat>, r: List<&2, Nat>) -> HsInt.L.QR:
  match bs:
    case Nil{}:
      HsInt.L.QR{q, r}
    case b <> t:
      +r2 = HsInt.L.scale(r, 2n, b)
      +ge = Cmp.is_ge(HsInt.L.cmp(r2, d, EQ{}))
      HsInt.L.divb(t, d, HsInt.L.scale(q, 2n, Bool.pick(Nat, ge, 1n, 0n)), HsBool.if(List<&2, Nat>, ge, _ => HsInt.L.norm(HsInt.L.sub(r2, d, 0n)), _ => r2))

# xs over ys (both without high 0 limbs); over 0 the quotient is 0
def HsInt.L.divmod(+xs: List<&2, Nat>, ys: List<&2, Nat>) -> HsInt.L.QR:
  match ys:
    case Nil{}:
      HsInt.L.QR{Nil{}, xs}
    case y <> t:
      match t:
        case Nil{}:
          HsInt.L.divs(HsInt.L.rev(xs, Nil{}), y, 0n, Nil{})
        case u <> w:
          HsInt.L.divb(HsInt.L.bits(xs, Nil{}), y <> (u <> w), Nil{}, Nil{})

def HsInt.L.QR.q(a: HsInt.L.QR) -> List<&2, Nat>:
  match a:
    case HsInt.L.QR{q, r}:
      q

def HsInt.L.QR.r(a: HsInt.L.QR) -> List<&2, Nat>:
  match a:
    case HsInt.L.QR{q, r}:
      r

# the decimal digits of limbs xs before acc, at most k of them
def HsInt.L.show.go(k: Nat, xs: List<&2, Nat>, acc: List<&2, Char>) -> List<&2, Char>:
  match k xs:
    case _ Nil{}:
      acc
    case 0n _:
      acc
    case 1n+p xs:
      +qr = HsInt.L.divs(HsInt.L.rev(xs, Nil{}), 10n, 0n, Nil{})
      HsInt.L.show.go(p, HsInt.L.QR.q(qr), List.append(&2, Char, String.to_list(Nat.show(HsInt.L.nat(HsInt.L.QR.r(qr)))), acc))

# the digits of limbs not 0 (a limb has at most 8)
def HsInt.L.digits(+xs: List<&2, Nat>) -> List<&2, Char>:
  HsInt.L.show.go(1n+Nat.mul(8n, HsInt.L.len(xs)), xs, Nil{})

#@after HsInt.neg.of
def HsInt.negate(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{n}:
      HsInt.neg.of(n)
    case HsInt.Neg{n}:
      HsInt.Pos{n}
    case HsInt.Big{g, ls}:
      HsInt.Big{Bool.not(g), ls}

#@after HsInt.nsub
def HsInt.mul.sign(neg: Bool, n: Nat) -> HsInt:
  match neg:
    case True{}:
      HsInt.neg.of(n)
    case False{}:
      HsInt.Pos{n}

def HsInt.L.mk.at(neg: Bool, xs: List<&2, Nat>) -> HsInt:
  match xs:
    case Nil{}:
      HsInt.Pos{0n}
    case x <> t:
      match t:
        case Nil{}:
          HsInt.mul.sign(neg, x)
        case y <> u:
          match u:
            case Nil{}:
              HsInt.mul.sign(neg, Nat.add(x, Nat.mul(y, 16777216n)))
            case z <> w:
              HsInt.Big{neg, x <> (y <> (z <> w))}

# the integer of a sign and limbs
def HsInt.L.mk(neg: Bool, xs: List<&2, Nat>) -> HsInt:
  HsInt.L.mk.at(neg, HsInt.L.norm(xs))

# signs unlike: the larger's sign, the difference of the sizes
def HsInt.L.addi.at(c: Cmp, an: Bool, +am: List<&2, Nat>, bn: Bool, +bm: List<&2, Nat>) -> HsInt:
  match c:
    case LT{}:
      HsInt.L.mk(bn, HsInt.L.sub(bm, am, 0n))
    case EQ{}:
      HsInt.Pos{0n}
    case GT{}:
      HsInt.L.mk(an, HsInt.L.sub(am, bm, 0n))

# a sign and limbs plus a sign and limbs
def HsInt.L.addi(+an: Bool, +am: List<&2, Nat>, +bn: Bool, +bm: List<&2, Nat>) -> HsInt:
  HsBool.if(HsInt, Bool.xor(an, bn), _ => HsInt.L.addi.at(HsInt.L.cmp(am, bm, EQ{}), an, am, bn, bm), _ => HsInt.L.mk(an, HsInt.L.add(am, bm, 0n)))

def HsInt.add(a: HsInt, b: HsInt) -> HsInt:
  match a b:
    case HsInt.Pos{+m} HsInt.Pos{+n}:
      HsBool.if(HsInt, HsInt.L.lt47(m, n), _ => HsInt.Pos{Nat.add(m, n)}, _ => HsInt.L.mk(False{}, HsInt.L.add(HsInt.L.of(m), HsInt.L.of(n), 0n)))
    case HsInt.Neg{+m} HsInt.Neg{+n}:
      HsBool.if(HsInt, HsInt.L.lt47(m, n), _ => HsInt.Neg{Nat.add(m, n)}, _ => HsInt.L.mk(True{}, HsInt.L.add(HsInt.L.of(m), HsInt.L.of(n), 0n)))
    case HsInt.Pos{m} HsInt.Neg{n}:
      HsInt.nsub(m, n)
    case HsInt.Neg{m} HsInt.Pos{n}:
      HsInt.nsub(n, m)
    case +a +b:
      HsInt.L.addi(HsInt.L.sgn(a), HsInt.L.mag(a), HsInt.L.sgn(b), HsInt.L.mag(b))

#@after HsInt.sub
def HsInt.mul(a: HsInt, b: HsInt) -> HsInt:
  match a b:
    case HsInt.Pos{+m} HsInt.Pos{+n}:
      HsBool.if(HsInt, HsInt.L.lt24(m, n), _ => HsInt.Pos{Nat.mul(m, n)}, _ => HsInt.L.mk(False{}, HsInt.L.mul(HsInt.L.of(m), HsInt.L.of(n))))
    case HsInt.Neg{+m} HsInt.Neg{+n}:
      HsBool.if(HsInt, HsInt.L.lt24(m, n), _ => HsInt.Pos{Nat.mul(m, n)}, _ => HsInt.L.mk(False{}, HsInt.L.mul(HsInt.L.of(m), HsInt.L.of(n))))
    case HsInt.Pos{+m} HsInt.Neg{+n}:
      HsBool.if(HsInt, HsInt.L.lt24(m, n), _ => HsInt.neg.of(Nat.mul(m, n)), _ => HsInt.L.mk(True{}, HsInt.L.mul(HsInt.L.of(m), HsInt.L.of(n))))
    case HsInt.Neg{+m} HsInt.Pos{+n}:
      HsBool.if(HsInt, HsInt.L.lt24(m, n), _ => HsInt.neg.of(Nat.mul(m, n)), _ => HsInt.L.mk(True{}, HsInt.L.mul(HsInt.L.of(m), HsInt.L.of(n))))
    case +a +b:
      HsInt.L.mk(Bool.xor(HsInt.L.sgn(a), HsInt.L.sgn(b)), HsInt.L.mul(HsInt.L.mag(a), HsInt.L.mag(b)))

#@after HsInt.mul
def HsInt.abs(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{n}:
      HsInt.Pos{n}
    case HsInt.Neg{n}:
      HsInt.Pos{n}
    case HsInt.Big{g, ls}:
      HsInt.Big{False{}, ls}

def HsInt.signum(a: HsInt) -> HsInt:
  match a:
    case HsInt.Pos{Zero{}}:
      HsInt.Pos{Zero{}}
    case HsInt.Pos{Succ{p}}:
      HsInt.Pos{1n}
    case HsInt.Neg{n}:
      HsInt.Neg{1n}
    case HsInt.Big{g, ls}:
      HsInt.mul.sign(g, 1n)

# a sign and limbs against a sign and limbs
def HsInt.L.cmpi(an: Bool, am: List<&2, Nat>, bn: Bool, bm: List<&2, Nat>) -> Cmp:
  match an bn:
    case False{} True{}:
      GT{}
    case True{} False{}:
      LT{}
    case False{} False{}:
      HsInt.L.cmp(am, bm, EQ{})
    case True{} True{}:
      HsInt.L.cmp(bm, am, EQ{})

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
    case +a +b:
      HsInt.L.cmpi(HsInt.L.sgn(a), HsInt.L.mag(a), HsInt.L.sgn(b), HsInt.L.mag(b))

#@after HsInt.min
def HsInt.mag(a: HsInt) -> Nat:
  match a:
    case HsInt.Pos{n}:
      n
    case HsInt.Neg{n}:
      n
    case HsInt.Big{g, ls}:
      HsInt.L.nat(ls)

def HsInt.isneg(a: HsInt) -> Bool:
  match a:
    case HsInt.Pos{n}:
      False{}
    case HsInt.Neg{n}:
      True{}
    case HsInt.Big{g, ls}:
      g

#@after HsInt.isneg
# quot and rem truncate toward zero (HsPrelude's div and mod are of these)
def HsInt.quot(+a: HsInt, +b: HsInt) -> HsInt:
  HsBool.if(HsInt, Bool.and(HsInt.L.small(a), HsInt.L.small(b)), _ => HsInt.mul.sign(Bool.xor(HsInt.isneg(a), HsInt.isneg(b)), Nat.div(HsInt.mag(a), HsInt.mag(b))), _ => HsInt.L.mk(Bool.xor(HsInt.isneg(a), HsInt.isneg(b)), HsInt.L.QR.q(HsInt.L.divmod(HsInt.L.mag(a), HsInt.L.mag(b)))))

def HsInt.rem(+a: HsInt, +b: HsInt) -> HsInt:
  HsBool.if(HsInt, Bool.and(HsInt.L.small(a), HsInt.L.small(b)), _ => HsInt.mul.sign(HsInt.isneg(a), Nat.mod(HsInt.mag(a), HsInt.mag(b))), _ => HsInt.L.mk(HsInt.isneg(a), HsInt.L.QR.r(HsInt.L.divmod(HsInt.L.mag(a), HsInt.L.mag(b)))))

#@after HsInt.pred
def HsInt.show(a: HsInt) -> List<&2, Char>:
  match a:
    case HsInt.Pos{n}:
      String.to_list(Nat.show(n))
    case HsInt.Neg{n}:
      '-' <> String.to_list(Nat.show(n))
    case HsInt.Big{g, ls}:
      match g:
        case False{}:
          HsInt.L.digits(ls)
        case True{}:
          '-' <> HsInt.L.digits(ls)

def HsInt.count(a: HsInt) -> Nat:
  match a:
    case HsInt.Pos{n}:
      n
    case HsInt.Neg{n}:
      0n
    case HsInt.Big{g, ls}:
      match g:
        case False{}:
          HsInt.L.nat(ls)
        case True{}:
          0n

#@after HsShow.digits
def HsShow.int(d: HsInt, n: HsInt, r: List<&2, Char>) -> List<&2, Char>:
  match n:
    case HsInt.Pos{k}:
      List.append(&2, Char, HsShow.digits(k), r)
    case HsInt.Neg{k}:
      HsShow.paren(HsInt.is_gt(d, HsInt.Pos{6n}), s => '-' <> List.append(&2, Char, HsShow.digits(k), s), r)
    case HsInt.Big{g, ls}:
      match g:
        case False{}:
          List.append(&2, Char, HsInt.L.digits(ls), r)
        case True{}:
          HsShow.paren(HsInt.is_gt(d, HsInt.Pos{6n}), s => '-' <> List.append(&2, Char, HsInt.L.digits(ls), s), r)

#@after HsList.index.go
# (no list holds 2^48 things)
def HsList.index(~A: Data, xs: List<&2, A>, n: HsInt) -> Either<&2, &2, List<&2, Char>, A>:
  match n:
    case HsInt.Pos{k}:
      HsList.index.go(~A, xs, k)
    case HsInt.Neg{k}:
      Inl{String.to_list("Prelude.!!: negative index")}
    case HsInt.Big{g, ls}:
      match g:
        case False{}:
          Inl{String.to_list("Prelude.!!: index too large")}
        case True{}:
          Inl{String.to_list("Prelude.!!: negative index")}

