# adj/gen/S.bend: cata's own partial subtraction, the prelude's HsNum.sub
# (../l/HsPrelude.bend is cata's; cert.zsh puts this file beside it), is the
# model's, at every pair: the number where a >= b, an error below.

import Base
import ../Core.bend as C
import ./R.bend as R
import ../l/HsPrelude.bend as H

# the model's, the test by Nat.is_lt
def m(+a: Nat, +b: Nat) -> Maybe<&2, C.HV>:
  C.h.pv(C.p.of(C.p.lt.at(Nat.is_lt(a, b), a, b)))

def under(c: Bool, -p: Nat, -q: Nat) -> {C.p.lt.at(c, p, q) == C.p.lt.at(c, 1n+p, 1n+q) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def sub(+a: Nat, +b: Nat) -> {R.err(~Nat, ~x => C.HvNat{x}, H.HsNum.sub(a, b)) == m(a, b) : Maybe<&2, C.HV>}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %under(Nat.is_lt(p, q), p, q) : {R.err(~Nat, ~x => C.HvNat{x}, H.HsNum.sub(p, q)) == C.h.pv(C.p.of(_)) : Maybe<&2, C.HV>}
      sub(p, q)
