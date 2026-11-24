import Base
import ../Core.bend as C

# a is b where a answers (b may answer more: Haskell's laziness)
def Le(a: Maybe<&2, C.HV>, b: Maybe<&2, C.HV>) -> Type:
  match a:
    case None{}:
      Unit
    case Some{u}:
      {Some{u} == b : Maybe<&2, C.HV>}

def refl(a: Maybe<&2, C.HV>) -> Le(a, a):
  match a:
    case None{}:
      Unit{}
    case Some{u}:
      {==}

# a context k of a stuck m: m is below n, so k(m) is below r when k(n) and
# k(None) are
def cut(-k: Maybe<&2, C.HV> -> Maybe<&2, C.HV>, m: Maybe<&2, C.HV>, -n: Maybe<&2, C.HV>, -r: Maybe<&2, C.HV>, e: Le(m, n), d: Le(k(n), r), z: Le(k(None{}), r)) -> Le(k(m), r):
  match m:
    case None{}:
      z
    case Some{u}:
      %Equal.sym(Maybe<&2, C.HV>, Some{u}, n, e) : Le(k(_), r)
      d

# a bind of a stuck m below n
def bind(-k: C.HV -> Maybe<&2, C.HV>, m: Maybe<&2, C.HV>, -n: Maybe<&2, C.HV>, -r: Maybe<&2, C.HV>, e: Le(m, n), d: Le(Maybe.bind(&2, C.HV, C.HV, n, k), r)) -> Le(Maybe.bind(&2, C.HV, C.HV, m, k), r):
  match m:
    case None{}:
      Unit{}
    case Some{u}:
      %Equal.sym(Maybe<&2, C.HV>, Some{u}, n, e) : Le(Maybe.bind(&2, C.HV, C.HV, _, k), r)
      d
