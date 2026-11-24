import Base
import ../Core.bend as C

def unit(x: Unit) -> C.HV:
  match x:
    case Unit{}:
      C.HvUnit{}

def pair(~A: Data, ~B: Data, ~f: A -> C.HV, ~g: B -> C.HV, p: Sigma<&2, &2, A, _ => B>) -> C.HV:
  match p:
    case Tuple{a, b}:
      C.HvPair{f(a), g(b)}

def either(~A: Data, ~B: Data, ~f: A -> C.HV, ~g: B -> C.HV, p: Either<&2, &2, A, B>) -> C.HV:
  match p:
    case Inl{a}:
      C.HvInl{f(a)}
    case Inr{b}:
      C.HvInr{g(b)}

def list(~A: Data, ~f: A -> C.HV, xs: List<&2, A>) -> C.HV:
  match xs:
    case Nil{}:
      C.HvNil{}
    case Con{h, t}:
      C.HvCons{f(h), list(~A, ~f, t)}

def err(~A: Data, ~f: A -> C.HV, r: Either<&2, &2, List<&2, Char>, A>) -> Maybe<&2, C.HV>:
  match r:
    case Inl{m}:
      None{}
    case Inr{a}:
      Some{f(a)}
