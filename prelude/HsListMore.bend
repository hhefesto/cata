# Data.List's splitAt, transpose, dropWhileEnd, uncons, scanl and elemIndex
# (base's definitions; transpose's recursion is bounded by how many elements
# and lists there are, which each step takes one of)
def HsList.splitAt.put(-A: Data, h: A, p: Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:
  match p:
    case Tuple{a, b}:
      Tuple{h <> a, b}

def HsList.splitAt(~A: Data, n: Nat, xs: List<&2, A>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:
  match n xs:
    case 0n ys:
      Tuple{Nil{}, ys}
    case 1n+p Nil{}:
      Tuple{Nil{}, Nil{}}
    case 1n+p h <> t:
      HsList.splitAt.put(A, h, HsList.splitAt(~A, p, t))

def HsList.heads(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  match xss:
    case Nil{}:
      Nil{}
    case Con{Nil{}, t}:
      HsList.heads(A, t)
    case Con{Con{h, _}, t}:
      h <> HsList.heads(A, t)

def HsList.tails1(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  match xss:
    case Nil{}:
      Nil{}
    case Con{Nil{}, t}:
      HsList.tails1(A, t)
    case Con{Con{_, r}, t}:
      r <> HsList.tails1(A, t)

def HsList.size2(-A: Data, xss: List<&2, List<&2, A>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case h <> t:
      1n+Nat.add(List.length(&2, A, h), HsList.size2(A, t))

def HsList.transpose.go(-A: Data, fuel: Nat, xss: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  match fuel xss:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{Nil{}, t}:
      HsList.transpose.go(A, p, t)
    case 1n+p Con{Con{x, xs}, +t}:
      (x <> HsList.heads(A, t)) <> HsList.transpose.go(A, p, xs <> HsList.tails1(A, t))

def HsList.transpose(~A: Data, +xss: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  HsList.transpose.go(A, HsList.size2(A, xss), xss)

def HsList.dropWhileEnd.put(-A: Data, b: Bool, h: A, r: List<&2, A>) -> List<&2, A>:
  match b r:
    case True{} Nil{}:
      Nil{}
    case False{} Nil{}:
      h <> Nil{}
    case _ Con{x, t}:
      h <> x <> t

def HsList.dropWhileEnd(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      HsList.dropWhileEnd.put(A, p(h), h, HsList.dropWhileEnd(~A, ~p, t))

def HsList.uncons(~A: Data, xs: List<&2, A>) -> Maybe<&2, Sigma<&2, &2, A, _ => List<&2, A>>>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{Tuple{h, t}}

def HsList.scanl.go(~B: Data, ~A: Data, ~f: B -> A -> B, xs: List<&2, A>, +q: B) -> List<&2, B>:
  match xs:
    case Nil{}:
      q <> Nil{}
    case h <> t:
      q <> HsList.scanl.go(~B, ~A, ~f, t, f(q)(h))

def HsList.scanl(~B: Data, ~A: Data, ~f: B -> A -> B, q: B, xs: List<&2, A>) -> List<&2, B>:
  HsList.scanl.go(~B, ~A, ~f, xs, q)

def HsList.elemIndex.go(~K: Data, ~eq: K -> K -> Bool, +x: K, xs: List<&2, K>, +n: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      HsBool.if(Maybe<&2, Nat>, eq(x)(h), _ => Some{n}, _ => HsList.elemIndex.go(~K, ~eq, x, t, 1n+n))

def HsList.elemIndex(~K: Data, ~eq: K -> K -> Bool, x: K, xs: List<&2, K>) -> Maybe<&2, Nat>:
  HsList.elemIndex.go(~K, ~eq, x, xs, 0n)
