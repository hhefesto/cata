# Haskell's partial functions as failure values (PLAN.md, "Partial
# functions"): each answers Either<&2, &2, String, A>, Inl{GHC's message}
# where GHC throws its ErrorCall (the message alone: GHC keeps the call
# stack apart), Inr{the answer} else. A def that calls one answers such an
# Either itself, its partial calls bound with hs.either.bind (Fold.bend's
# partial pass, fd.pt).

# error and errorWithoutStackTrace
def HsList.error(~A: Data, msg: List<&2, Char>) -> Either<&2, &2, List<&2, Char>, A>:
  Inl{msg}

def HsList.undefined(~A: Data) -> Either<&2, &2, List<&2, Char>, A>:
  Inl{String.to_list("Prelude.undefined")}

def HsList.head(~A: Data, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.head: empty list")}
    case x <> t:
      Inr{x}

def HsList.tail(~A: Data, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, List<&2, A>>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.tail: empty list")}
    case x <> t:
      Inr{t}

def HsList.last.go(~A: Data, xs: List<&2, A>, x: A) -> A:
  match xs:
    case Nil{}:
      x
    case y <> t:
      HsList.last.go(~A, t, y)

def HsList.last(~A: Data, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.last: empty list")}
    case x <> t:
      Inr{HsList.last.go(~A, t, x)}

def HsList.init.go(~A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case y <> t:
      x <> HsList.init.go(~A, t, y)

def HsList.init(~A: Data, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, List<&2, A>>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.init: empty list")}
    case x <> t:
      Inr{HsList.init.go(~A, t, x)}

# xs !! n
def HsList.index.go(~A: Data, xs: List<&2, A>, n: Nat) -> Either<&2, &2, List<&2, Char>, A>:
  match xs n:
    case Nil{} _:
      Inl{String.to_list("Prelude.!!: index too large")}
    case x <> t 0n:
      Inr{x}
    case x <> t 1n+k:
      HsList.index.go(~A, t, k)

def HsList.index(~A: Data, xs: List<&2, A>, n: HsInt) -> Either<&2, &2, List<&2, Char>, A>:
  match n:
    case HsInt.Pos{k}:
      HsList.index.go(~A, xs, k)
    case HsInt.Neg{k}:
      Inl{String.to_list("Prelude.!!: negative index")}

def HsList.fromJust(~A: Data, m: Maybe<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match m:
    case None{}:
      Inl{String.to_list("Maybe.fromJust: Nothing")}
    case Some{x}:
      Inr{x}

# Data.Map's m ! k
def HsMap.at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, +k: K) -> Either<&2, &2, List<&2, Char>, V>:
  match m:
    case HsMap.Tip{}:
      Inl{String.to_list("Map.!: given key is not an element in the map")}
    case HsMap.Bin{+k2, +v2, +t}:
      HsCmp.on(Either<&2, &2, List<&2, Char>, V>, cmp(k, k2), _ => Inl{String.to_list("Map.!: given key is not an element in the map")}, _ => Inr{v2}, _ => HsMap.at(~K, ~V, ~cmp, t, k))

# maximum and minimum (Foldable's, at a list): Ord's max and min, so of two
# equal elements maximum keeps the later one and minimum the earlier one.
# Foldable's maximumBy and minimumBy keep the same ones, with their own
# message.
def HsList.maximum.go(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, +x: A) -> A:
  match xs:
    case Nil{}:
      x
    case +y <> t:
      HsList.maximum.go(~A, ~cmp, t, HsCmp.on(A, cmp(x)(y), _ => y, _ => y, _ => x))

def HsList.minimum.go(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, +x: A) -> A:
  match xs:
    case Nil{}:
      x
    case +y <> t:
      HsList.minimum.go(~A, ~cmp, t, HsCmp.on(A, cmp(x)(y), _ => x, _ => x, _ => y))

def HsList.maximum(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.maximum: empty list")}
    case x <> t:
      Inr{HsList.maximum.go(~A, ~cmp, t, x)}

def HsList.minimum(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.minimum: empty list")}
    case x <> t:
      Inr{HsList.minimum.go(~A, ~cmp, t, x)}

def HsList.maximumBy(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("maximumBy: empty structure")}
    case x <> t:
      Inr{HsList.maximum.go(~A, ~cmp, t, x)}

def HsList.minimumBy(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("minimumBy: empty structure")}
    case x <> t:
      Inr{HsList.minimum.go(~A, ~cmp, t, x)}

# foldr1 and foldl1 (Foldable's, at a list)
def HsList.foldr1.go(~A: Data, ~f: A -> A -> A, xs: List<&2, A>, x: A) -> A:
  match xs:
    case Nil{}:
      x
    case y <> t:
      f(x, HsList.foldr1.go(~A, ~f, t, y))

def HsList.foldl1.go(~A: Data, ~f: A -> A -> A, xs: List<&2, A>, acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case y <> t:
      HsList.foldl1.go(~A, ~f, t, f(acc, y))

def HsList.foldr1(~A: Data, ~f: A -> A -> A, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.foldr1: empty list")}
    case x <> t:
      Inr{HsList.foldr1.go(~A, ~f, t, x)}

def HsList.foldl1(~A: Data, ~f: A -> A -> A, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, A>:
  match xs:
    case Nil{}:
      Inl{String.to_list("Prelude.foldl1: empty list")}
    case x <> t:
      Inr{HsList.foldl1.go(~A, ~f, t, x)}
