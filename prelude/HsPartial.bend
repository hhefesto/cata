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
def HsList.foldr1.go(~A: Data, ~f: A -> A -> A, xs: List<&2, A>, +x: A) -> A:
  match xs:
    case Nil{}:
      x
    case +y <> t:
      +r = HsList.foldr1.go(~A, ~f, t, y)
      f(x, r)

def HsList.foldl1.go(~A: Data, ~f: A -> A -> A, xs: List<&2, A>, +acc: A) -> A:
  match xs:
    case Nil{}:
      acc
    case +y <> t:
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

# div, mod, quot and rem by a divisor that is not a known non-zero
# literal (Fold.bend's fd.num): GHC throws ArithException DivideByZero,
# shown "divide by zero", at 0, so these answer it there (Base's Nat.div
# and Nat.mod answer 0 and a: F was more defined than Haskell, and no left
# adjoint, adj/PROOF.bend's P.tot.not).  At Nat (Natural, and Int and
# Integer where nothing subtracts) quot is div and rem is mod.
def HsNum.div(a: Nat, b: Nat) -> Either<&2, &2, List<&2, Char>, Nat>:
  match b:
    case 0n:
      Inl{String.to_list("divide by zero")}
    case 1n+q:
      Inr{Nat.div(a, 1n+q)}

def HsNum.mod(a: Nat, b: Nat) -> Either<&2, &2, List<&2, Char>, Nat>:
  match b:
    case 0n:
      Inl{String.to_list("divide by zero")}
    case 1n+q:
      Inr{Nat.mod(a, 1n+q)}

# Natural's (-), below 0 GHC's ArithException Underflow (Spec writes the
# method at Natural HsPrelude.N.natSub, in a module alone and in a package)
def HsNum.sub(a: Nat, b: Nat) -> Either<&2, &2, List<&2, Char>, Nat>:
  match a b:
    case 0n 0n:
      Inr{0n}
    case 0n 1n+q:
      Inl{String.to_list("arithmetic underflow")}
    case 1n+p 0n:
      Inr{1n+p}
    case 1n+p 1n+q:
      HsNum.sub(p, q)

# at HsInt (Int and Integer): 0 is Pos{0n} only
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

# x / y at Rational: GHC throws ArithException RatioZeroDenominator, shown
# "Ratio has zero denominator", at 0 (HsRational.div answers 0 there)
def HsNum.rdiv(a: HsRational, b: HsRational) -> Either<&2, &2, List<&2, Char>, HsRational>:
  match b:
    case HsRational{HsInt.Pos{0n}, q}:
      Inl{String.to_list("Ratio has zero denominator")}
    case c:
      Inr{HsRational.div(a, c)}

# The list functions given a partial function, one that answers the Either
# (Fold.bend's fd.pt.ho): the first failure, left to right (foldr's from
# the right), any and all stopping as Haskell's do.
def HsPt.bind(-A: Data, -B: Data, m: Either<&2, &2, List<&2, Char>, A>, k: A -> Either<&2, &2, List<&2, Char>, B>) -> Either<&2, &2, List<&2, Char>, B>:
  match m:
    case Inl{e}:
      Inl{e}
    case Inr{a}:
      k(a)

def HsPt.map(~A: Data, ~B: Data, ~f: A -> Either<&2, &2, List<&2, Char>, B>, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, List<&2, B>>:
  match xs:
    case Nil{}:
      Inr{[]}
    case +x <> t:
      HsPt.bind(B, List<&2, B>, f(x), b => HsPt.bind(List<&2, B>, List<&2, B>, HsPt.map(~A, ~B, ~f, t), bs => Inr{b <> bs}))

def HsPt.foldr(~A: Data, ~B: Data, ~f: A -> B -> Either<&2, &2, List<&2, Char>, B>, xs: List<&2, A>, z: B) -> Either<&2, &2, List<&2, Char>, B>:
  match xs:
    case Nil{}:
      Inr{z}
    case +x <> t:
      HsPt.bind(B, B, HsPt.foldr(~A, ~B, ~f, t, z), +r => f(x)(r))

def HsPt.foldl(~A: Data, ~B: Data, ~f: B -> A -> Either<&2, &2, List<&2, Char>, B>, xs: List<&2, A>, +acc: B) -> Either<&2, &2, List<&2, Char>, B>:
  match xs:
    case Nil{}:
      Inr{acc}
    case +x <> t:
      HsPt.bind(B, B, f(acc)(x), r => HsPt.foldl(~A, ~B, ~f, t, r))

def HsPt.keep(-A: Data, x: A, k: Bool, r: List<&2, A>) -> List<&2, A>:
  match k:
    case True{}:
      x <> r
    case False{}:
      r

def HsPt.filter(~A: Data, ~p: A -> Either<&2, &2, List<&2, Char>, Bool>, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, List<&2, A>>:
  match xs:
    case Nil{}:
      Inr{[]}
    case +x <> t:
      HsPt.bind(Bool, List<&2, A>, p(x), k => HsPt.bind(List<&2, A>, List<&2, A>, HsPt.filter(~A, ~p, t), r => Inr{HsPt.keep(A, x, k, r)}))

def HsPt.stop(v: Bool, at: Bool, rest: Unit -> Either<&2, &2, List<&2, Char>, Bool>) -> Either<&2, &2, List<&2, Char>, Bool>:
  match v at:
    case True{} True{}:
      Inr{True{}}
    case False{} False{}:
      Inr{False{}}
    case _ _:
      rest(Unit{})

def HsPt.any(~a: Quant, ~A: Data, ~p: A -> Either<&2, &2, List<&2, Char>, Bool>, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, Bool>:
  match xs:
    case Nil{}:
      Inr{False{}}
    case +x <> t:
      HsPt.bind(Bool, Bool, p(x), v => HsPt.stop(v, True{}, _ => HsPt.any(~a, ~A, ~p, t)))

def HsPt.all(~a: Quant, ~A: Data, ~p: A -> Either<&2, &2, List<&2, Char>, Bool>, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, Bool>:
  match xs:
    case Nil{}:
      Inr{True{}}
    case +x <> t:
      HsPt.bind(Bool, Bool, p(x), v => HsPt.stop(v, False{}, _ => HsPt.all(~a, ~A, ~p, t)))

def HsPt.zipWith(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> Either<&2, &2, List<&2, Char>, C>, xs: List<&2, A>, ys: List<&2, B>) -> Either<&2, &2, List<&2, Char>, List<&2, C>>:
  match xs ys:
    case Nil{} _:
      Inr{[]}
    case _ Nil{}:
      Inr{[]}
    case +x <> t +y <> u:
      HsPt.bind(C, List<&2, C>, f(x)(y), c => HsPt.bind(List<&2, C>, List<&2, C>, HsPt.zipWith(~A, ~B, ~C, ~f, t, u), cs => Inr{c <> cs}))

def HsPt.maybe(-B: Data, m: Maybe<&2, B>, r: List<&2, B>) -> List<&2, B>:
  match m:
    case Some{b}:
      b <> r
    case None{}:
      r

def HsPt.mapMaybe(~A: Data, ~B: Data, ~f: A -> Either<&2, &2, List<&2, Char>, Maybe<&2, B>>, xs: List<&2, A>) -> Either<&2, &2, List<&2, Char>, List<&2, B>>:
  match xs:
    case Nil{}:
      Inr{[]}
    case +x <> t:
      HsPt.bind(Maybe<&2, B>, List<&2, B>, f(x), m => HsPt.bind(List<&2, B>, List<&2, B>, HsPt.mapMaybe(~A, ~B, ~f, t), r => Inr{HsPt.maybe(B, m, r)}))
