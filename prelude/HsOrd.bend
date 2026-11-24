# Data.Ord's comparing: an Ord's compare on a key (Fold.bend's
# fd.bftab2.ord; the survey had it as base it maps, the fold had not)
def HsList.comparing(~K: Data, ~A: Data, ~cmp: K -> K -> Cmp, ~f: A -> K, x: A, y: A) -> Cmp:
  cmp(f(x))(f(y))

# Integral's even and odd at Int (Fold.bend's BfParity)
def HsInt.even(+x: HsInt) -> Bool:
  HsInt.is_eq(HsInt.rem(x, HsInt.Pos{2n}), HsInt.Pos{0n})

def HsInt.odd(+x: HsInt) -> Bool:
  Bool.not(HsInt.even(x))

# compare at Either, Ordering, a Map and a Set (Data.Map's and Data.Set's
# Ord: their lists in ascending order), and max and min by a compare
# (Haskell's defaults: max x y = if x <= y then y else x)
def HsCmp.either(~A: Data, ~B: Data, ~ca: A -> A -> Cmp, ~cb: B -> B -> Cmp, a: Either<&2, &2, A, B>, b: Either<&2, &2, A, B>) -> Cmp:
  match a b:
    case Inl{x} Inl{y}:
      ca(x)(y)
    case Inl{x} Inr{y}:
      LT{}
    case Inr{x} Inl{y}:
      GT{}
    case Inr{x} Inr{y}:
      cb(x)(y)

def HsCmp.cmp(a: Cmp, b: Cmp) -> Cmp:
  match a b:
    case LT{} LT{}:
      EQ{}
    case LT{} _:
      LT{}
    case _ LT{}:
      GT{}
    case EQ{} EQ{}:
      EQ{}
    case EQ{} _:
      LT{}
    case _ EQ{}:
      GT{}
    case GT{} GT{}:
      EQ{}

def HsCmp.map(~K: Data, ~V: Data, ~ck: K -> K -> Cmp, ~cv: V -> V -> Cmp, a: HsMap<K, V>, b: HsMap<K, V>) -> Cmp:
  match a b:
    case HsMap.Tip{} HsMap.Tip{}:
      EQ{}
    case HsMap.Tip{} _:
      LT{}
    case _ HsMap.Tip{}:
      GT{}
    case HsMap.Bin{k1, v1, r1} HsMap.Bin{k2, v2, r2}:
      HsCmp.on(Cmp, ck(k1)(k2), _ => LT{}, _ => HsCmp.on(Cmp, cv(v1)(v2), _ => LT{}, _ => HsCmp.map(~K, ~V, ~ck, ~cv, r1, r2), _ => GT{}), _ => GT{})

def HsCmp.set(~K: Data, ~ck: K -> K -> Cmp, a: HsSet<K>, b: HsSet<K>) -> Cmp:
  match a b:
    case HsSet.Tip{} HsSet.Tip{}:
      EQ{}
    case HsSet.Tip{} _:
      LT{}
    case _ HsSet.Tip{}:
      GT{}
    case HsSet.Bin{k1, r1} HsSet.Bin{k2, r2}:
      HsCmp.on(Cmp, ck(k1)(k2), _ => LT{}, _ => HsCmp.set(~K, ~ck, r1, r2), _ => GT{})

def HsCmp.max(~A: Data, ~cmp: A -> A -> Cmp, +a: A, +b: A) -> A:
  Bool.pick(A, Cmp.is_le(cmp(a)(b)), b, a)

def HsCmp.min(~A: Data, ~cmp: A -> A -> Cmp, +a: A, +b: A) -> A:
  Bool.pick(A, Cmp.is_le(cmp(a)(b)), a, b)
