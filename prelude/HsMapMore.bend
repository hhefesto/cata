
# Data.Map's and Data.Set's functions after the first ones (HsPrelude's
# HsMap and HsSet: the pairs, the keys, in ascending order of the key, each
# key once; compare at K the template ~cmp), Data.Map's semantics on that
# list.

# insertWithKey f k new: f k new old at a key there
def HsMap.insertWithKey(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, +k: K, +v: V, m: HsMap<K, V>) -> HsMap<K, V>:
  match m:
    case HsMap.Tip{}:
      HsMap.Bin{k, v, HsMap.Tip{}}
    case HsMap.Bin{+k2, +v2, +t}:
      HsCmp.on(HsMap<K, V>, cmp(k, k2), _ => HsMap.Bin{k, v, HsMap.Bin{k2, v2, t}}, _ => HsMap.Bin{k, f(k)(v)(v2), t}, _ => HsMap.Bin{k2, v2, HsMap.insertWithKey(~K, ~V, ~cmp, ~f, k, v, t)})

# unionWithKey f a b: f k (a's) (b's) at a key in both
def HsMap.unionWithKey(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:
  match a:
    case HsMap.Tip{}:
      b
    case HsMap.Bin{k, v, t}:
      HsMap.insertWithKey(~K, ~V, ~cmp, ~f, k, v, HsMap.unionWithKey(~K, ~V, ~cmp, ~f, t, b))

def HsMap.unionsWith.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, ms: List<&2, HsMap<K, V>>, acc: HsMap<K, V>) -> HsMap<K, V>:
  match ms:
    case Nil{}:
      acc
    case m <> t:
      HsMap.unionsWith.go(~K, ~V, ~cmp, ~f, t, HsMap.unionWith(~K, ~V, ~cmp, ~f, acc, m))

# unionsWith f ms: the maps' unionWith f, the first's values first
def HsMap.unionsWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, ms: List<&2, HsMap<K, V>>) -> HsMap<K, V>:
  match ms:
    case Nil{}:
      HsMap.Tip{}
    case m <> t:
      HsMap.unionsWith.go(~K, ~V, ~cmp, ~f, t, m)

def HsMap.intersectionWith.at(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~f: V -> W -> X, k: K, v: V, w: Maybe<&2, W>, r: HsMap<K, X>) -> HsMap<K, X>:
  match w:
    case None{}:
      r
    case Some{x}:
      HsMap.Bin{k, f(v)(x), r}

# intersectionWith f a b: the keys in both, f at a's value and b's
def HsMap.intersectionWith(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~cmp: K -> K -> Cmp, ~f: V -> W -> X, a: HsMap<K, V>, +b: HsMap<K, W>) -> HsMap<K, X>:
  match a:
    case HsMap.Tip{}:
      HsMap.Tip{}
    case HsMap.Bin{+k, v, t}:
      HsMap.intersectionWith.at(~K, ~V, ~W, ~X, ~f, k, v, HsMap.lookup(~K, ~W, ~cmp, k, b), HsMap.intersectionWith(~K, ~V, ~W, ~X, ~cmp, ~f, t, b))

# restrictKeys m s: m's pairs whose key s holds
def HsMap.restrictKeys(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, +s: HsSet<K>) -> HsMap<K, V>:
  match m:
    case HsMap.Tip{}:
      HsMap.Tip{}
    case HsMap.Bin{+k, +v, +t}:
      HsBool.if(HsMap<K, V>, HsSet.member(~K, ~cmp, k, s), _ => HsMap.Bin{k, v, HsMap.restrictKeys(~K, ~V, ~cmp, t, s)}, _ => HsMap.restrictKeys(~K, ~V, ~cmp, t, s))

# withoutKeys m s: m's pairs whose key s does not hold
def HsMap.withoutKeys(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, +s: HsSet<K>) -> HsMap<K, V>:
  match m:
    case HsMap.Tip{}:
      HsMap.Tip{}
    case HsMap.Bin{+k, +v, +t}:
      HsBool.if(HsMap<K, V>, HsSet.member(~K, ~cmp, k, s), _ => HsMap.withoutKeys(~K, ~V, ~cmp, t, s), _ => HsMap.Bin{k, v, HsMap.withoutKeys(~K, ~V, ~cmp, t, s)})

# fromSet f s: each key of s with f at it (the keys already in order)
def HsMap.fromSet(~K: Data, ~V: Data, ~f: K -> V, s: HsSet<K>) -> HsMap<K, V>:
  match s:
    case HsSet.Tip{}:
      HsMap.Tip{}
    case HsSet.Bin{+k, t}:
      HsMap.Bin{k, f(k), HsMap.fromSet(~K, ~V, ~f, t)}

def HsMap.split.below(~K: Data, ~V: Data, k: K, v: V, p: Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>) -> Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>:
  match p:
    case (a, b):
      (HsMap.Bin{k, v, a}, b)

# split k m: the pairs whose key is below k, and those above it
def HsMap.split(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, m: HsMap<K, V>) -> Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>:
  match m:
    case HsMap.Tip{}:
      (HsMap.Tip{}, HsMap.Tip{})
    case HsMap.Bin{+k2, +v2, +t}:
      HsCmp.on(Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>, cmp(k2, k), _ => HsMap.split.below(~K, ~V, k2, v2, HsMap.split(~K, ~V, ~cmp, k, t)), _ => (HsMap.Tip{}, t), _ => (HsMap.Tip{}, HsMap.Bin{k2, v2, t}))

# intersection a b: a's keys b holds
def HsSet.intersection(~K: Data, ~cmp: K -> K -> Cmp, a: HsSet<K>, +b: HsSet<K>) -> HsSet<K>:
  match a:
    case HsSet.Tip{}:
      HsSet.Tip{}
    case HsSet.Bin{+k, +t}:
      HsBool.if(HsSet<K>, HsSet.member(~K, ~cmp, k, b), _ => HsSet.Bin{k, HsSet.intersection(~K, ~cmp, t, b)}, _ => HsSet.intersection(~K, ~cmp, t, b))

# Data.Map's and Data.Set's size: an Int, which is HsInt (Spec's rewrite)
def HsMap.isize(~K: Data, ~V: Data, m: HsMap<K, V>) -> HsInt:
  HsInt.Pos{HsMap.size(~K, ~V, m)}

def HsSet.isize(~K: Data, s: HsSet<K>) -> HsInt:
  HsInt.Pos{HsSet.size(~K, s)}
