#@drop HsMap.split.below
#@after HsCmp.on
# Data.Map's Map and Data.Set's Set as containers' weight-balanced trees
# (delta 3, ratio 2): what a translated program runs on. HsPrelude's own HsMap
# and HsSet are ascending lists, so that two equal maps are one term and a law
# can say so; a list insert is linear. Every def here has its HsPrelude
# header and, through toList, its answer (tests/maps): tools/run-prelude.zsh
# puts these in HsPrelude's place in a package that is to run. Modules name
# only the empty constructors (HsMap.Tip, HsSet.Tip), so nothing else changes.
type HsMap<-K: Data, -V: Data> is Data:
  HsMap.Tip{}
  HsMap.Bin{size: U32, key: K, val: V, l: HsMap<K, V>, r: HsMap<K, V>}

type HsSet<-K: Data> is Data:
  HsSet.Tip{}
  HsSet.Bin{size: U32, key: K, l: HsSet<K>, r: HsSet<K>}

# a list of pairs, the rest of a traversal in hand
type HsMap.Cut<-K: Data, -V: Data> is Data:
  HsMap.Cut{m: HsMap<K, V>, rest: List<&2, Sigma<&2, &2, K, _ => V>>}

type HsSet.Cut<-K: Data> is Data:
  HsSet.Cut{s: HsSet<K>, rest: List<&2, K>}

# a map's first (or last) pair and the map without it
type HsMap.View<-K: Data, -V: Data> is Data:
  HsMap.View{key: K, val: V, m: HsMap<K, V>}

type HsSet.View<-K: Data> is Data:
  HsSet.View{key: K, s: HsSet<K>}

# which way a node leans
type HsDir is Data:
  HsDir.N{}
  HsDir.L{}
  HsDir.R{}

def HsDir.big(a: Bool, b: Bool) -> HsDir:
  match a b:
    case True{} _:
      HsDir.L{}
    case False{} True{}:
      HsDir.R{}
    case False{} False{}:
      HsDir.N{}

def HsDir.small(s: Bool, d: HsDir) -> HsDir:
  match s:
    case True{}:
      HsDir.N{}
    case False{}:
      d

# L: rotate left (the right is more than 3 times the left); R: rotate right
def HsDir.of(+sl: U32, +sr: U32) -> HsDir:
  HsDir.small(U32.is_lt(U32.add(sl, sr), 2), HsDir.big(U32.is_lt(U32.mul(sl, 3), sr), U32.is_lt(U32.mul(sr, 3), sl)))

# ---- HsMap

def HsMap.sz(-K: Data, -V: Data, m: HsMap<K, V>) -> U32:
  match m:
    case HsMap.Tip{}:
      0
    case HsMap.Bin{s, k, v, l, r}:
      s

def HsMap.bin(-K: Data, -V: Data, k: K, v: V, +l: HsMap<K, V>, +r: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.Bin{U32.inc(U32.add(HsMap.sz(K, V, l), HsMap.sz(K, V, r))), k, v, l, r}

def HsMap.rotl2(-K: Data, -V: Data, k: K, v: V, l: HsMap<K, V>, rk: K, rv: V, rl: HsMap<K, V>, rr: HsMap<K, V>) -> HsMap<K, V>:
  match rl:
    case HsMap.Tip{}:
      HsMap.bin(K, V, rk, rv, HsMap.bin(K, V, k, v, l, HsMap.Tip{}), rr)
    case HsMap.Bin{s, k2, v2, a, b}:
      HsMap.bin(K, V, k2, v2, HsMap.bin(K, V, k, v, l, a), HsMap.bin(K, V, rk, rv, b, rr))

def HsMap.rotl1(-K: Data, -V: Data, single: Bool, k: K, v: V, l: HsMap<K, V>, rk: K, rv: V, rl: HsMap<K, V>, rr: HsMap<K, V>) -> HsMap<K, V>:
  match single:
    case True{}:
      HsMap.bin(K, V, rk, rv, HsMap.bin(K, V, k, v, l, rl), rr)
    case False{}:
      HsMap.rotl2(K, V, k, v, l, rk, rv, rl, rr)

def HsMap.rotl(-K: Data, -V: Data, k: K, v: V, l: HsMap<K, V>, r: HsMap<K, V>) -> HsMap<K, V>:
  match r:
    case HsMap.Tip{}:
      HsMap.bin(K, V, k, v, l, HsMap.Tip{})
    case HsMap.Bin{s, rk, rv, +rl, +rr}:
      HsMap.rotl1(K, V, U32.is_lt(HsMap.sz(K, V, rl), U32.mul(2, HsMap.sz(K, V, rr))), k, v, l, rk, rv, rl, rr)

def HsMap.rotr2(-K: Data, -V: Data, k: K, v: V, r: HsMap<K, V>, lk: K, lv: V, ll: HsMap<K, V>, lr: HsMap<K, V>) -> HsMap<K, V>:
  match lr:
    case HsMap.Tip{}:
      HsMap.bin(K, V, lk, lv, ll, HsMap.bin(K, V, k, v, HsMap.Tip{}, r))
    case HsMap.Bin{s, k2, v2, a, b}:
      HsMap.bin(K, V, k2, v2, HsMap.bin(K, V, lk, lv, ll, a), HsMap.bin(K, V, k, v, b, r))

def HsMap.rotr1(-K: Data, -V: Data, single: Bool, k: K, v: V, r: HsMap<K, V>, lk: K, lv: V, ll: HsMap<K, V>, lr: HsMap<K, V>) -> HsMap<K, V>:
  match single:
    case True{}:
      HsMap.bin(K, V, lk, lv, ll, HsMap.bin(K, V, k, v, lr, r))
    case False{}:
      HsMap.rotr2(K, V, k, v, r, lk, lv, ll, lr)

def HsMap.rotr(-K: Data, -V: Data, k: K, v: V, l: HsMap<K, V>, r: HsMap<K, V>) -> HsMap<K, V>:
  match l:
    case HsMap.Tip{}:
      HsMap.bin(K, V, k, v, HsMap.Tip{}, r)
    case HsMap.Bin{s, lk, lv, +ll, +lr}:
      HsMap.rotr1(K, V, U32.is_lt(HsMap.sz(K, V, lr), U32.mul(2, HsMap.sz(K, V, ll))), k, v, r, lk, lv, ll, lr)

def HsMap.bal.at(-K: Data, -V: Data, d: HsDir, n: U32, k: K, v: V, l: HsMap<K, V>, r: HsMap<K, V>) -> HsMap<K, V>:
  match d:
    case HsDir.N{}:
      HsMap.Bin{n, k, v, l, r}
    case HsDir.L{}:
      HsMap.rotl(K, V, k, v, l, r)
    case HsDir.R{}:
      HsMap.rotr(K, V, k, v, l, r)

# a node whose sides differ by one insert or delete
def HsMap.bal(-K: Data, -V: Data, k: K, v: V, +l: HsMap<K, V>, +r: HsMap<K, V>) -> HsMap<K, V>:
  +sl = HsMap.sz(K, V, l)
  +sr = HsMap.sz(K, V, r)
  HsMap.bal.at(K, V, HsDir.of(sl, sr), U32.inc(U32.add(sl, sr)), k, v, l, r)

# how a key compares with a map's root (LT at an empty map)
def HsMap.first(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, k: K, m: HsMap<K, V>) -> Cmp:
  match m:
    case HsMap.Tip{}:
      LT{}
    case HsMap.Bin{s, k2, v2, l, r}:
      cmp(k, k2)

def HsMap.insert.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, +k: K, v: V) -> HsMap<K, V>:
  match m c:
    case HsMap.Tip{} _:
      HsMap.Bin{1, k, v, HsMap.Tip{}, HsMap.Tip{}}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.bal(K, V, k2, v2, HsMap.insert.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), k, v), r)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      HsMap.Bin{s, k, v, l, r}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.bal(K, V, k2, v2, l, HsMap.insert.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), k, v))

def HsMap.insert(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +v: V, +m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.insert.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), k, v)

# insertWith f k new: f new old at a key there (f runs at most once: a closure
# may be given)
def HsMap.insertWith.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, f: V -> V -> V, +k: K, v: V) -> HsMap<K, V>:
  match m c:
    case HsMap.Tip{} _:
      HsMap.Bin{1, k, v, HsMap.Tip{}, HsMap.Tip{}}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.bal(K, V, k2, v2, HsMap.insertWith.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), f, k, v), r)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      HsMap.Bin{s, k, f(v)(v2), l, r}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.bal(K, V, k2, v2, l, HsMap.insertWith.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), f, k, v))

def HsMap.insertWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, f: V -> V -> V, +k: K, v: V, +m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.insertWith.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), f, k, v)

# insertWithKey f k new: f k new old at a key there
def HsMap.insertWithKey.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, m: HsMap<K, V>, c: Cmp, +k: K, v: V) -> HsMap<K, V>:
  match m c:
    case HsMap.Tip{} _:
      HsMap.Bin{1, k, v, HsMap.Tip{}, HsMap.Tip{}}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.bal(K, V, k2, v2, HsMap.insertWithKey.go(~K, ~V, ~cmp, ~f, l, HsMap.first(~K, ~V, ~cmp, k, l), k, v), r)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      HsMap.Bin{s, k, f(k)(v)(v2), l, r}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.bal(K, V, k2, v2, l, HsMap.insertWithKey.go(~K, ~V, ~cmp, ~f, r, HsMap.first(~K, ~V, ~cmp, k, r), k, v))

def HsMap.insertWithKey(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, +k: K, +v: V, +m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.insertWithKey.go(~K, ~V, ~cmp, ~f, m, HsMap.first(~K, ~V, ~cmp, k, m), k, v)

def HsMap.lookup.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, +k: K) -> Maybe<&2, V>:
  match m c:
    case HsMap.Tip{} _:
      None{}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.lookup.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), k)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      Some{v2}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.lookup.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), k)

def HsMap.lookup(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsMap<K, V>) -> Maybe<&2, V>:
  HsMap.lookup.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), k)

def HsMap.member.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, +k: K) -> Bool:
  match m c:
    case HsMap.Tip{} _:
      False{}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.member.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), k)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      True{}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.member.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), k)

def HsMap.member(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsMap<K, V>) -> Bool:
  HsMap.member.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), k)

def HsMap.findWithDefault(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +d: V, +k: K, +m: HsMap<K, V>) -> V:
  Maybe.default(&2, V, HsMap.lookup(~K, ~V, ~cmp, k, m), d)

def HsMap.at.got(~V: Data, m: Maybe<&2, V>) -> Either<&2, &2, List<&2, Char>, V>:
  match m:
    case None{}:
      Inl{String.to_list("Map.!: given key is not an element in the map")}
    case Some{v}:
      Inr{v}

# Data.Map's m ! k
def HsMap.at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m: HsMap<K, V>, +k: K) -> Either<&2, &2, List<&2, Char>, V>:
  HsMap.at.got(~V, HsMap.lookup(~K, ~V, ~cmp, k, m))

def HsMap.minv.bal(-K: Data, -V: Data, w: HsMap.View<K, V>, k: K, v: V, r: HsMap<K, V>) -> HsMap.View<K, V>:
  match w:
    case HsMap.View{km, vm, l}:
      HsMap.View{km, vm, HsMap.bal(K, V, k, v, l, r)}

def HsMap.minv(-K: Data, -V: Data, l: HsMap<K, V>, k: K, v: V, r: HsMap<K, V>) -> HsMap.View<K, V>:
  match l:
    case HsMap.Tip{}:
      HsMap.View{k, v, r}
    case HsMap.Bin{s, kl, vl, ll, lr}:
      HsMap.minv.bal(K, V, HsMap.minv(K, V, ll, kl, vl, lr), k, v, r)

def HsMap.maxv.bal(-K: Data, -V: Data, w: HsMap.View<K, V>, k: K, v: V, l: HsMap<K, V>) -> HsMap.View<K, V>:
  match w:
    case HsMap.View{km, vm, r}:
      HsMap.View{km, vm, HsMap.bal(K, V, k, v, l, r)}

def HsMap.maxv(-K: Data, -V: Data, r: HsMap<K, V>, k: K, v: V, l: HsMap<K, V>) -> HsMap.View<K, V>:
  match r:
    case HsMap.Tip{}:
      HsMap.View{k, v, l}
    case HsMap.Bin{s, kr, vr, rl, rr}:
      HsMap.maxv.bal(K, V, HsMap.maxv(K, V, rr, kr, vr, rl), k, v, l)

def HsMap.glue.l(-K: Data, -V: Data, w: HsMap.View<K, V>, r: HsMap<K, V>) -> HsMap<K, V>:
  match w:
    case HsMap.View{k, v, l}:
      HsMap.bal(K, V, k, v, l, r)

def HsMap.glue.r(-K: Data, -V: Data, w: HsMap.View<K, V>, l: HsMap<K, V>) -> HsMap<K, V>:
  match w:
    case HsMap.View{k, v, r}:
      HsMap.bal(K, V, k, v, l, r)

def HsMap.glue.at(-K: Data, -V: Data, b: Bool, l: HsMap<K, V>, r: HsMap<K, V>) -> HsMap<K, V>:
  match b l r:
    case _ HsMap.Tip{} r2:
      r2
    case _ l2 HsMap.Tip{}:
      l2
    case True{} HsMap.Bin{s, k, v, ll, lr} HsMap.Bin{s2, k2, v2, rl, rr}:
      HsMap.glue.l(K, V, HsMap.maxv(K, V, lr, k, v, ll), HsMap.Bin{s2, k2, v2, rl, rr})
    case False{} HsMap.Bin{s, k, v, ll, lr} HsMap.Bin{s2, k2, v2, rl, rr}:
      HsMap.glue.r(K, V, HsMap.minv(K, V, rl, k2, v2, rr), HsMap.Bin{s, k, v, ll, lr})

# two maps that balance, the first's keys all below the second's
def HsMap.glue(-K: Data, -V: Data, +l: HsMap<K, V>, +r: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.glue.at(K, V, U32.is_lt(HsMap.sz(K, V, r), HsMap.sz(K, V, l)), l, r)

def HsMap.delete.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, +k: K) -> HsMap<K, V>:
  match m c:
    case HsMap.Tip{} _:
      HsMap.Tip{}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.bal(K, V, k2, v2, HsMap.delete.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), k), r)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      HsMap.glue(K, V, l, r)
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.bal(K, V, k2, v2, l, HsMap.delete.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), k))

def HsMap.delete(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.delete.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), k)

def HsMap.adjust.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, f: V -> V, +k: K) -> HsMap<K, V>:
  match m c:
    case HsMap.Tip{} _:
      HsMap.Tip{}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.Bin{s, k2, v2, HsMap.adjust.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), f, k), r}
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      HsMap.Bin{s, k2, f(v2), l, r}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.Bin{s, k2, v2, l, HsMap.adjust.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), f, k)}

def HsMap.adjust(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, f: V -> V, +k: K, +m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.adjust.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), f, k)

def HsMap.toList.go(-K: Data, -V: Data, m: HsMap<K, V>, acc: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match m:
    case HsMap.Tip{}:
      acc
    case HsMap.Bin{s, k, v, l, r}:
      HsMap.toList.go(K, V, l, (k, v) <> HsMap.toList.go(K, V, r, acc))

def HsMap.toList(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  HsMap.toList.go(K, V, m, Nil{})

def HsMap.build.join(-K: Data, -V: Data, n: U32, k: K, v: V, l: HsMap<K, V>, c: HsMap.Cut<K, V>) -> HsMap.Cut<K, V>:
  match c:
    case HsMap.Cut{r, t}:
      HsMap.Cut{HsMap.Bin{n, k, v, l, r}, t}

def HsMap.build.node(-K: Data, -V: Data, n: U32, c: HsMap.Cut<K, V>, next: List<&2, Sigma<&2, &2, K, _ => V>> -> HsMap.Cut<K, V>) -> HsMap.Cut<K, V>:
  match c:
    case HsMap.Cut{l, Nil{}}:
      HsMap.Cut{l, Nil{}}
    case HsMap.Cut{l, (k, v) <> t}:
      HsMap.build.join(K, V, n, k, v, l, next(t))

# the first n pairs of xs (in order, distinct) as a tree, and the rest; d is
# a depth no tree of n pairs passes, z whether n is 0
def HsMap.build(-K: Data, -V: Data, d: Nat, z: Bool, +n: U32, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap.Cut<K, V>:
  match d z:
    case 0n _:
      HsMap.Cut{HsMap.Tip{}, xs}
    case _ True{}:
      HsMap.Cut{HsMap.Tip{}, xs}
    case 1n++e False{}:
      +h = U32.shr(U32.sub(n, 1))
      +j = U32.sub(U32.sub(n, 1), h)
      HsMap.build.node(K, V, n, HsMap.build(K, V, e, U32.is_eq(h, 0), h, xs), t => HsMap.build(K, V, e, U32.is_eq(j, 0), j, t))

def HsMap.build.m(-K: Data, -V: Data, c: HsMap.Cut<K, V>) -> HsMap<K, V>:
  match c:
    case HsMap.Cut{m, t}:
      m

def HsMap.len(-A: Data, xs: List<&2, A>, n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case x <> t:
      HsMap.len(A, t, U32.inc(n))

# fromDistinctAscList
def HsMap.fromAsc(~K: Data, ~V: Data, +xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap<K, V>:
  +n = HsMap.len(Sigma<&2, &2, K, _ => V>, xs, 0)
  HsMap.build.m(K, V, HsMap.build(K, V, 40n, U32.is_eq(n, 0), n, xs))

def HsMap.fromList.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Sigma<&2, &2, K, _ => V>>, acc: HsMap<K, V>) -> HsMap<K, V>:
  match xs:
    case Nil{}:
      acc
    case (k, v) <> t:
      HsMap.fromList.go(~K, ~V, ~cmp, t, HsMap.insert(~K, ~V, ~cmp, k, v, acc))

def HsMap.fromList(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap<K, V>:
  HsMap.fromList.go(~K, ~V, ~cmp, xs, HsMap.Tip{})

def HsMap.fromListWith.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, xs: List<&2, Sigma<&2, &2, K, _ => V>>, acc: HsMap<K, V>) -> HsMap<K, V>:
  match xs:
    case Nil{}:
      acc
    case (k, v) <> t:
      HsMap.fromListWith.go(~K, ~V, ~cmp, ~f, t, HsMap.insertWith(~K, ~V, ~cmp, f, k, v, acc))

def HsMap.fromListWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap<K, V>:
  HsMap.fromListWith.go(~K, ~V, ~cmp, ~f, xs, HsMap.Tip{})

def HsMap.elems.go(-K: Data, -V: Data, m: HsMap<K, V>, acc: List<&2, V>) -> List<&2, V>:
  match m:
    case HsMap.Tip{}:
      acc
    case HsMap.Bin{s, k, v, l, r}:
      HsMap.elems.go(K, V, l, v <> HsMap.elems.go(K, V, r, acc))

def HsMap.elems(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, V>:
  HsMap.elems.go(K, V, m, Nil{})

def HsMap.keys.go(-K: Data, -V: Data, m: HsMap<K, V>, acc: List<&2, K>) -> List<&2, K>:
  match m:
    case HsMap.Tip{}:
      acc
    case HsMap.Bin{s, k, v, l, r}:
      HsMap.keys.go(K, V, l, k <> HsMap.keys.go(K, V, r, acc))

def HsMap.keys(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, K>:
  HsMap.keys.go(K, V, m, Nil{})

def HsMap.keysSet(~K: Data, ~V: Data, m: HsMap<K, V>) -> HsSet<K>:
  match m:
    case HsMap.Tip{}:
      HsSet.Tip{}
    case HsMap.Bin{s, k, v, l, r}:
      HsSet.Bin{s, k, HsMap.keysSet(~K, ~V, l), HsMap.keysSet(~K, ~V, r)}

def HsMap.size(~K: Data, ~V: Data, m: HsMap<K, V>) -> Nat:
  U32.to_nat(HsMap.sz(K, V, m))

def HsMap.null(~K: Data, ~V: Data, m: HsMap<K, V>) -> Bool:
  match m:
    case HsMap.Tip{}:
      True{}
    case HsMap.Bin{s, k, v, l, r}:
      False{}

# each pair of xs put in m; keep: only where its key is not there yet
def HsMap.puts(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, xs: List<&2, Sigma<&2, &2, K, _ => V>>, m: HsMap<K, V>) -> HsMap<K, V>:
  match xs:
    case Nil{}:
      m
    case (k, v) <> t:
      HsMap.puts(~K, ~V, ~cmp, ~f, t, HsMap.insertWithKey(~K, ~V, ~cmp, ~f, k, v, m))

# f k (a's) (b's) at a key in both: the smaller's pairs put in the larger
def HsMap.unionWithKey.at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, s: Bool, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:
  match s:
    case True{}:
      HsMap.puts(~K, ~V, ~cmp, ~f, HsMap.toList(~K, ~V, a), b)
    case False{}:
      HsMap.puts(~K, ~V, ~cmp, ~(k => new => old => f(k)(old)(new)), HsMap.toList(~K, ~V, b), a)

def HsMap.unionWithKey(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: K -> V -> V -> V, +a: HsMap<K, V>, +b: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.unionWithKey.at(~K, ~V, ~cmp, ~f, U32.is_le(HsMap.sz(K, V, a), HsMap.sz(K, V, b)), a, b)

def HsMap.unionWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.unionWithKey(~K, ~V, ~cmp, ~(k => f), a, b)

# union is left-biased: a's value at a key both have
def HsMap.union(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.unionWithKey(~K, ~V, ~cmp, ~(k => x => y => x), a, b)

def HsMap.unionsWith.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, ms: List<&2, HsMap<K, V>>, acc: HsMap<K, V>) -> HsMap<K, V>:
  match ms:
    case Nil{}:
      acc
    case m <> t:
      HsMap.unionsWith.go(~K, ~V, ~cmp, ~f, t, HsMap.unionWith(~K, ~V, ~cmp, ~f, acc, m))

def HsMap.unionsWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, ms: List<&2, HsMap<K, V>>) -> HsMap<K, V>:
  match ms:
    case Nil{}:
      HsMap.Tip{}
    case m <> t:
      HsMap.unionsWith.go(~K, ~V, ~cmp, ~f, t, m)

def HsMap.unions(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ms: List<&2, HsMap<K, V>>) -> HsMap<K, V>:
  HsMap.unionsWith(~K, ~V, ~cmp, ~(a => b => a), ms)

# the pairs p keeps, in order
def HsMap.keep.at(-K: Data, -V: Data, b: Bool, k: K, v: V, r: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match b:
    case True{}:
      (k, v) <> r
    case False{}:
      r

def HsMap.keep(~K: Data, ~V: Data, ~p: K -> V -> Bool, m: HsMap<K, V>, acc: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match m:
    case HsMap.Tip{}:
      acc
    case HsMap.Bin{s, +k, +v, l, r}:
      HsMap.keep(~K, ~V, ~p, l, HsMap.keep.at(K, V, p(k)(v), k, v, HsMap.keep(~K, ~V, ~p, r, acc)))

def HsMap.filterWithKey(~K: Data, ~V: Data, ~p: K -> V -> Bool, m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.fromAsc(~K, ~V, HsMap.keep(~K, ~V, ~p, m, Nil{}))

def HsMap.filter(~K: Data, ~V: Data, ~p: V -> Bool, m: HsMap<K, V>) -> HsMap<K, V>:
  HsMap.filterWithKey(~K, ~V, ~(k => p), m)

# the pairs of a whose key f (a lookup's answer in b) keeps
def HsMap.minus.at(-K: Data, -V: Data, b: Bool, k: K, v: V, r: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match b:
    case True{}:
      r
    case False{}:
      (k, v) <> r

def HsMap.minus(~K: Data, ~V: Data, ~W: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Sigma<&2, &2, K, _ => V>>, +b: HsMap<K, W>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match xs:
    case Nil{}:
      Nil{}
    case (+k, v) <> t:
      HsMap.minus.at(K, V, HsMap.member(~K, ~W, ~cmp, k, b), k, v, HsMap.minus(~K, ~V, ~W, ~cmp, t, b))

def HsMap.dels(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ks: List<&2, K>, m: HsMap<K, V>) -> HsMap<K, V>:
  match ks:
    case Nil{}:
      m
    case k <> t:
      HsMap.dels(~K, ~V, ~cmp, t, HsMap.delete(~K, ~V, ~cmp, k, m))

def HsMap.difference.at(~K: Data, ~V: Data, ~W: Data, ~cmp: K -> K -> Cmp, s: Bool, a: HsMap<K, V>, b: HsMap<K, W>) -> HsMap<K, V>:
  match s:
    case True{}:
      HsMap.dels(~K, ~V, ~cmp, HsMap.keys(~K, ~W, b), a)
    case False{}:
      HsMap.fromAsc(~K, ~V, HsMap.minus(~K, ~V, ~W, ~cmp, HsMap.toList(~K, ~V, a), b))

# the keys of a not in b (IntMap's and Set's difference, \\)
def HsMap.difference(~K: Data, ~V: Data, ~W: Data, ~cmp: K -> K -> Cmp, +a: HsMap<K, V>, +b: HsMap<K, W>) -> HsMap<K, V>:
  HsMap.difference.at(~K, ~V, ~W, ~cmp, U32.is_le(HsMap.sz(K, W, b), HsMap.sz(K, V, a)), a, b)

def HsMap.map(~K: Data, ~V: Data, ~W: Data, ~f: V -> W, m: HsMap<K, V>) -> HsMap<K, W>:
  match m:
    case HsMap.Tip{}:
      HsMap.Tip{}
    case HsMap.Bin{s, k, v, l, r}:
      HsMap.Bin{s, k, f(v), HsMap.map(~K, ~V, ~W, ~f, l), HsMap.map(~K, ~V, ~W, ~f, r)}

def HsMap.mapWithKey(~K: Data, ~V: Data, ~W: Data, ~f: K -> V -> W, m: HsMap<K, V>) -> HsMap<K, W>:
  match m:
    case HsMap.Tip{}:
      HsMap.Tip{}
    case HsMap.Bin{s, +k, v, l, r}:
      HsMap.Bin{s, k, f(k)(v), HsMap.mapWithKey(~K, ~V, ~W, ~f, l), HsMap.mapWithKey(~K, ~V, ~W, ~f, r)}

def HsMap.foldr.go(~K: Data, ~V: Data, ~B: Data, ~f: K -> V -> B -> B, m: HsMap<K, V>, z: B) -> B:
  match m:
    case HsMap.Tip{}:
      z
    case HsMap.Bin{s, k, v, l, r}:
      HsMap.foldr.go(~K, ~V, ~B, ~f, l, f(k)(v)(HsMap.foldr.go(~K, ~V, ~B, ~f, r, z)))

def HsMap.foldrWithKey(~K: Data, ~V: Data, ~B: Data, ~f: K -> V -> B -> B, z: B, m: HsMap<K, V>) -> B:
  HsMap.foldr.go(~K, ~V, ~B, ~f, m, z)

def HsMap.foldr(~K: Data, ~V: Data, ~B: Data, ~f: V -> B -> B, z: B, m: HsMap<K, V>) -> B:
  HsMap.foldr.go(~K, ~V, ~B, ~(k => f), m, z)

def HsMap.eq.go(~K: Data, ~V: Data, ~eqk: K -> K -> Bool, ~eqv: V -> V -> Bool, a: List<&2, Sigma<&2, &2, K, _ => V>>, b: List<&2, Sigma<&2, &2, K, _ => V>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Tuple{k1, v1} <> t1 Tuple{k2, v2} <> t2:
      Bool.and(Bool.and(eqk(k1)(k2), eqv(v1)(v2)), HsMap.eq.go(~K, ~V, ~eqk, ~eqv, t1, t2))
    case _ _:
      False{}

def HsMap.eq(~K: Data, ~V: Data, ~eqk: K -> K -> Bool, ~eqv: V -> V -> Bool, a: HsMap<K, V>, b: HsMap<K, V>) -> Bool:
  HsMap.eq.go(~K, ~V, ~eqk, ~eqv, HsMap.toList(~K, ~V, a), HsMap.toList(~K, ~V, b))

def HsCmp.map.go(~K: Data, ~V: Data, ~ck: K -> K -> Cmp, ~cv: V -> V -> Cmp, a: List<&2, Sigma<&2, &2, K, _ => V>>, b: List<&2, Sigma<&2, &2, K, _ => V>>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} _:
      LT{}
    case _ Nil{}:
      GT{}
    case Tuple{k1, v1} <> r1 Tuple{k2, v2} <> r2:
      HsCmp.on(Cmp, ck(k1)(k2), _ => LT{}, _ => HsCmp.on(Cmp, cv(v1)(v2), _ => LT{}, _ => HsCmp.map.go(~K, ~V, ~ck, ~cv, r1, r2), _ => GT{}), _ => GT{})

def HsCmp.map(~K: Data, ~V: Data, ~ck: K -> K -> Cmp, ~cv: V -> V -> Cmp, a: HsMap<K, V>, b: HsMap<K, V>) -> Cmp:
  HsCmp.map.go(~K, ~V, ~ck, ~cv, HsMap.toList(~K, ~V, a), HsMap.toList(~K, ~V, b))

def HsMap.empty(~K: Data, ~V: Data) -> HsMap<K, V>:
  HsMap.Tip{}

def HsMap.singleton(~K: Data, ~V: Data, k: K, v: V) -> HsMap<K, V>:
  HsMap.Bin{1, k, v, HsMap.Tip{}, HsMap.Tip{}}

def HsMap.notMember(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, k: K, m: HsMap<K, V>) -> Bool:
  Bool.not(HsMap.member(~K, ~V, ~cmp, k, m))

def HsMap.intersectionWith.at(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~f: V -> W -> X, k: K, v: V, w: Maybe<&2, W>, r: List<&2, Sigma<&2, &2, K, _ => X>>) -> List<&2, Sigma<&2, &2, K, _ => X>>:
  match w:
    case None{}:
      r
    case Some{x}:
      (k, f(v)(x)) <> r

def HsMap.intersectionWith.go(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~cmp: K -> K -> Cmp, ~f: V -> W -> X, xs: List<&2, Sigma<&2, &2, K, _ => V>>, +b: HsMap<K, W>) -> List<&2, Sigma<&2, &2, K, _ => X>>:
  match xs:
    case Nil{}:
      Nil{}
    case (+k, v) <> t:
      HsMap.intersectionWith.at(~K, ~V, ~W, ~X, ~f, k, v, HsMap.lookup(~K, ~W, ~cmp, k, b), HsMap.intersectionWith.go(~K, ~V, ~W, ~X, ~cmp, ~f, t, b))

# the pair at k, its key the map's own
def HsMap.entry.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: HsMap<K, V>, c: Cmp, +k: K) -> Maybe<&2, Sigma<&2, &2, K, _ => V>>:
  match m c:
    case HsMap.Tip{} _:
      None{}
    case HsMap.Bin{s, k2, v2, +l, r} LT{}:
      HsMap.entry.go(~K, ~V, ~cmp, l, HsMap.first(~K, ~V, ~cmp, k, l), k)
    case HsMap.Bin{s, k2, v2, l, r} EQ{}:
      Some{(k2, v2)}
    case HsMap.Bin{s, k2, v2, l, +r} GT{}:
      HsMap.entry.go(~K, ~V, ~cmp, r, HsMap.first(~K, ~V, ~cmp, k, r), k)

def HsMap.entry(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsMap<K, V>) -> Maybe<&2, Sigma<&2, &2, K, _ => V>>:
  HsMap.entry.go(~K, ~V, ~cmp, m, HsMap.first(~K, ~V, ~cmp, k, m), k)

# intersectionWith with b the smaller: b's pairs looked up in a
def HsMap.intersectionWith.by.at(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~f: V -> W -> X, w: W, e: Maybe<&2, Sigma<&2, &2, K, _ => V>>, r: List<&2, Sigma<&2, &2, K, _ => X>>) -> List<&2, Sigma<&2, &2, K, _ => X>>:
  match e:
    case None{}:
      r
    case Some{(k, v)}:
      (k, f(v)(w)) <> r

def HsMap.intersectionWith.by(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~cmp: K -> K -> Cmp, ~f: V -> W -> X, xs: List<&2, Sigma<&2, &2, K, _ => W>>, +a: HsMap<K, V>) -> List<&2, Sigma<&2, &2, K, _ => X>>:
  match xs:
    case Nil{}:
      Nil{}
    case (+k, w) <> t:
      HsMap.intersectionWith.by.at(~K, ~V, ~W, ~X, ~f, w, HsMap.entry(~K, ~V, ~cmp, k, a), HsMap.intersectionWith.by(~K, ~V, ~W, ~X, ~cmp, ~f, t, a))

def HsMap.intersectionWith.on(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~cmp: K -> K -> Cmp, ~f: V -> W -> X, s: Bool, a: HsMap<K, V>, b: HsMap<K, W>) -> HsMap<K, X>:
  match s:
    case True{}:
      HsMap.fromAsc(~K, ~X, HsMap.intersectionWith.go(~K, ~V, ~W, ~X, ~cmp, ~f, HsMap.toList(~K, ~V, a), b))
    case False{}:
      HsMap.fromAsc(~K, ~X, HsMap.intersectionWith.by(~K, ~V, ~W, ~X, ~cmp, ~f, HsMap.toList(~K, ~W, b), a))

# intersectionWith f a b: the keys in both, f at a's value and b's (the smaller
# looked up in the larger)
def HsMap.intersectionWith(~K: Data, ~V: Data, ~W: Data, ~X: Data, ~cmp: K -> K -> Cmp, ~f: V -> W -> X, +a: HsMap<K, V>, +b: HsMap<K, W>) -> HsMap<K, X>:
  HsMap.intersectionWith.on(~K, ~V, ~W, ~X, ~cmp, ~f, U32.is_le(HsMap.sz(K, V, a), HsMap.sz(K, W, b)), a, b)

# split k m: the pairs whose key is below k, and those above it
def HsMap.split.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, xs: List<&2, Sigma<&2, &2, K, _ => V>>, below: List<&2, Sigma<&2, &2, K, _ => V>>) -> Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>:
  match xs:
    case Nil{}:
      (HsMap.fromAsc(~K, ~V, List.reverse(&2, Sigma<&2, &2, K, _ => V>, below)), HsMap.Tip{})
    case (+k2, +v2) <> +t:
      +b = below
      HsCmp.on(Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>, cmp(k2, k), _ => HsMap.split.go(~K, ~V, ~cmp, k, t, (k2, v2) <> b), _ => (HsMap.fromAsc(~K, ~V, List.reverse(&2, Sigma<&2, &2, K, _ => V>, b)), HsMap.fromAsc(~K, ~V, t)), _ => (HsMap.fromAsc(~K, ~V, List.reverse(&2, Sigma<&2, &2, K, _ => V>, b)), HsMap.fromAsc(~K, ~V, (k2, v2) <> t)))

def HsMap.split(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, m: HsMap<K, V>) -> Sigma<&2, &2, HsMap<K, V>, _ => HsMap<K, V>>:
  HsMap.split.go(~K, ~V, ~cmp, k, HsMap.toList(~K, ~V, m), Nil{})

# ---- HsSet: the maps without their values

def HsSet.sz(-K: Data, m: HsSet<K>) -> U32:
  match m:
    case HsSet.Tip{}:
      0
    case HsSet.Bin{s, k, l, r}:
      s

def HsSet.bin(-K: Data, k: K, +l: HsSet<K>, +r: HsSet<K>) -> HsSet<K>:
  HsSet.Bin{U32.inc(U32.add(HsSet.sz(K, l), HsSet.sz(K, r))), k, l, r}

def HsSet.rotl2(-K: Data, k: K, l: HsSet<K>, rk: K, rl: HsSet<K>, rr: HsSet<K>) -> HsSet<K>:
  match rl:
    case HsSet.Tip{}:
      HsSet.bin(K, rk, HsSet.bin(K, k, l, HsSet.Tip{}), rr)
    case HsSet.Bin{s, k2, a, b}:
      HsSet.bin(K, k2, HsSet.bin(K, k, l, a), HsSet.bin(K, rk, b, rr))

def HsSet.rotl1(-K: Data, single: Bool, k: K, l: HsSet<K>, rk: K, rl: HsSet<K>, rr: HsSet<K>) -> HsSet<K>:
  match single:
    case True{}:
      HsSet.bin(K, rk, HsSet.bin(K, k, l, rl), rr)
    case False{}:
      HsSet.rotl2(K, k, l, rk, rl, rr)

def HsSet.rotl(-K: Data, k: K, l: HsSet<K>, r: HsSet<K>) -> HsSet<K>:
  match r:
    case HsSet.Tip{}:
      HsSet.bin(K, k, l, HsSet.Tip{})
    case HsSet.Bin{s, rk, +rl, +rr}:
      HsSet.rotl1(K, U32.is_lt(HsSet.sz(K, rl), U32.mul(2, HsSet.sz(K, rr))), k, l, rk, rl, rr)

def HsSet.rotr2(-K: Data, k: K, r: HsSet<K>, lk: K, ll: HsSet<K>, lr: HsSet<K>) -> HsSet<K>:
  match lr:
    case HsSet.Tip{}:
      HsSet.bin(K, lk, ll, HsSet.bin(K, k, HsSet.Tip{}, r))
    case HsSet.Bin{s, k2, a, b}:
      HsSet.bin(K, k2, HsSet.bin(K, lk, ll, a), HsSet.bin(K, k, b, r))

def HsSet.rotr1(-K: Data, single: Bool, k: K, r: HsSet<K>, lk: K, ll: HsSet<K>, lr: HsSet<K>) -> HsSet<K>:
  match single:
    case True{}:
      HsSet.bin(K, lk, ll, HsSet.bin(K, k, lr, r))
    case False{}:
      HsSet.rotr2(K, k, r, lk, ll, lr)

def HsSet.rotr(-K: Data, k: K, l: HsSet<K>, r: HsSet<K>) -> HsSet<K>:
  match l:
    case HsSet.Tip{}:
      HsSet.bin(K, k, HsSet.Tip{}, r)
    case HsSet.Bin{s, lk, +ll, +lr}:
      HsSet.rotr1(K, U32.is_lt(HsSet.sz(K, lr), U32.mul(2, HsSet.sz(K, ll))), k, r, lk, ll, lr)

def HsSet.bal.at(-K: Data, d: HsDir, n: U32, k: K, l: HsSet<K>, r: HsSet<K>) -> HsSet<K>:
  match d:
    case HsDir.N{}:
      HsSet.Bin{n, k, l, r}
    case HsDir.L{}:
      HsSet.rotl(K, k, l, r)
    case HsDir.R{}:
      HsSet.rotr(K, k, l, r)

def HsSet.bal(-K: Data, k: K, +l: HsSet<K>, +r: HsSet<K>) -> HsSet<K>:
  +sl = HsSet.sz(K, l)
  +sr = HsSet.sz(K, r)
  HsSet.bal.at(K, HsDir.of(sl, sr), U32.inc(U32.add(sl, sr)), k, l, r)

def HsSet.first(~K: Data, ~cmp: K -> K -> Cmp, k: K, m: HsSet<K>) -> Cmp:
  match m:
    case HsSet.Tip{}:
      LT{}
    case HsSet.Bin{s, k2, l, r}:
      cmp(k, k2)

def HsSet.member.go(~K: Data, ~cmp: K -> K -> Cmp, m: HsSet<K>, c: Cmp, +k: K) -> Bool:
  match m c:
    case HsSet.Tip{} _:
      False{}
    case HsSet.Bin{s, k2, +l, r} LT{}:
      HsSet.member.go(~K, ~cmp, l, HsSet.first(~K, ~cmp, k, l), k)
    case HsSet.Bin{s, k2, l, r} EQ{}:
      True{}
    case HsSet.Bin{s, k2, l, +r} GT{}:
      HsSet.member.go(~K, ~cmp, r, HsSet.first(~K, ~cmp, k, r), k)

def HsSet.member(~K: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsSet<K>) -> Bool:
  HsSet.member.go(~K, ~cmp, m, HsSet.first(~K, ~cmp, k, m), k)

def HsSet.minv.bal(-K: Data, w: HsSet.View<K>, k: K, r: HsSet<K>) -> HsSet.View<K>:
  match w:
    case HsSet.View{km, l}:
      HsSet.View{km, HsSet.bal(K, k, l, r)}

def HsSet.minv(-K: Data, l: HsSet<K>, k: K, r: HsSet<K>) -> HsSet.View<K>:
  match l:
    case HsSet.Tip{}:
      HsSet.View{k, r}
    case HsSet.Bin{s, kl, ll, lr}:
      HsSet.minv.bal(K, HsSet.minv(K, ll, kl, lr), k, r)

def HsSet.maxv.bal(-K: Data, w: HsSet.View<K>, k: K, l: HsSet<K>) -> HsSet.View<K>:
  match w:
    case HsSet.View{km, r}:
      HsSet.View{km, HsSet.bal(K, k, l, r)}

def HsSet.maxv(-K: Data, r: HsSet<K>, k: K, l: HsSet<K>) -> HsSet.View<K>:
  match r:
    case HsSet.Tip{}:
      HsSet.View{k, l}
    case HsSet.Bin{s, kr, rl, rr}:
      HsSet.maxv.bal(K, HsSet.maxv(K, rr, kr, rl), k, l)

def HsSet.glue.l(-K: Data, w: HsSet.View<K>, r: HsSet<K>) -> HsSet<K>:
  match w:
    case HsSet.View{k, l}:
      HsSet.bal(K, k, l, r)

def HsSet.glue.r(-K: Data, w: HsSet.View<K>, l: HsSet<K>) -> HsSet<K>:
  match w:
    case HsSet.View{k, r}:
      HsSet.bal(K, k, l, r)

def HsSet.glue.at(-K: Data, b: Bool, l: HsSet<K>, r: HsSet<K>) -> HsSet<K>:
  match b l r:
    case _ HsSet.Tip{} r2:
      r2
    case _ l2 HsSet.Tip{}:
      l2
    case True{} HsSet.Bin{s, k, ll, lr} HsSet.Bin{s2, k2, rl, rr}:
      HsSet.glue.l(K, HsSet.maxv(K, lr, k, ll), HsSet.Bin{s2, k2, rl, rr})
    case False{} HsSet.Bin{s, k, ll, lr} HsSet.Bin{s2, k2, rl, rr}:
      HsSet.glue.r(K, HsSet.minv(K, rl, k2, rr), HsSet.Bin{s, k, ll, lr})

def HsSet.glue(-K: Data, +l: HsSet<K>, +r: HsSet<K>) -> HsSet<K>:
  HsSet.glue.at(K, U32.is_lt(HsSet.sz(K, r), HsSet.sz(K, l)), l, r)

def HsSet.delete.go(~K: Data, ~cmp: K -> K -> Cmp, m: HsSet<K>, c: Cmp, +k: K) -> HsSet<K>:
  match m c:
    case HsSet.Tip{} _:
      HsSet.Tip{}
    case HsSet.Bin{s, k2, +l, r} LT{}:
      HsSet.bal(K, k2, HsSet.delete.go(~K, ~cmp, l, HsSet.first(~K, ~cmp, k, l), k), r)
    case HsSet.Bin{s, k2, l, r} EQ{}:
      HsSet.glue(K, l, r)
    case HsSet.Bin{s, k2, l, +r} GT{}:
      HsSet.bal(K, k2, l, HsSet.delete.go(~K, ~cmp, r, HsSet.first(~K, ~cmp, k, r), k))

def HsSet.delete(~K: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsSet<K>) -> HsSet<K>:
  HsSet.delete.go(~K, ~cmp, m, HsSet.first(~K, ~cmp, k, m), k)

def HsSet.build.join(-K: Data, n: U32, k: K, l: HsSet<K>, c: HsSet.Cut<K>) -> HsSet.Cut<K>:
  match c:
    case HsSet.Cut{r, t}:
      HsSet.Cut{HsSet.Bin{n, k, l, r}, t}

def HsSet.build.node(-K: Data, n: U32, c: HsSet.Cut<K>, next: List<&2, K> -> HsSet.Cut<K>) -> HsSet.Cut<K>:
  match c:
    case HsSet.Cut{l, Nil{}}:
      HsSet.Cut{l, Nil{}}
    case HsSet.Cut{l, k <> t}:
      HsSet.build.join(K, n, k, l, next(t))

def HsSet.build(-K: Data, d: Nat, z: Bool, +n: U32, xs: List<&2, K>) -> HsSet.Cut<K>:
  match d z:
    case 0n _:
      HsSet.Cut{HsSet.Tip{}, xs}
    case _ True{}:
      HsSet.Cut{HsSet.Tip{}, xs}
    case 1n++e False{}:
      +h = U32.shr(U32.sub(n, 1))
      +j = U32.sub(U32.sub(n, 1), h)
      HsSet.build.node(K, n, HsSet.build(K, e, U32.is_eq(h, 0), h, xs), t => HsSet.build(K, e, U32.is_eq(j, 0), j, t))

def HsSet.build.m(-K: Data, c: HsSet.Cut<K>) -> HsSet<K>:
  match c:
    case HsSet.Cut{m, t}:
      m

def HsSet.fromAsc(~K: Data, +xs: List<&2, K>) -> HsSet<K>:
  +n = HsMap.len(K, xs, 0)
  HsSet.build.m(K, HsSet.build(K, 40n, U32.is_eq(n, 0), n, xs))

def HsSet.insert.go(~K: Data, ~cmp: K -> K -> Cmp, s: HsSet<K>, c: Cmp, +k: K) -> HsSet<K>:
  match s c:
    case HsSet.Tip{} _:
      HsSet.Bin{1, k, HsSet.Tip{}, HsSet.Tip{}}
    case HsSet.Bin{n, k2, +l, r} LT{}:
      HsSet.bal(K, k2, HsSet.insert.go(~K, ~cmp, l, HsSet.first(~K, ~cmp, k, l), k), r)
    case HsSet.Bin{n, k2, l, r} EQ{}:
      HsSet.Bin{n, k2, l, r}
    case HsSet.Bin{n, k2, l, +r} GT{}:
      HsSet.bal(K, k2, l, HsSet.insert.go(~K, ~cmp, r, HsSet.first(~K, ~cmp, k, r), k))

def HsSet.insert(~K: Data, ~cmp: K -> K -> Cmp, +k: K, +s: HsSet<K>) -> HsSet<K>:
  HsSet.insert.go(~K, ~cmp, s, HsSet.first(~K, ~cmp, k, s), k)

def HsSet.toList.go(-K: Data, s: HsSet<K>, acc: List<&2, K>) -> List<&2, K>:
  match s:
    case HsSet.Tip{}:
      acc
    case HsSet.Bin{n, k, l, r}:
      HsSet.toList.go(K, l, k <> HsSet.toList.go(K, r, acc))

def HsSet.toList(~K: Data, s: HsSet<K>) -> List<&2, K>:
  HsSet.toList.go(K, s, Nil{})

def HsSet.fromList.go(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>, acc: HsSet<K>) -> HsSet<K>:
  match xs:
    case Nil{}:
      acc
    case k <> t:
      HsSet.fromList.go(~K, ~cmp, t, HsSet.insert(~K, ~cmp, k, acc))

def HsSet.fromList(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>) -> HsSet<K>:
  HsSet.fromList.go(~K, ~cmp, xs, HsSet.Tip{})

# the smaller's keys put in the larger
def HsSet.union.at(~K: Data, ~cmp: K -> K -> Cmp, c: Bool, a: HsSet<K>, b: HsSet<K>) -> HsSet<K>:
  match c:
    case True{}:
      HsSet.fromList.go(~K, ~cmp, HsSet.toList(~K, a), b)
    case False{}:
      HsSet.fromList.go(~K, ~cmp, HsSet.toList(~K, b), a)

def HsSet.union(~K: Data, ~cmp: K -> K -> Cmp, +a: HsSet<K>, +b: HsSet<K>) -> HsSet<K>:
  HsSet.union.at(~K, ~cmp, U32.is_le(HsSet.sz(K, a), HsSet.sz(K, b)), a, b)

def HsSet.unions(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, HsSet<K>>) -> HsSet<K>:
  match xs:
    case Nil{}:
      HsSet.Tip{}
    case s <> t:
      HsSet.union(~K, ~cmp, s, HsSet.unions(~K, ~cmp, t))

# the keys p keeps, in order
def HsSet.keep.at(-K: Data, b: Bool, k: K, r: List<&2, K>) -> List<&2, K>:
  match b:
    case True{}:
      k <> r
    case False{}:
      r

def HsSet.keep(~K: Data, ~p: K -> Bool, s: HsSet<K>, acc: List<&2, K>) -> List<&2, K>:
  match s:
    case HsSet.Tip{}:
      acc
    case HsSet.Bin{n, +k, l, r}:
      HsSet.keep(~K, ~p, l, HsSet.keep.at(K, p(k), k, HsSet.keep(~K, ~p, r, acc)))

def HsSet.filter(~K: Data, ~p: K -> Bool, s: HsSet<K>) -> HsSet<K>:
  HsSet.fromAsc(~K, HsSet.keep(~K, ~p, s, Nil{}))

def HsSet.dels(~K: Data, ~cmp: K -> K -> Cmp, ks: List<&2, K>, s: HsSet<K>) -> HsSet<K>:
  match ks:
    case Nil{}:
      s
    case k <> t:
      HsSet.dels(~K, ~cmp, t, HsSet.delete(~K, ~cmp, k, s))

# the keys of xs in b (or, w False, not in it)
def HsSet.within(~K: Data, ~cmp: K -> K -> Cmp, +w: Bool, xs: List<&2, K>, +b: HsSet<K>) -> List<&2, K>:
  match xs:
    case Nil{}:
      Nil{}
    case +k <> t:
      HsSet.keep.at(K, Bool.not(Bool.xor(w, HsSet.member(~K, ~cmp, k, b))), k, HsSet.within(~K, ~cmp, w, t, b))

def HsSet.difference.at(~K: Data, ~cmp: K -> K -> Cmp, c: Bool, a: HsSet<K>, b: HsSet<K>) -> HsSet<K>:
  match c:
    case True{}:
      HsSet.dels(~K, ~cmp, HsSet.toList(~K, b), a)
    case False{}:
      HsSet.fromAsc(~K, HsSet.within(~K, ~cmp, False{}, HsSet.toList(~K, a), b))

def HsSet.difference(~K: Data, ~cmp: K -> K -> Cmp, +a: HsSet<K>, +b: HsSet<K>) -> HsSet<K>:
  HsSet.difference.at(~K, ~cmp, U32.is_le(HsSet.sz(K, b), HsSet.sz(K, a)), a, b)

# the set's own key at k
def HsSet.entry.go(~K: Data, ~cmp: K -> K -> Cmp, m: HsSet<K>, c: Cmp, +k: K) -> Maybe<&2, K>:
  match m c:
    case HsSet.Tip{} _:
      None{}
    case HsSet.Bin{s, k2, +l, r} LT{}:
      HsSet.entry.go(~K, ~cmp, l, HsSet.first(~K, ~cmp, k, l), k)
    case HsSet.Bin{s, k2, l, r} EQ{}:
      Some{k2}
    case HsSet.Bin{s, k2, l, +r} GT{}:
      HsSet.entry.go(~K, ~cmp, r, HsSet.first(~K, ~cmp, k, r), k)

def HsSet.entry(~K: Data, ~cmp: K -> K -> Cmp, +k: K, +m: HsSet<K>) -> Maybe<&2, K>:
  HsSet.entry.go(~K, ~cmp, m, HsSet.first(~K, ~cmp, k, m), k)

def HsSet.inter.at(-K: Data, e: Maybe<&2, K>, r: List<&2, K>) -> List<&2, K>:
  match e:
    case None{}:
      r
    case Some{k}:
      k <> r

# a's own keys at the keys xs
def HsSet.inter(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>, +a: HsSet<K>) -> List<&2, K>:
  match xs:
    case Nil{}:
      Nil{}
    case k <> t:
      HsSet.inter.at(K, HsSet.entry(~K, ~cmp, k, a), HsSet.inter(~K, ~cmp, t, a))

def HsSet.intersection.on(~K: Data, ~cmp: K -> K -> Cmp, s: Bool, a: HsSet<K>, b: HsSet<K>) -> HsSet<K>:
  match s:
    case True{}:
      HsSet.fromAsc(~K, HsSet.within(~K, ~cmp, True{}, HsSet.toList(~K, a), b))
    case False{}:
      HsSet.fromAsc(~K, HsSet.inter(~K, ~cmp, HsSet.toList(~K, b), a))

# intersection a b: a's keys b holds (the smaller looked up in the larger)
def HsSet.intersection(~K: Data, ~cmp: K -> K -> Cmp, +a: HsSet<K>, +b: HsSet<K>) -> HsSet<K>:
  HsSet.intersection.on(~K, ~cmp, U32.is_le(HsSet.sz(K, a), HsSet.sz(K, b)), a, b)

def HsSet.map.go(~K: Data, ~L: Data, ~cmp: L -> L -> Cmp, ~f: K -> L, xs: List<&2, K>, acc: HsSet<L>) -> HsSet<L>:
  match xs:
    case Nil{}:
      acc
    case k <> t:
      HsSet.map.go(~K, ~L, ~cmp, ~f, t, HsSet.insert(~L, ~cmp, f(k), acc))

def HsSet.map(~K: Data, ~L: Data, ~cmp: L -> L -> Cmp, ~f: K -> L, s: HsSet<K>) -> HsSet<L>:
  HsSet.map.go(~K, ~L, ~cmp, ~f, HsSet.toList(~K, s), HsSet.Tip{})

def HsSet.size(~K: Data, s: HsSet<K>) -> Nat:
  U32.to_nat(HsSet.sz(K, s))

def HsSet.null(~K: Data, s: HsSet<K>) -> Bool:
  match s:
    case HsSet.Tip{}:
      True{}
    case HsSet.Bin{n, k, l, r}:
      False{}

def HsSet.eq.go(~K: Data, ~eqk: K -> K -> Bool, a: List<&2, K>, b: List<&2, K>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case k1 <> t1 k2 <> t2:
      Bool.and(eqk(k1)(k2), HsSet.eq.go(~K, ~eqk, t1, t2))
    case _ _:
      False{}

def HsSet.eq(~K: Data, ~eqk: K -> K -> Bool, a: HsSet<K>, b: HsSet<K>) -> Bool:
  HsSet.eq.go(~K, ~eqk, HsSet.toList(~K, a), HsSet.toList(~K, b))

def HsCmp.set.go(~K: Data, ~ck: K -> K -> Cmp, a: List<&2, K>, b: List<&2, K>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} _:
      LT{}
    case _ Nil{}:
      GT{}
    case k1 <> r1 k2 <> r2:
      HsCmp.on(Cmp, ck(k1)(k2), _ => LT{}, _ => HsCmp.set.go(~K, ~ck, r1, r2), _ => GT{})

def HsCmp.set(~K: Data, ~ck: K -> K -> Cmp, a: HsSet<K>, b: HsSet<K>) -> Cmp:
  HsCmp.set.go(~K, ~ck, HsSet.toList(~K, a), HsSet.toList(~K, b))

def HsSet.empty(~K: Data) -> HsSet<K>:
  HsSet.Tip{}

def HsSet.singleton(~K: Data, k: K) -> HsSet<K>:
  HsSet.Bin{1, k, HsSet.Tip{}, HsSet.Tip{}}

def HsSet.notMember(~K: Data, ~cmp: K -> K -> Cmp, k: K, s: HsSet<K>) -> Bool:
  Bool.not(HsSet.member(~K, ~cmp, k, s))

# ---- a map and a set

# m's pairs whose key s holds (or, w False, does not)
def HsMap.within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +w: Bool, xs: List<&2, Sigma<&2, &2, K, _ => V>>, +s: HsSet<K>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match xs:
    case Nil{}:
      Nil{}
    case (+k, v) <> t:
      HsMap.keep.at(K, V, Bool.not(Bool.xor(w, HsSet.member(~K, ~cmp, k, s))), k, v, HsMap.within(~K, ~V, ~cmp, w, t, s))

# the pairs of m at the keys xs
def HsMap.pick.at(-K: Data, -V: Data, e: Maybe<&2, Sigma<&2, &2, K, _ => V>>, r: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match e:
    case None{}:
      r
    case Some{kv}:
      kv <> r

def HsMap.pick(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>, +m: HsMap<K, V>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match xs:
    case Nil{}:
      Nil{}
    case k <> t:
      HsMap.pick.at(K, V, HsMap.entry(~K, ~V, ~cmp, k, m), HsMap.pick(~K, ~V, ~cmp, t, m))

def HsMap.restrictKeys.on(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, b: Bool, m: HsMap<K, V>, s: HsSet<K>) -> HsMap<K, V>:
  match b:
    case True{}:
      HsMap.fromAsc(~K, ~V, HsMap.within(~K, ~V, ~cmp, True{}, HsMap.toList(~K, ~V, m), s))
    case False{}:
      HsMap.fromAsc(~K, ~V, HsMap.pick(~K, ~V, ~cmp, HsSet.toList(~K, s), m))

# restrictKeys m s: m's pairs whose key s holds (the smaller looked up in the
# larger)
def HsMap.restrictKeys(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m: HsMap<K, V>, +s: HsSet<K>) -> HsMap<K, V>:
  HsMap.restrictKeys.on(~K, ~V, ~cmp, U32.is_le(HsMap.sz(K, V, m), HsSet.sz(K, s)), m, s)

def HsMap.withoutKeys.on(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, b: Bool, m: HsMap<K, V>, s: HsSet<K>) -> HsMap<K, V>:
  match b:
    case True{}:
      HsMap.fromAsc(~K, ~V, HsMap.within(~K, ~V, ~cmp, False{}, HsMap.toList(~K, ~V, m), s))
    case False{}:
      HsMap.dels(~K, ~V, ~cmp, HsSet.toList(~K, s), m)

# withoutKeys m s: m's pairs whose key s does not hold
def HsMap.withoutKeys(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m: HsMap<K, V>, +s: HsSet<K>) -> HsMap<K, V>:
  HsMap.withoutKeys.on(~K, ~V, ~cmp, U32.is_le(HsMap.sz(K, V, m), HsSet.sz(K, s)), m, s)

# fromSet f s: each key of s with f at it
def HsMap.fromSet(~K: Data, ~V: Data, ~f: K -> V, s: HsSet<K>) -> HsMap<K, V>:
  match s:
    case HsSet.Tip{}:
      HsMap.Tip{}
    case HsSet.Bin{n, +k, l, r}:
      HsMap.Bin{n, k, f(k), HsMap.fromSet(~K, ~V, ~f, l), HsMap.fromSet(~K, ~V, ~f, r)}

#@after HsPt.bind
# the partial ones, in the keys' order

def HsPt.mmap.go(~K: Data, ~V: Data, ~W: Data, ~f: K -> V -> Either<&2, &2, List<&2, Char>, W>, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> Either<&2, &2, List<&2, Char>, List<&2, Sigma<&2, &2, K, _ => W>>>:
  match xs:
    case Nil{}:
      Inr{Nil{}}
    case (+k, +v) <> t:
      HsPt.bind(W, List<&2, Sigma<&2, &2, K, _ => W>>, f(k)(v), w => HsPt.bind(List<&2, Sigma<&2, &2, K, _ => W>>, List<&2, Sigma<&2, &2, K, _ => W>>, HsPt.mmap.go(~K, ~V, ~W, ~f, t), r => Inr{(k, w) <> r}))

def HsPt.mmapk(~K: Data, ~V: Data, ~W: Data, ~f: K -> V -> Either<&2, &2, List<&2, Char>, W>, m: HsMap<K, V>) -> Either<&2, &2, List<&2, Char>, HsMap<K, W>>:
  HsPt.bind(List<&2, Sigma<&2, &2, K, _ => W>>, HsMap<K, W>, HsPt.mmap.go(~K, ~V, ~W, ~f, HsMap.toList(~K, ~V, m)), r => Inr{HsMap.fromAsc(~K, ~W, r)})

def HsPt.mmap(~K: Data, ~V: Data, ~W: Data, ~f: V -> Either<&2, &2, List<&2, Char>, W>, m: HsMap<K, V>) -> Either<&2, &2, List<&2, Char>, HsMap<K, W>>:
  HsPt.mmapk(~K, ~V, ~W, ~(k => f), m)

def HsPt.mkeep(-K: Data, -V: Data, k: K, v: V, b: Bool, r: List<&2, Sigma<&2, &2, K, _ => V>>) -> List<&2, Sigma<&2, &2, K, _ => V>>:
  match b:
    case True{}:
      (k, v) <> r
    case False{}:
      r

def HsPt.mfilter.go(~K: Data, ~V: Data, ~p: V -> Either<&2, &2, List<&2, Char>, Bool>, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> Either<&2, &2, List<&2, Char>, List<&2, Sigma<&2, &2, K, _ => V>>>:
  match xs:
    case Nil{}:
      Inr{Nil{}}
    case (k, +v) <> t:
      HsPt.bind(Bool, List<&2, Sigma<&2, &2, K, _ => V>>, p(v), b => HsPt.bind(List<&2, Sigma<&2, &2, K, _ => V>>, List<&2, Sigma<&2, &2, K, _ => V>>, HsPt.mfilter.go(~K, ~V, ~p, t), r => Inr{HsPt.mkeep(K, V, k, v, b, r)}))

def HsPt.mfilter(~K: Data, ~V: Data, ~p: V -> Either<&2, &2, List<&2, Char>, Bool>, m: HsMap<K, V>) -> Either<&2, &2, List<&2, Char>, HsMap<K, V>>:
  HsPt.bind(List<&2, Sigma<&2, &2, K, _ => V>>, HsMap<K, V>, HsPt.mfilter.go(~K, ~V, ~p, HsMap.toList(~K, ~V, m)), r => Inr{HsMap.fromAsc(~K, ~V, r)})

def HsPt.mfoldr.go(~K: Data, ~V: Data, ~B: Data, ~f: V -> B -> Either<&2, &2, List<&2, Char>, B>, xs: List<&2, Sigma<&2, &2, K, _ => V>>, z: B) -> Either<&2, &2, List<&2, Char>, B>:
  match xs:
    case Nil{}:
      Inr{z}
    case (k, +v) <> t:
      HsPt.bind(B, B, HsPt.mfoldr.go(~K, ~V, ~B, ~f, t, z), +r => f(v)(r))

def HsPt.mfoldr(~K: Data, ~V: Data, ~B: Data, ~f: V -> B -> Either<&2, &2, List<&2, Char>, B>, z: B, m: HsMap<K, V>) -> Either<&2, &2, List<&2, Char>, B>:
  HsPt.mfoldr.go(~K, ~V, ~B, ~f, HsMap.toList(~K, ~V, m), z)
#@after HsInt.negate
# a - b for Nats, as an integer (HsPrelude's counts both down; Nat's own are
# the machine's)
def HsInt.nsub(+a: Nat, +b: Nat) -> HsInt:
  Bool.pick(HsInt, Nat.is_lt(a, b), HsInt.neg.of(Nat.sub(b, a)), HsInt.Pos{Nat.sub(a, b)})
#@after HsList.insertBy
# sortBy as a merge sort, stable (HsPrelude's is an insertion sort)
def HsList.mergeBy(~A: Data, ~cmp: A -> A -> Cmp, n: Nat, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match n xs ys:
    case 0n a b:
      List.append(&2, A, a, b)
    case 1n+p Nil{} b:
      b
    case 1n+p x <> a Nil{}:
      x <> a
    case 1n+(+p) +x <> +a +y <> +b:
      HsCmp.on(List<&2, A>, cmp(x)(y), _ => x <> HsList.mergeBy(~A, ~cmp, p, a, y <> b), _ => x <> HsList.mergeBy(~A, ~cmp, p, a, y <> b), _ => y <> HsList.mergeBy(~A, ~cmp, p, x <> a, b))

def HsList.mergePairs(~A: Data, ~cmp: A -> A -> Cmp, rs: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  match rs:
    case Nil{}:
      Nil{}
    case a <> Nil{}:
      [a]
    case a <> b <> t:
      HsList.mergeBy(~A, ~cmp, U32.to_nat(4294967295), a, b) <> HsList.mergePairs(~A, ~cmp, t)

def HsList.mergeRuns(~A: Data, ~cmp: A -> A -> Cmp, n: Nat, rs: List<&2, List<&2, A>>) -> List<&2, A>:
  match n rs:
    case _ Nil{}:
      Nil{}
    case _ a <> Nil{}:
      a
    case 1n+p a <> b <> t:
      HsList.mergeRuns(~A, ~cmp, p, HsList.mergePairs(~A, ~cmp, a <> b <> t))
    case 0n a <> t:
      a

def HsList.singles(~A: Data, xs: List<&2, A>) -> List<&2, List<&2, A>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      [x] <> HsList.singles(~A, t)

def HsList.sortBy(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> List<&2, A>:
  HsList.mergeRuns(~A, ~cmp, 64n, HsList.singles(~A, xs))
