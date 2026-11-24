import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X
import ./a2b/ToBend/Ast.bend as T
import ./Survey.bend as V
import ./Fold.bend as F
import ./Cache.bend as C
import ./Back.bend as K

# Law: cata hs's example laws (PLAN.md, step 2's oracle).  It folds each
# module as Fold.bend does, gates it, and then holds every def the gate
# kept to the original Haskell on small inputs:
#
#   law OUT FILE.sexp...
#
# For each def it lists inputs by the Haskell type (smallest first, the
# same every run), writes them as Haskell and as Bend, and writes a GHCi
# script (OUT/NAME.ghci) that runs the original function on each input,
# printing the output as an S-expression (OUT/NAME.ghc holds what GHCi
# said).  Each output becomes a law, a def whose type is the equality
#
#   def f.exK() -> {f(a, b) == v : R}:
#     {==}
#
# and the gate runs again with the laws in.  A law Bend refuses takes its
# def out (and whatever uses it), with the law's first error line as the
# reason.  OUT/NAME.bend is then the module with its laws, and
# OUT/ledger.tsv gets, for every binding a user wrote, one line
#
#   FILE  NAME  ok-law|ok-check|ok-type|out  WHY
#
# ok-law: the def checks and K example laws hold (WHY is `laws:K`);
# ok-check: the def checks and has no law (WHY says why: a function
# argument, a type the inputs do not cover, no input GHC answered);
# ok-type: a data type that checks; out: as Fold's ledger, or `law:..`.
# The three levels are never one label (PLAN.md, rule 3).  GHC is only
# the oracle: what it says about the original is taken as the law; no
# model takes part.
#
# Inputs: Int, Integer and Natural are 0..3 (the fold writes them as Nat,
# and the survey keeps out what subtracts), Bool both, Char 'a' 'b' ' ',
# lists up to three elements, Maybe, Either, tuples, Ordering, unit, and
# the module's own data types two constructors deep; a type variable is
# Int.  At most 8 inputs per def, ordered by the sum of each argument's
# place in its own list.
#
# BEND names the bend to check with, GHC the ghc (the flake's .#ghc).
# Every def is prefixed `lw.`.

# Text ---------------------------------------------------------------------

def lw.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def lw.cat3(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> List<&2, U32>:
  lw.cat(a, lw.cat(b, c))

# the bytes after the first: a list printed with a separator in front of
# each element, without the first one
def lw.tail1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case h <> t:
      t
    case Nil{}:
      Nil{}

def lw.nshow(n: Nat) -> List<&2, U32>:
  S.b(Nat.show(n))

# a list tree of strings: ("c" "a")
def lw.strs(x: X.Sx) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{h, t}:
      X.tsx.str.of(h) <> lw.strs(t)
    case _:
      Nil{}

# whether a name holds a dot (a law's: f.ex3; no Haskell name the fold
# writes as a def does)
def lw.dotted(xs: List<&2, U32>) -> Bool:
  match xs:
    case +h <> t:
      Bool.or(U32.is_eq(h, 46), lw.dotted(t))
    case Nil{}:
      False{}

# the name after the first dot
def lw.afterdot(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +h <> +t:
      F.fd.bpick(U32.is_eq(h, 46), t, lw.afterdot(t))
    case Nil{}:
      Nil{}

# whether a dotted name is a law's, NAME.exK (not a def lifted out of
# NAME, NAME.lK or NAME.go)
def lw.islaw(+k: List<&2, U32>) -> Bool:
  S.prefix(lw.afterdot(k), S.b("ex"))

# whether a dotted name is a def a type of the module has (T.eq, T.cata:
# its first letter a capital), not a law or a def lifted out of a function
def lw.upper(xs: List<&2, U32>) -> Bool:
  match xs:
    case +h <> t:
      Bool.and(U32.is_ge(h, 65), U32.is_le(h, 90))
    case Nil{}:
      False{}

def lw.tydef(+n: List<&2, U32>) -> Bool:
  Bool.and(lw.dotted(n), lw.upper(n))

# the name before the first dot
def lw.undot(xs: List<&2, U32>) -> List<&2, U32>:
  S.until(xs, 46)

# Haskell types ------------------------------------------------------------

# A Haskell type at the instance the laws use (every type variable Int).
# HyNat keeps the Haskell name (Int, Integer or Natural) for GHCi; a
# user type's arguments and a constructor's fields are an HyArgs spine.
type Hy is Data:
  HyNat{hs: List<&2, U32>}
  HyInt{hs: List<&2, U32>}
  HyBool{}
  HyChar{}
  HyUnit{}
  HyCmp{}
  HyList{a: Hy}
  HyMaybe{a: Hy}
  HyEither{a: Hy, b: Hy}
  HyT2{a: Hy, b: Hy}
  HyT3{a: Hy, b: Hy, c: Hy}
  HyUser{n: List<&2, U32>, args: Hy}
  HyFun{a: Hy, b: Hy}
  HyNo{why: List<&2, U32>}
  HyArgs{a: Hy, rest: Hy}
  HyANil{}

# Base's types the laws cover
type Bk is Data:
  BkInt{}
  BkHsInt{}
  BkHsInteger{}
  BkInteger{}
  BkNatural{}
  BkBool{}
  BkChar{}
  BkStr{}
  BkUnit{}
  BkCmp{}
  BkList{}
  BkMaybe{}
  BkEither{}
  BkT2{}
  BkT3{}
  BkNone{}

type BkE is Data:
  BkE{k: String, v: Bk}

def lw.bktab() -> List<&2, BkE>:
  [BkE{"GHC.Types.Int", BkInt{}}, BkE{"GHC.Num.Integer.Integer", BkInteger{}}, BkE{"GHC.Num.Natural.Natural", BkNatural{}}, BkE{"GHC.Types.Bool", BkBool{}}, BkE{"GHC.Types.Char", BkChar{}}, BkE{"GHC.Types.List", BkList{}}, BkE{"GHC.Internal.Base.String", BkStr{}}, BkE{"GHC.Internal.IO.FilePath", BkStr{}}, BkE{"GHC.Internal.Maybe.Maybe", BkMaybe{}}, BkE{"GHC.Internal.Data.Either.Either", BkEither{}}, BkE{"GHC.Tuple.Tuple2", BkT2{}}, BkE{"GHC.Tuple.Tuple3", BkT3{}}, BkE{"GHC.Tuple.Unit", BkUnit{}}, BkE{"GHC.Types.Ordering", BkCmp{}}, BkE{"HsPrelude.HsInt", BkHsInt{}}, BkE{"HsPrelude.HsInteger", BkHsInteger{}}]

def lw.bk.find(xs: List<&2, BkE>, +k: List<&2, U32>) -> Bk:
  match xs:
    case Nil{}:
      BkNone{}
    case BkE{s, v} <> t:
      Bool.pick(Bk, S.eq(S.b(s), k), v, lw.bk.find(t, k))

def lw.base(k: Bk, key: List<&2, U32>, args: Hy) -> Hy:
  match k args:
    case BkInt{} _:
      HyNat{S.b("LawP.Int")}
    case BkHsInt{} _:
      HyInt{S.b("LawP.Int")}
    case BkHsInteger{} _:
      HyInt{S.b("LawP.Integer")}
    case BkInteger{} _:
      HyNat{S.b("LawP.Integer")}
    case BkNatural{} _:
      HyNat{S.b("LawN.Natural")}
    case BkBool{} _:
      HyBool{}
    case BkChar{} _:
      HyChar{}
    case BkStr{} _:
      HyList{HyChar{}}
    case BkUnit{} _:
      HyUnit{}
    case BkCmp{} _:
      HyCmp{}
    case BkList{} HyArgs{a, _}:
      HyList{a}
    case BkMaybe{} HyArgs{a, _}:
      HyMaybe{a}
    case BkEither{} HyArgs{a, HyArgs{b, _}}:
      HyEither{a, b}
    case BkT2{} HyArgs{a, HyArgs{b, _}}:
      HyT2{a, b}
    case BkT3{} HyArgs{a, HyArgs{b, HyArgs{c, _}}}:
      HyT3{a, b, c}
    case _ _:
      HyNo{lw.cat(S.b("type:"), key)}

# the module's type synonyms, and a type variable's instance
type Sy is Data:
  Sy{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, body: X.Sx}

type Sb is Data:
  Sb{v: List<&2, U32>, h: Hy}

# where a type is read: the module, its synonyms, the type variables bound
type Le is Data:
  Le{m: List<&2, U32>, syns: List<&2, Sy>, sub: List<&2, Sb>}

def lw.le.m(+le: Le) -> List<&2, U32>:
  match le:
    case Le{m, s, b}:
      m

def lw.le.syns(+le: Le) -> List<&2, Sy>:
  match le:
    case Le{m, s, b}:
      s

def lw.le.sub(+le: Le) -> List<&2, Sb>:
  match le:
    case Le{m, s, b}:
      b

def lw.le.with(le: Le, sub: List<&2, Sb>) -> Le:
  match le:
    case Le{m, s, b}:
      Le{m, s, sub}

# a type variable: its instance, Int when nothing binds it
def lw.sub.find(xs: List<&2, Sb>, +v: List<&2, U32>) -> Hy:
  match xs:
    case Nil{}:
      HyNat{S.b("LawP.Int")}
    case Sb{k, h} <> t:
      Bool.pick(Hy, S.eq(k, v), h, lw.sub.find(t, v))

def lw.zip.sub(tvs: List<&2, List<&2, U32>>, args: Hy) -> List<&2, Sb>:
  match tvs args:
    case v <> t HyArgs{a, r}:
      Sb{v, a} <> lw.zip.sub(t, r)
    case _ _:
      Nil{}

def lw.syn.find(ss: List<&2, Sy>, +n: List<&2, U32>) -> Maybe<&2, Sy>:
  match ss:
    case Nil{}:
      None{}
    case Sy{+k, tvs, body} <> t:
      Bool.pick(Maybe<&2, Sy>, S.eq(k, n), Some{Sy{k, tvs, body}}, lw.syn.find(t, n))

# (synonym NAME (TV...) TYPE SPAN)
def lw.syns.if(s: Bool, +x: X.Sx, acc: List<&2, Sy>) -> List<&2, Sy>:
  match s:
    case True{}:
      Sy{V.sv.str(x, 1n), lw.strs(V.sv.at(x, 2n)), V.sv.at(x, 3n)} <> acc
    case False{}:
      acc

def lw.syns(xs: List<&2, X.Sx>) -> List<&2, Sy>:
  match xs:
    case +h <> t:
      lw.syns.if(V.sv.is(V.sv.hd(h), "synonym"), h, lw.syns(t))
    case Nil{}:
      Nil{}

# What a type tree is, read off its head (the walk below takes it as a
# parameter, so it recurses in one def)
type Hh is Data:
  HhTv{}
  HhTc{}
  HhFun{}
  HhIn{}
  HhNo{}

def lw.hh(+h: List<&2, U32>) -> Hh:
  Bool.pick(Hh, V.sv.is(h, "tv"), HhTv{}, Bool.pick(Hh, V.sv.is(h, "tc"), HhTc{}, Bool.pick(Hh, V.sv.is(h, "tfun"), HhFun{}, Bool.pick(Hh, Bool.or(V.sv.is(h, "tforall"), V.sv.is(h, "tctx")), HhIn{}, HhNo{}))))

type Hm is Data:
  HmTv{n: List<&2, U32>}
  HmTc{own: Bool, key: List<&2, U32>, name: List<&2, U32>, args: X.Sx}
  HmSyn{tvs: List<&2, List<&2, U32>>, body: X.Sx, args: X.Sx}
  HmFun{a: X.Sx, b: X.Sx}
  HmIn{t: X.Sx}
  HmChain{x: X.Sx}
  HmNo{why: List<&2, U32>}

def lw.syn.pick(own: Bool, ss: List<&2, Sy>, +n: List<&2, U32>) -> Maybe<&2, Sy>:
  match own:
    case True{}:
      lw.syn.find(ss, n)
    case False{}:
      None{}

def lw.syn.of(found: Maybe<&2, Sy>, own: Bool, key: List<&2, U32>, name: List<&2, U32>, args: X.Sx) -> Hm:
  match found:
    case Some{Sy{n, tvs, body}}:
      HmSyn{tvs, body, args}
    case None{}:
      HmTc{own, key, name, args}

# (tc MOD NAME ARG...): the arguments are what follows the name
def lw.drop3(x: X.Sx) -> X.Sx:
  X.tsx.args(X.tsx.args(X.tsx.args(x)))

def lw.tc.hm(+le: Le, +x: X.Sx) -> Hm:
  +mod = V.sv.str(x, 1n)
  +name = V.sv.str(x, 2n)
  +own = S.eq(mod, lw.le.m(le))
  lw.syn.of(lw.syn.pick(own, lw.le.syns(le), name), own, lw.cat3(mod, [46], name), name, lw.drop3(x))

def lw.hm.of(k: Hh, +le: Le, +x: X.Sx) -> Hm:
  match k:
    case HhTv{}:
      HmTv{V.sv.str(x, 1n)}
    case HhTc{}:
      lw.tc.hm(le, x)
    case HhFun{}:
      HmFun{V.sv.at(x, 1n), V.sv.at(x, 2n)}
    case HhIn{}:
      HmIn{V.sv.at(x, 2n)}
    case HhNo{}:
      HmNo{lw.cat(S.b("type-form:"), V.sv.hd(x))}

def lw.hm(+le: Le, +x: X.Sx) -> Hm:
  lw.hm.of(lw.hh(V.sv.hd(x)), le, x)

def lw.tc(own: Bool, +key: List<&2, U32>, name: List<&2, U32>, args: Hy) -> Hy:
  match own:
    case True{}:
      HyUser{name, args}
    case False{}:
      lw.base(lw.bk.find(lw.bktab(), key), key, args)

# a type tree as an Hy: synonyms of the module expanded, every type
# variable its instance (fuel: synonyms may name synonyms)
def lw.hy(fuel: Nat, +le: Le, m: Hm) -> Hy:
  match fuel m:
    case 0n _:
      HyNo{S.b("type-depth")}
    case 1n+p HmTv{n}:
      lw.sub.find(lw.le.sub(le), n)
    case 1n+p HmTc{own, key, name, args}:
      lw.tc(own, key, name, lw.hy(p, le, HmChain{args}))
    case 1n+(+p) HmSyn{tvs, body, args}:
      +le2 = lw.le.with(le, lw.zip.sub(tvs, lw.hy(p, le, HmChain{args})))
      lw.hy(p, le2, lw.hm(le2, body))
    case 1n+(+p) HmFun{a, b}:
      HyFun{lw.hy(p, le, lw.hm(le, a)), lw.hy(p, le, lw.hm(le, b))}
    case 1n+p HmIn{t}:
      lw.hy(p, le, lw.hm(le, t))
    case 1n+(+p) HmChain{X.SxCons{+h, t}}:
      HyArgs{lw.hy(p, le, lw.hm(le, h)), lw.hy(p, le, HmChain{t})}
    case 1n+p HmChain{_}:
      HyANil{}
    case 1n+p HmNo{w}:
      HyNo{w}

def lw.ty(+le: Le, +x: X.Sx) -> Hy:
  lw.hy(64n, le, lw.hm(le, x))

# a function type's arguments (an HyArgs spine) and its result
def lw.args(h: Hy) -> Hy:
  match h:
    case HyFun{a, b}:
      HyArgs{a, lw.args(b)}
    case _:
      HyANil{}

def lw.res(h: Hy) -> Hy:
  match h:
    case HyFun{a, b}:
      lw.res(b)
    case r:
      r

def lw.first(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      b
    case w:
      w

# why a type has no inputs or outputs the laws can write (empty: none)
def lw.notype(h: Hy) -> List<&2, U32>:
  match h:
    case HyNo{w}:
      w
    case HyFun{a, b}:
      S.b("function")
    case HyList{a}:
      lw.notype(a)
    case HyMaybe{a}:
      lw.notype(a)
    case HyEither{a, b}:
      lw.first(lw.notype(a), lw.notype(b))
    case HyT2{a, b}:
      lw.first(lw.notype(a), lw.notype(b))
    case HyT3{a, b, c}:
      lw.first(lw.notype(a), lw.first(lw.notype(b), lw.notype(c)))
    case HyUser{n, args}:
      lw.notype(args)
    case HyArgs{a, r}:
      lw.first(lw.notype(a), lw.notype(r))
    case _:
      Nil{}

def lw.nargs(h: Hy) -> Nat:
  match h:
    case HyArgs{a, r}:
      1n+lw.nargs(r)
    case _:
      0n

# The type as GHCi reads it in the module's scope (M.T for the module's)
def lw.hs.ty(h: Hy, +m: List<&2, U32>) -> List<&2, U32>:
  match h:
    case HyNat{s}:
      s
    case HyInt{s}:
      s
    case HyBool{}:
      S.b("LawP.Bool")
    case HyChar{}:
      S.b("LawP.Char")
    case HyUnit{}:
      S.b("()")
    case HyCmp{}:
      S.b("LawP.Ordering")
    case HyList{a}:
      91 <> lw.cat(lw.hs.ty(a, m), [93])
    case HyMaybe{a}:
      lw.cat3(S.b("(LawP.Maybe "), lw.hs.ty(a, m), [41])
    case HyEither{a, b}:
      lw.cat3(S.b("(LawP.Either "), lw.hs.ty(a, m), 32 <> lw.cat(lw.hs.ty(b, m), [41]))
    case HyT2{a, b}:
      40 <> lw.cat3(lw.hs.ty(a, m), S.b(", "), lw.cat(lw.hs.ty(b, m), [41]))
    case HyT3{a, b, c}:
      40 <> lw.cat3(lw.hs.ty(a, m), S.b(", "), lw.cat3(lw.hs.ty(b, m), S.b(", "), lw.cat(lw.hs.ty(c, m), [41])))
    case HyUser{n, args}:
      40 <> lw.cat3(m, 46 <> n, lw.cat(lw.hs.ty(args, m), [41]))
    case HyFun{a, b}:
      40 <> lw.cat3(lw.hs.ty(a, m), S.b(" -> "), lw.cat(lw.hs.ty(b, m), [41]))
    case HyArgs{a, r}:
      32 <> lw.cat(lw.hs.ty(a, m), lw.hs.ty(r, m))
    case _:
      Nil{}

# The type in Bend, as the fold writes it (Fold.bend's fd.tc.of)
def lw.bty(h: Hy) -> T.Bt:
  match h:
    case HyNat{s}:
      F.fd.ty0("Nat")
    case HyInt{s}:
      F.fd.ty0("HsPrelude.HsInt")
    case HyBool{}:
      F.fd.ty0("Bool")
    case HyChar{}:
      F.fd.ty0("Char")
    case HyUnit{}:
      F.fd.ty0("Unit")
    case HyCmp{}:
      F.fd.ty0("Cmp")
    case HyList{a}:
      F.fd.list(lw.bty(a))
    case HyMaybe{a}:
      T.BtTyApp{S.b("Maybe"), T.BtArgs{F.fd.v("&2"), T.BtArgs{lw.bty(a), T.BtANil{}}}}
    case HyEither{a, b}:
      T.BtTyApp{S.b("Either"), T.BtArgs{F.fd.v("&2"), T.BtArgs{F.fd.v("&2"), T.BtArgs{lw.bty(a), T.BtArgs{lw.bty(b), T.BtANil{}}}}}}
    case HyT2{a, b}:
      F.fd.pair(lw.bty(a), lw.bty(b))
    case HyT3{a, b, c}:
      F.fd.pair(lw.bty(a), F.fd.pair(lw.bty(b), lw.bty(c)))
    case HyUser{n, args}:
      T.BtTyApp{F.fd.tyname(n), lw.bty(args)}
    case HyArgs{a, r}:
      T.BtArgs{lw.bty(a), lw.bty(r)}
    case HyANil{}:
      T.BtANil{}
    case _:
      T.BtTodo{S.b("law:type")}

# The module's data types --------------------------------------------------

type Dd is Data:
  Dd{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, cs: X.Sx}

# (data NAME (TV...) (CON...) SPAN), a newtype the same
def lw.dds.if(d: Bool, +x: X.Sx, acc: List<&2, Dd>) -> List<&2, Dd>:
  match d:
    case True{}:
      Dd{V.sv.str(x, 1n), lw.strs(V.sv.at(x, 2n)), V.sv.at(x, 3n)} <> acc
    case False{}:
      acc

def lw.dds(xs: List<&2, X.Sx>) -> List<&2, Dd>:
  match xs:
    case +h <> t:
      lw.dds.if(F.fd.isdata(h), h, lw.dds(t))
    case Nil{}:
      Nil{}

def lw.dd.find(ds: List<&2, Dd>, +n: List<&2, U32>) -> Maybe<&2, Dd>:
  match ds:
    case Nil{}:
      None{}
    case Dd{+k, tvs, cs} <> t:
      Bool.pick(Maybe<&2, Dd>, S.eq(k, n), Some{Dd{k, tvs, cs}}, lw.dd.find(t, n))

# a name as GHCi reads it in the module's scope: M.f, or (M.<+>) for an
# operator
def lw.hsname(+m: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  F.fd.bpick(F.fd.name.lead(n), lw.cat3(m, [46], n), 40 <> lw.cat3(m, 46 <> n, [41]))

# A constructor at the instance: GHCi's name, Bend's, and its fields'
# types (an HyArgs spine)
type Ck is Data:
  Ck{hs: List<&2, U32>, bend: List<&2, U32>, fs: Hy}

# (con NAME (FIELD...) (ARGTYPE...) (ex NEX NTHETA)); one with
# existential variables or its own constraints has no inputs
def lw.ck.fs(ex: Bool, +le: Le, tys: X.Sx) -> Hy:
  match ex:
    case False{}:
      lw.hy(64n, le, HmChain{tys})
    case True{}:
      HyArgs{HyNo{S.b("existential")}, HyANil{}}

def lw.ck(+m: List<&2, U32>, +ty: List<&2, U32>, +le: Le, +c: X.Sx) -> Ck:
  +n = V.sv.str(c, 1n)
  +ex = V.sv.at(c, 4n)
  Ck{lw.hsname(m, n), F.fd.cname(ty, n), lw.ck.fs(Bool.not(Nat.is_eq(Nat.add(X.tsx.nat(V.sv.at(ex, 1n)), X.tsx.nat(V.sv.at(ex, 2n))), 0n)), le, V.sv.at(c, 3n))}

def lw.cks(+m: List<&2, U32>, +ty: List<&2, U32>, +le: Le, cs: X.Sx) -> List<&2, Ck>:
  match cs:
    case X.SxCons{+c, t}:
      lw.ck(m, ty, le, c) <> lw.cks(m, ty, le, t)
    case _:
      Nil{}

# a type's constructors at the arguments args
def lw.cks.of(found: Maybe<&2, Dd>, +le: Le, args: Hy) -> List<&2, Ck>:
  match found:
    case Some{Dd{+n, tvs, cs}}:
      lw.cks(lw.le.m(le), n, lw.le.with(le, lw.zip.sub(tvs, args)), cs)
    case None{}:
      Nil{}

def lw.nullary(cs: List<&2, Ck>) -> List<&2, Ck>:
  match cs:
    case Ck{hs, b, HyANil{}} <> t:
      Ck{hs, b, HyANil{}} <> lw.nullary(t)
    case _ <> t:
      lw.nullary(t)
    case Nil{}:
      Nil{}

# at depth 0 only the constructors with no fields
def lw.atd(d: Nat, cs: List<&2, Ck>) -> List<&2, Ck>:
  match d:
    case 0n:
      lw.nullary(cs)
    case 1n+p:
      cs

def lw.dec(d: Nat) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+p:
      p

# Values ---------------------------------------------------------------------

# An input or output: a constructor carries GHCi's name and Bend's; the
# arguments, a list's and a tuple's elements are a VaArgs spine.
type Va is Data:
  VaNat{n: Nat}
  VaInt{neg: Bool, n: Nat}
  VaChar{c: Nat}
  VaCon{hs: List<&2, U32>, bend: List<&2, U32>, args: Va}
  VaList{xs: Va}
  VaTup{xs: Va}
  VaArgs{a: Va, rest: Va}
  VaANil{}

def lw.spine(xs: List<&2, Va>) -> Va:
  match xs:
    case h <> t:
      VaArgs{h, lw.spine(t)}
    case Nil{}:
      VaANil{}

def lw.l(xs: List<&2, Va>) -> Va:
  VaList{lw.spine(xs)}

def lw.c0(hs: String, b: String) -> Va:
  VaCon{S.b(hs), S.b(b), VaANil{}}

def lw.nats() -> List<&2, Va>:
  [VaNat{0n}, VaNat{1n}, VaNat{2n}, VaNat{3n}]

def lw.ints() -> List<&2, Va>:
  [VaInt{False{}, 0n}, VaInt{False{}, 1n}, VaInt{True{}, 1n}, VaInt{False{}, 2n}, VaInt{True{}, 3n}]

def lw.bools() -> List<&2, Va>:
  [lw.c0("LawP.False", "False"), lw.c0("LawP.True", "True")]

def lw.chars() -> List<&2, Va>:
  [VaChar{97n}, VaChar{98n}, VaChar{32n}]

def lw.cmps() -> List<&2, Va>:
  [lw.c0("LawP.LT", "LT"), lw.c0("LawP.EQ", "EQ"), lw.c0("LawP.GT", "GT")]

def lw.units() -> List<&2, Va>:
  [lw.c0("()", "Unit")]

def lw.wrap1(+hs: List<&2, U32>, +b: List<&2, U32>, xs: List<&2, Va>) -> List<&2, Va>:
  match xs:
    case h <> t:
      VaCon{hs, b, VaArgs{h, VaANil{}}} <> lw.wrap1(hs, b, t)
    case Nil{}:
      Nil{}

def lw.maybes(xs: List<&2, Va>) -> List<&2, Va>:
  lw.c0("LawP.Nothing", "None") <> lw.wrap1(S.b("LawP.Just"), S.b("Some"), List.take(&2, Va, xs, 2n))

def lw.inter(xs: List<&2, Va>, ys: List<&2, Va>) -> List<&2, Va>:
  match xs ys:
    case h <> t k <> u:
      h <> k <> lw.inter(t, u)
    case Nil{} r:
      r
    case r Nil{}:
      r

def lw.eithers(xs: List<&2, Va>, ys: List<&2, Va>) -> List<&2, Va>:
  lw.inter(lw.wrap1(S.b("LawP.Left"), S.b("Inl"), List.take(&2, Va, xs, 2n)), lw.wrap1(S.b("LawP.Right"), S.b("Inr"), List.take(&2, Va, ys, 2n)))

# lists of the element values e, shortest first
def lw.lists(e: List<&2, Va>) -> List<&2, Va>:
  match e:
    case +a <> +b <> +c <> t:
      [lw.l(Nil{}), lw.l([a]), lw.l([b]), lw.l([c]), lw.l([a, b]), lw.l([b, a]), lw.l([a, b, c]), lw.l([c, a, b])]
    case +a <> +b <> t:
      [lw.l(Nil{}), lw.l([a]), lw.l([b]), lw.l([a, b]), lw.l([b, a])]
    case +a <> t:
      [lw.l(Nil{}), lw.l([a]), lw.l([a, a])]
    case Nil{}:
      [lw.l(Nil{})]

# x in front of the tuple m holds
def lw.cell(x: Va, m: Maybe<&2, Va>) -> List<&2, Va>:
  match m:
    case Some{VaTup{s}}:
      [VaTup{VaArgs{x, s}}]
    case _:
      Nil{}

# the pairs whose places sum to j: xs's i-th with ys's (j - i)-th
def lw.row(xs: List<&2, Va>, +ys: List<&2, Va>, j: Nat) -> List<&2, Va>:
  match xs j:
    case Nil{} _:
      Nil{}
    case x <> t 0n:
      lw.cell(x, List.get(&2, Va, ys, 0n))
    case x <> t 1n+(+q):
      List.append(&2, Va, lw.cell(x, List.get(&2, Va, ys, 1n+q)), lw.row(t, ys, q))

def lw.rows(k: Nat, +xs: List<&2, Va>, +ys: List<&2, Va>, +s: Nat) -> List<&2, Va>:
  match k:
    case 0n:
      Nil{}
    case 1n+q:
      List.append(&2, Va, lw.row(xs, ys, s), lw.rows(q, xs, ys, 1n+s))

# every x of xs in front of every tuple of ys, by the sum of their places
def lw.diag(+xs: List<&2, Va>, +ys: List<&2, Va>) -> List<&2, Va>:
  List.take(&2, Va, lw.rows(Nat.add(List.length(&2, Va, xs), List.length(&2, Va, ys)), xs, ys, 0n), 8n)

def lw.mk(hs: List<&2, U32>, b: List<&2, U32>, m: Maybe<&2, Va>) -> List<&2, Va>:
  match m:
    case Some{VaTup{s}}:
      [VaCon{hs, b, s}]
    case _:
      Nil{}

# what to list: a type's values, the tuples of a spine of field types, or
# the k-th tuple of each constructor's fields
type Q is Data:
  QTy{h: Hy}
  QFields{fs: Hy}
  QCons{k: Nat, cs: List<&2, Ck>}

# the inputs of a type, smallest first; d: how many of the module's own
# types deep (at 0, only their constructors with no fields)
def lw.vals(fuel: Nat, +d: Nat, +le: Le, +dds: List<&2, Dd>, q: Q) -> List<&2, Va>:
  match fuel q:
    case 0n _:
      Nil{}
    case 1n+p QTy{HyNat{s}}:
      lw.nats()
    case 1n+p QTy{HyInt{s}}:
      lw.ints()
    case 1n+p QTy{HyBool{}}:
      lw.bools()
    case 1n+p QTy{HyChar{}}:
      lw.chars()
    case 1n+p QTy{HyUnit{}}:
      lw.units()
    case 1n+p QTy{HyCmp{}}:
      lw.cmps()
    case 1n+p QTy{HyList{a}}:
      lw.lists(lw.vals(p, d, le, dds, QTy{a}))
    case 1n+p QTy{HyMaybe{a}}:
      lw.maybes(lw.vals(p, d, le, dds, QTy{a}))
    case 1n+(+p) QTy{HyEither{a, b}}:
      lw.eithers(lw.vals(p, d, le, dds, QTy{a}), lw.vals(p, d, le, dds, QTy{b}))
    case 1n+p QTy{HyT2{a, b}}:
      lw.vals(p, d, le, dds, QFields{HyArgs{a, HyArgs{b, HyANil{}}}})
    case 1n+p QTy{HyT3{a, b, c}}:
      lw.vals(p, d, le, dds, QFields{HyArgs{a, HyArgs{b, HyArgs{c, HyANil{}}}}})
    case 1n+(+p) QTy{HyUser{+n, args}}:
      +cs = lw.atd(d, lw.cks.of(lw.dd.find(dds, n), le, args))
      List.take(&2, Va, List.append(&2, Va, lw.vals(p, lw.dec(d), le, dds, QCons{0n, cs}), lw.vals(p, lw.dec(d), le, dds, QCons{1n, cs})), 6n)
    case 1n+p QTy{_}:
      Nil{}
    case 1n+(+p) QFields{HyArgs{h, r}}:
      lw.diag(lw.vals(p, d, le, dds, QTy{h}), lw.vals(p, d, le, dds, QFields{r}))
    case 1n+p QFields{_}:
      [VaTup{VaANil{}}]
    case 1n+(+p) QCons{+k, Ck{hs, b, fs} <> t}:
      List.append(&2, Va, lw.mk(hs, b, List.get(&2, Va, lw.vals(p, d, le, dds, QFields{fs}), k)), lw.vals(p, d, le, dds, QCons{k, t}))
    case 1n+p QCons{k, Nil{}}:
      Nil{}

# how a value is printed: itself, or a spine's elements
type Vm is Data:
  VmVal{}
  VmSp{}
  VmComma{}
  VmList{}
  VmTup{}

# a value as GHCi reads it
# an integer input as GHCi reads it: -n in parentheses
def lw.va.int(neg: Bool, n: Nat) -> List<&2, U32>:
  match neg:
    case True{}:
      40 <> 45 <> lw.cat(lw.nshow(n), [41])
    case False{}:
      lw.nshow(n)

def lw.va.hs(v: Va, mode: Vm) -> List<&2, U32>:
  match v mode:
    case VaNat{n} _:
      lw.nshow(n)
    case VaInt{neg, n} _:
      lw.va.int(neg, n)
    case VaChar{c} _:
      [39, U32.from_nat(c), 39]
    case VaCon{hs, b, VaANil{}} _:
      hs
    case VaCon{hs, b, args} _:
      40 <> lw.cat3(hs, lw.va.hs(args, VmSp{}), [41])
    case VaList{xs} _:
      91 <> lw.cat(lw.tail1(lw.va.hs(xs, VmComma{})), [93])
    case VaTup{xs} _:
      40 <> lw.cat(lw.tail1(lw.va.hs(xs, VmComma{})), [41])
    case VaArgs{a, r} VmSp{}:
      32 <> lw.cat(lw.va.hs(a, VmVal{}), lw.va.hs(r, VmSp{}))
    case VaArgs{a, r} _:
      44 <> lw.cat(lw.va.hs(a, VmVal{}), lw.va.hs(r, VmComma{}))
    case _ _:
      Nil{}

# a value in Bend: a list is Con/Nil, a tuple Tuple (three nest to the
# right), unit Unit
def lw.va.bt(v: Va, mode: Vm) -> T.Bt:
  match v mode:
    case VaNat{n} _:
      T.BtNat{lw.nshow(n)}
    case VaInt{+neg, n} _:
      T.BtCon{F.fd.bpick(neg, S.b("HsPrelude.HsInt.Neg"), S.b("HsPrelude.HsInt.Pos")), T.tba.args([T.BtNat{lw.nshow(n)}])}
    case VaChar{c} _:
      F.fd.char(c)
    case VaCon{hs, b, args} _:
      T.BtCon{b, lw.va.bt(args, VmSp{})}
    case VaList{xs} _:
      lw.va.bt(xs, VmList{})
    case VaTup{xs} _:
      lw.va.bt(xs, VmTup{})
    case VaArgs{a, r} VmSp{}:
      T.BtArgs{lw.va.bt(a, VmVal{}), lw.va.bt(r, VmSp{})}
    case VaArgs{a, r} VmList{}:
      T.BtCon{S.b("Con"), T.BtArgs{lw.va.bt(a, VmVal{}), T.BtArgs{lw.va.bt(r, VmList{}), T.BtANil{}}}}
    case VaArgs{a, VaANil{}} VmTup{}:
      lw.va.bt(a, VmVal{})
    case VaArgs{a, r} VmTup{}:
      T.BtCon{S.b("Tuple"), T.BtArgs{lw.va.bt(a, VmVal{}), T.BtArgs{lw.va.bt(r, VmTup{}), T.BtANil{}}}}
    case VaANil{} VmList{}:
      F.fd.con0("Nil")
    case VaANil{} VmTup{}:
      F.fd.con0("Unit")
    case _ _:
      T.BtANil{}

# GHC's answers ----------------------------------------------------------------

# what an answer tree is: (nat N) (neg N) (char N) (list ..) (tuple ..) (con "C" ..)
type Ok is Data:
  OkNat{}
  OkNeg{}
  OkChar{}
  OkList{}
  OkTup{}
  OkCon{}
  OkNo{}

def lw.okind(+x: X.Sx) -> Ok:
  +h = V.sv.hd(x)
  Bool.pick(Ok, V.sv.is(h, "nat"), OkNat{}, Bool.pick(Ok, V.sv.is(h, "neg"), OkNeg{}, Bool.pick(Ok, V.sv.is(h, "char"), OkChar{}, Bool.pick(Ok, V.sv.is(h, "list"), OkList{}, Bool.pick(Ok, V.sv.is(h, "tuple"), OkTup{}, Bool.pick(Ok, V.sv.is(h, "con"), OkCon{}, OkNo{}))))))

# a number answer: an HsInt where the def's result type has one (Spec's
# Int), else a Nat (a negative one has none: the fold's Int is Nat)
def lw.out.num(sg: Bool, neg: Bool, +n: List<&2, U32>) -> T.Bt:
  match sg neg:
    case True{} _:
      T.BtCon{F.fd.bpick(neg, S.b("HsPrelude.HsInt.Neg"), S.b("HsPrelude.HsInt.Pos")), T.tba.args([T.BtNat{n}])}
    case False{} False{}:
      T.BtNat{n}
    case False{} True{}:
      T.BtTodo{S.b("law:negative-answer")}

# an answer in Bend; a negative number has none (the fold's Int is Nat).
# It recurses on the tree's own parts (a string's answer is as long as the
# string)
def lw.out(x: X.Sx, k: Ok, mode: Vm, +sg: Bool) -> T.Bt:
  match x k mode:
    case X.SxCons{+h, t} _ VmSp{}:
      T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, sg), lw.out(t, OkNo{}, VmSp{}, sg)}
    case _ _ VmSp{}:
      T.BtANil{}
    case X.SxCons{+h, t} _ VmList{}:
      T.BtCon{S.b("Con"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, sg), T.BtArgs{lw.out(t, OkNo{}, VmList{}, sg), T.BtANil{}}}}
    case _ _ VmList{}:
      F.fd.con0("Nil")
    case X.SxCons{+h, X.SxNil{}} _ VmTup{}:
      lw.out(h, lw.okind(h), VmVal{}, sg)
    case X.SxCons{+h, t} _ VmTup{}:
      T.BtCon{S.b("Tuple"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, sg), T.BtArgs{lw.out(t, OkNo{}, VmTup{}, sg), T.BtANil{}}}}
    case _ _ VmTup{}:
      F.fd.con0("Unit")
    case +y OkNat{} _:
      lw.out.num(sg, False{}, X.tsx.atom.of(X.tsx.at(1n, y)))
    case +y OkNeg{} _:
      lw.out.num(sg, True{}, X.tsx.atom.of(X.tsx.at(1n, y)))
    case +y OkChar{} _:
      F.fd.char(X.tsx.nat(X.tsx.at(1n, y)))
    case X.SxCons{h, t} OkList{} _:
      lw.out(t, OkNo{}, VmList{}, sg)
    case X.SxCons{h, t} OkTup{} _:
      lw.out(t, OkNo{}, VmTup{}, sg)
    case X.SxCons{h, X.SxCons{c, t}} OkCon{} _:
      T.BtCon{X.tsx.str.of(c), lw.out(t, OkNo{}, VmSp{}, sg)}
    case _ _ _:
      T.BtTodo{S.b("law:answer")}

# One line GHCi printed: @law NAME K ok|err|timeout [ANSWER]
type Ol is Data:
  Ol{b: List<&2, U32>, k: List<&2, U32>, st: List<&2, U32>, v: List<&2, U32>}

def lw.ol.of(ws: List<&2, List<&2, U32>>) -> List<&2, Ol>:
  match ws:
    case at <> b <> k <> st <> rest:
      Bool.pick(List<&2, Ol>, V.sv.is(at, "@law"), [Ol{b, k, st, S.join(rest, 32)}], Nil{})
    case _:
      Nil{}

def lw.ols(ls: List<&2, List<&2, U32>>) -> List<&2, Ol>:
  match ls:
    case +l <> t:
      List.append(&2, Ol, lw.ol.of(S.split(l, 32)), lw.ols(t))
    case Nil{}:
      Nil{}

def lw.ol.find(os: List<&2, Ol>, +b: List<&2, U32>, +k: List<&2, U32>) -> Maybe<&2, Ol>:
  match os:
    case Nil{}:
      None{}
    case Ol{+ob, +ok, st, v} <> t:
      Bool.pick(Maybe<&2, Ol>, Bool.and(S.eq(ob, b), S.eq(ok, k)), Some{Ol{ob, ok, st, v}}, lw.ol.find(t, b, k))

# Plans: what each def's laws are ------------------------------------------------

# One law: its number, the call GHCi evaluates, the call in Bend
type Lc is Data:
  Lc{k: Nat, hs: List<&2, U32>, call: T.Bt}

# A def's laws (its name, the result type in Bend), or why it has none
type Pl is Data:
  Pl{b: List<&2, U32>, ret: T.Bt, ls: List<&2, Lc>}
  PlNo{b: List<&2, U32>, why: List<&2, U32>}

# a parameter's term in a law's call when it is no value: a type (Data) is
# Nat, a dictionary (Fold's fd.dc: eq_A, cmp_A) Nat's == or compare; and
# whether it is a template
type La is Data:
  La{t: Bool, d: T.Bt}

def lw.dterm(k: Nat) -> T.Bt:
  match k:
    case 0n:
      F.fd.ty0("Nat")
    case 1n:
      F.fd.v("Nat.is_eq")
    case _:
      F.fd.v("Nat.cmp")

# a parameter of the def: a type (Data), passed Nat, or a dictionary; else
# a value
def lw.kinds(ps: List<&2, T.BParam>) -> List<&2, Bool>:
  match ps:
    case T.BParam{m, x, T.BtVar{k}} <> t:
      S.eq(k, S.b("Data")) <> lw.kinds(t)
    case p <> t:
      Nat.is_gt(K.bk.dc.isdict(p), 0n) <> lw.kinds(t)
    case Nil{}:
      Nil{}

def lw.tpls(ps: List<&2, T.BParam>) -> List<&2, La>:
  match ps:
    case T.BParam{T.BmTpl{}, +x, +ty} <> t:
      La{True{}, lw.dterm(K.bk.dc.isdict(T.BParam{T.BmTpl{}, x, ty}))} <> lw.tpls(t)
    case _ <> t:
      La{False{}, F.fd.ty0("Nat")} <> lw.tpls(t)
    case Nil{}:
      Nil{}

def lw.nvals(ks: List<&2, Bool>) -> Nat:
  match ks:
    case True{} <> t:
      lw.nvals(t)
    case False{} <> t:
      1n+lw.nvals(t)
    case Nil{}:
      0n

def lw.wrap(t: Bool, b: T.Bt) -> T.Bt:
  match t:
    case True{}:
      T.BtTplArg{b}
    case False{}:
      b

# the def's arguments: Nat at each type parameter, the inputs in order at
# the others (a template parameter is passed as one)
def lw.bargs(ks: List<&2, Bool>, ts: List<&2, La>, vs: Va) -> List<&2, T.Bt>:
  match ks ts vs:
    case True{} <> k2 La{t, d} <> t2 _:
      lw.wrap(t, d) <> lw.bargs(k2, t2, vs)
    case False{} <> k2 La{t, d} <> t2 VaArgs{v, r}:
      lw.wrap(t, lw.va.bt(v, VmVal{})) <> lw.bargs(k2, t2, r)
    case _ _ _:
      Nil{}

def lw.vdrop(n: Nat, vs: Va) -> Va:
  match n vs:
    case 0n _:
      vs
    case 1n+p VaArgs{a, r}:
      lw.vdrop(p, r)
    case _ _:
      VaANil{}

# the inputs the def's parameters do not take, applied one by one to what
# it returns (a def written point-free returns a function)
def lw.apply(vs: Va, c: T.Bt) -> T.Bt:
  match vs:
    case VaArgs{v, r}:
      lw.apply(r, T.tba.call(c, [lw.va.bt(v, VmVal{})]))
    case _:
      c

def lw.bcall(+b: List<&2, U32>, +ks: List<&2, Bool>, ts: List<&2, La>, +vs: Va) -> T.Bt:
  lw.apply(lw.vdrop(lw.nvals(ks), vs), T.tba.call(T.BtVar{b}, lw.bargs(ks, ts, vs)))

def lw.lcs(ins: List<&2, Va>, +k: Nat, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, La>) -> List<&2, Lc>:
  match ins:
    case VaTup{+s} <> t:
      Lc{k, lw.cat(f, lw.va.hs(s, VmSp{})), lw.bcall(b, ks, ts, s)} <> lw.lcs(t, 1n+k, b, f, ks, ts)
    case _ <> t:
      lw.lcs(t, k, b, f, ks, ts)
    case Nil{}:
      Nil{}

def lw.plan.ins(ins: List<&2, Va>, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, La>, ret: T.Bt) -> Pl:
  match ins:
    case Nil{}:
      PlNo{b, S.b("nolaw:no-input")}
    case +h <> t:
      Pl{b, ret, lw.lcs(h <> t, 1n, b, f, ks, ts)}

# why the def has no laws, before any input: empty when it may have them
def lw.plan.why(+h: Hy, +ks: List<&2, Bool>) -> List<&2, U32>:
  +nt = lw.notype(lw.args(h))
  +nr = lw.notype(lw.res(h))
  lw.first(lw.first(F.fd.bpick(List.is_empty(&2, U32, nt), Nil{}, lw.cat(S.b("nolaw:argument-"), nt)), F.fd.bpick(List.is_empty(&2, U32, nr), Nil{}, lw.cat(S.b("nolaw:result-"), nr))), F.fd.bpick(Nat.is_gt(lw.nvals(ks), lw.nargs(lw.args(h))), S.b("nolaw:arity"), Nil{}))

# a partial def (Fold's fd.pt: its answer an Either, Inl{GHC's error}): its
# GHCi line wraps the call in LawEw, which answers GHC's ErrorCall as Inl
# (and its ArithException, as shown: "divide by zero", HsNum's message)
def lw.pt.open(pt: Bool) -> List<&2, U32>:
  F.fd.bpick(pt, S.b("(LawEw LawP.$ ("), S.b("(("))

def lw.pt.ret(pt: Bool, +r: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, pt, F.fd.pt.ety(r), r)

def lw.kept.pt(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case T.BiDef{k, ps, r, b, d} <> t:
      Bool.or(Bool.and(S.eq(k, n), S.mem(S.b(F.fd.pt.doc()), d)), lw.kept.pt(t, n))
    case _ <> t:
      lw.kept.pt(t, n)
    case Nil{}:
      False{}

def lw.plan.of(why: List<&2, U32>, +b: List<&2, U32>, +h: Hy, +m: List<&2, U32>, +hsn: List<&2, U32>, +le: Le, +dds: List<&2, Dd>, +ps: List<&2, T.BParam>, +pt: Bool) -> Pl:
  match why:
    case Nil{}:
      +f = lw.cat3(lw.pt.open(pt), lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41]))
      lw.plan.ins(List.take(&2, Va, lw.vals(40n, 2n, le, dds, QFields{lw.args(h)}), 8n), b, f, lw.kinds(ps), lw.tpls(ps), lw.pt.ret(pt, lw.bty(lw.res(h))))
    case w:
      PlNo{b, w}

# the def the gate kept named n: its parameters
def lw.kept(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Maybe<&2, List<&2, T.BParam>>:
  match its:
    case T.BiDef{k, ps, r, b, d} <> t:
      Bool.pick(Maybe<&2, List<&2, T.BParam>>, S.eq(k, n), Some{ps}, lw.kept(t, n))
    case _ <> t:
      lw.kept(t, n)
    case Nil{}:
      None{}

# (fun VAR TYPE SPAN MATCHES): the def's plan, if the gate kept it
def lw.plan.tb(found: Maybe<&2, List<&2, T.BParam>>, +n: List<&2, U32>, +f: X.Sx, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>, pt: Bool) -> List<&2, Pl>:
  match found:
    case Some{+ps}:
      +h = lw.ty(le, V.sv.at(f, 2n))
      [lw.plan.of(lw.plan.why(h, lw.kinds(ps)), F.fd.vname(n), h, m, n, le, dds, ps, pt)]
    case None{}:
      Nil{}

def lw.plans(tbs: List<&2, F.Tb>, +its: List<&2, T.BItem>, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>) -> List<&2, Pl>:
  match tbs:
    case F.TbFun{+n, tvs, +f} <> t:
      List.append(&2, Pl, lw.plan.tb(lw.kept(its, F.fd.vname(n)), n, f, le, dds, m, lw.kept.pt(its, F.fd.vname(n))), lw.plans(t, its, le, dds, m))
    case _ <> t:
      lw.plans(t, its, le, dds, m)
    case Nil{}:
      Nil{}

def lw.any.pl(ps: List<&2, Pl>) -> Bool:
  match ps:
    case Pl{b, r, ls} <> t:
      True{}
    case _ <> t:
      lw.any.pl(t)
    case Nil{}:
      False{}

# The GHCi script ------------------------------------------------------------------

# Everything the script names is qualified (LawP is the Prelude), so a
# module that defines its own Maybe, or hides the Prelude's, changes
# nothing here.  Each answer is printed with lawSx; lawRun gives each call
# 2 s and turns an exception (error, a failed pattern) into `err`.
def lw.ghci.pre() -> String:
  ":set -XScopedTypeVariables -XFlexibleInstances -XFlexibleContexts\nimport qualified Prelude as LawP\nimport qualified System.Timeout as LawT\nimport qualified Control.Exception as LawE\nimport qualified System.IO as LawIO\nimport qualified Numeric.Natural as LawN\nimport qualified System.IO.Unsafe as LawU\n:{\nclass LawSx a where\n  lawSx :: a -> LawP.String\n:}\n:{\nlawI :: LawP.Integer -> LawP.String\nlawI n = if n LawP.< 0 then \"(neg \" LawP.++ LawP.show (LawP.negate n) LawP.++ \")\" else \"(nat \" LawP.++ LawP.show n LawP.++ \")\"\n:}\n:{\nlawC :: LawP.String -> [LawP.String] -> LawP.String\nlawC c xs = \"(con \\\"\" LawP.++ c LawP.++ \"\\\"\" LawP.++ LawP.concatMap (\\x -> ' ' : x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx LawP.Int where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Integer where\n  lawSx n = lawI n\n:}\n:{\ninstance LawSx LawN.Natural where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Bool where\n  lawSx b = if b then lawC \"True\" [] else lawC \"False\" []\n:}\n:{\ninstance LawSx LawP.Char where\n  lawSx c = \"(char \" LawP.++ LawP.show (LawP.fromEnum c) LawP.++ \")\"\n:}\n:{\ninstance LawSx () where\n  lawSx _ = lawC \"Unit\" []\n:}\n:{\ninstance LawSx LawP.Ordering where\n  lawSx o = case o of { LawP.LT -> lawC \"LT\" []; LawP.EQ -> lawC \"EQ\" []; LawP.GT -> lawC \"GT\" [] }\n:}\n:{\ninstance LawSx a => LawSx [a] where\n  lawSx xs = \"(list\" LawP.++ LawP.concatMap (\\x -> ' ' : lawSx x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx a => LawSx (LawP.Maybe a) where\n  lawSx m = case m of { LawP.Nothing -> lawC \"None\" []; LawP.Just x -> lawC \"Some\" [lawSx x] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (LawP.Either a b) where\n  lawSx e = case e of { LawP.Left x -> lawC \"Inl\" [lawSx x]; LawP.Right y -> lawC \"Inr\" [lawSx y] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (a, b) where\n  lawSx (a, b) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \")\"\n:}\n:{\ninstance (LawSx a, LawSx b, LawSx c) => LawSx (a, b, c) where\n  lawSx (a, b, c) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \" \" LawP.++ lawSx c LawP.++ \")\"\n:}\n:{\nlawRun :: LawSx b => LawP.String -> LawP.Int -> b -> LawP.IO ()\nlawRun n k v = do\n  r <- LawE.try (LawT.timeout 2000000 (let s = lawSx v in LawE.evaluate (LawP.length s) LawP.>> LawP.return s))\n  case r of\n    LawP.Left (e :: LawE.SomeException) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" err\")\n    LawP.Right LawP.Nothing -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" timeout\")\n    LawP.Right (LawP.Just s) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" ok \" LawP.++ s)\n  LawIO.hFlush LawIO.stdout\n:}\n:{\nnewtype LawEw a = LawEw a\n:}\n:{\ninstance LawSx a => LawSx (LawEw a) where\n  lawSx (LawEw v) = LawU.unsafePerformIO (LawE.try (let s = lawSx v in LawE.evaluate (LawP.length s) LawP.>> LawP.return s) LawP.>>= \\r -> case r of { LawP.Left (e :: LawE.SomeException) -> case LawE.fromException e of { LawP.Just (LawE.ErrorCall m) -> LawP.return (lawC \"Inl\" [lawSx m]); LawP.Nothing -> case LawE.fromException e of { LawP.Just (a :: LawE.ArithException) -> LawP.return (lawC \"Inl\" [lawSx (LawP.show a)]); LawP.Nothing -> LawE.throwIO e } }; LawP.Right s -> LawP.return (lawC \"Inr\" [s]) })\n:}\n"

# x0 x1 ..: a constructor's fields in a pattern
def lw.vars(n: Nat, +i: Nat) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (120 <> lw.nshow(i)) <> lw.vars(p, 1n+i)

def lw.sxs(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case x <> t:
      lw.cat(S.b("lawSx "), x) <> lw.sxs(t)
    case Nil{}:
      Nil{}

def lw.ctxs(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case x <> t:
      lw.cat(S.b("LawSx "), x) <> lw.ctxs(t)
    case Nil{}:
      Nil{}

# one case of lawSx: M.C x0 x1 -> lawC "T.C" [lawSx x0, lawSx x1]
def lw.alt(+m: List<&2, U32>, +ty: List<&2, U32>, +c: X.Sx) -> List<&2, U32>:
  +n = V.sv.str(c, 1n)
  +vs = lw.vars(X.tsx.len(V.sv.at(c, 3n)), 0n)
  lw.cat3(S.b("    "), lw.hsname(m, n), lw.cat3(S.join(S.b("") <> vs, 32), S.b(" -> lawC \""), lw.cat3(F.fd.cname(ty, n), S.b("\" ["), lw.cat(S.join(lw.sxs(vs), 44), S.b("]\n")))))

def lw.alts(+m: List<&2, U32>, +ty: List<&2, U32>, cs: X.Sx) -> List<&2, U32>:
  match cs:
    case X.SxCons{+c, t}:
      lw.cat(lw.alt(m, ty, c), lw.alts(m, ty, t))
    case _:
      Nil{}

def lw.ctx(tvs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match tvs:
    case Nil{}:
      Nil{}
    case +h <> t:
      40 <> lw.cat(S.join(lw.ctxs(h <> t), 44), S.b(") => "))

# lawSx for one of the module's data types
def lw.inst(+m: List<&2, U32>, d: Dd) -> List<&2, U32>:
  match d:
    case Dd{+n, +tvs, cs}:
      lw.cat3(S.b("instance "), lw.ctx(tvs), lw.cat3(S.b("LawSx ("), lw.cat3(m, 46 <> n, S.join(S.b("") <> tvs, 32)), lw.cat(S.b(") where\n  lawSx v = case v of\n"), lw.alts(m, n, cs))))

# the instances in one block (types that use each other, in any order),
# then each in its own block twice (so one GHCi refuses, a type with a
# function field say, costs only its own laws; the second round sees the
# first's; GHCi lets an instance shadow the same one declared before)
def lw.insts.one(+m: List<&2, U32>, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case d <> t:
      lw.cat(lw.inst(m, d), lw.insts.one(m, t))
    case Nil{}:
      Nil{}

def lw.insts.each(+m: List<&2, U32>, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case d <> t:
      lw.cat3(S.b(":{\n"), lw.inst(m, d), lw.cat(S.b(":}\n"), lw.insts.each(m, t)))
    case Nil{}:
      Nil{}

def lw.insts(+m: List<&2, U32>, +ds: List<&2, Dd>) -> List<&2, U32>:
  lw.cat3(lw.cat3(S.b(":{\n"), lw.insts.one(m, ds), S.b(":}\n")), lw.insts.each(m, ds), lw.insts.each(m, ds))

# lawRun "f" 3 ((M.f :: T) a b)
def lw.lines.lc(ls: List<&2, Lc>, +b: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Lc{k, hs, c} <> t:
      lw.cat3(S.b("lawRun \""), b, lw.cat3(S.b("\" "), lw.nshow(k), lw.cat3([32], hs, lw.cat(S.b(")\n"), lw.lines.lc(t, b)))))
    case Nil{}:
      Nil{}

def lw.lines(ps: List<&2, Pl>) -> List<&2, U32>:
  match ps:
    case Pl{+b, r, ls} <> t:
      lw.cat(lw.lines.lc(ls, b), lw.lines(t))
    case _ <> t:
      lw.lines(t)
    case Nil{}:
      Nil{}

# (the last line ends GHCi at once: a law out of time whose thread never
# allocates, `replace "" "" s`, is left running, and GHC's own exit waits
# for it, hs1003's 00632)
def lw.script(+m: List<&2, U32>, ds: List<&2, Dd>, ps: List<&2, Pl>) -> List<&2, U32>:
  lw.cat3(S.b(lw.ghci.pre()), lw.insts(m, ds), lw.cat(lw.lines(ps), S.b(":!kill -9 $PPID\n")))

# The laws ---------------------------------------------------------------------------

def lw.lawname(+b: List<&2, U32>, k: Nat) -> List<&2, U32>:
  lw.cat3(b, S.b(".ex"), lw.nshow(k))

# whether a module's export names HsInt (the specialiser's Int): its number
# answers are HsInts
def lw.has.str.go(x: X.Sx, +s: List<&2, U32>) -> Bool:
  match x:
    case X.SxStr{a}:
      S.eq(a, s)
    case X.SxCons{h, t}:
      Bool.or(lw.has.str.go(h, s), lw.has.str.go(t, s))
    case _:
      False{}

def lw.has.str(xs: List<&2, X.Sx>, +s: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(lw.has.str.go(x, s), lw.has.str(t, s))

# the law, once GHC's answer reads as a tree
def lw.law.sx(m: Maybe<&2, X.Sx>, +b: List<&2, U32>, +ret: T.Bt, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>, sg: Bool) -> List<&2, T.BItem>:
  match m:
    case Some{+x}:
      +doc = lw.cat3(S.b("GHC: "), hs, lw.cat(S.b(") = "), v))
      T.BiDef{lw.lawname(b, k), Nil{}, T.BtEq{ret, call, lw.out(x, lw.okind(x), VmVal{}, Bool.and(sg, Bool.not(S.mem(S.b("Nat"), T.tba.refs(ret, Nil{})))))}, T.BtExpr{T.BtRefl{}}, doc <> Nil{}} <> Nil{}
    case None{}:
      Nil{}

# whether a text has a number of five digits or more: Bend's checker
# overflows its stack expanding a Nat past about 10000 (10000n checks,
# 30000n does not), and then it names no def, so the whole module's laws
# would go; such a law is not written
def lw.digits(xs: List<&2, U32>) -> List<&2, Bool>:
  match xs:
    case +c <> t:
      Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)) <> lw.digits(t)
    case Nil{}:
      Nil{}

def lw.bigrun(ds: List<&2, Bool>, run: Nat) -> Bool:
  match ds run:
    case True{} <> t 4n:
      True{}
    case True{} <> t _:
      lw.bigrun(t, 1n+run)
    case False{} <> t _:
      lw.bigrun(t, 0n)
    case Nil{} _:
      False{}

def lw.bignum(+xs: List<&2, U32>) -> Bool:
  lw.bigrun(lw.digits(xs), 0n)

def lw.law.ok(ok: Bool, +b: List<&2, U32>, +ret: T.Bt, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>, sg: Bool) -> List<&2, T.BItem>:
  match ok:
    case True{}:
      lw.law.sx(X.tsx.one(v), b, ret, k, hs, call, v, sg)
    case False{}:
      Nil{}

def lw.law(o: Maybe<&2, Ol>, +b: List<&2, U32>, +ret: T.Bt, k: Nat, +hs: List<&2, U32>, call: T.Bt, sg: Bool) -> List<&2, T.BItem>:
  match o:
    case Some{Ol{ob, ok, +st, +v}}:
      lw.law.ok(Bool.and(V.sv.is(st, "ok"), Bool.not(Bool.or(lw.bignum(v), lw.bignum(hs)))), b, ret, k, hs, call, v, sg)
    case None{}:
      Nil{}

def lw.laws.lc(ls: List<&2, Lc>, +b: List<&2, U32>, +ret: T.Bt, +os: List<&2, Ol>, +sg: Bool) -> List<&2, T.BItem>:
  match ls:
    case Lc{+k, hs, c} <> t:
      List.append(&2, T.BItem, lw.law(lw.ol.find(os, b, lw.nshow(k)), b, ret, k, hs, c, sg), lw.laws.lc(t, b, ret, os, sg))
    case Nil{}:
      Nil{}

def lw.items(ps: List<&2, Pl>, +os: List<&2, Ol>, +sg: Bool) -> List<&2, T.BItem>:
  match ps:
    case Pl{+b, +r, ls} <> t:
      List.append(&2, T.BItem, lw.laws.lc(ls, b, r, os, sg), lw.items(t, os, sg))
    case _ <> t:
      lw.items(t, os, sg)
    case Nil{}:
      Nil{}

def lw.todos(+it: T.BItem) -> List<&2, List<&2, U32>>:
  T.tba.item.fold(~T.tba.todos, it, Nil{})

# the laws with an answer Bend can write, and the defs of the others (a
# negative answer: the fold's Int is Nat, so that def is wrong there)
def lw.good(its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case +h <> t:
      F.fd.without.put(Bool.not(List.is_empty(&2, List<&2, U32>, lw.todos(h))), h, lw.good(t))
    case Nil{}:
      Nil{}

def lw.bad.put(todos: List<&2, List<&2, U32>>, +n: List<&2, U32>, r: List<&2, F.Dr>) -> List<&2, F.Dr>:
  match todos:
    case w <> t:
      F.Dr{lw.undot(n), w} <> r
    case Nil{}:
      r

def lw.bad(its: List<&2, T.BItem>) -> List<&2, F.Dr>:
  match its:
    case +h <> t:
      lw.bad.put(lw.todos(h), F.fd.item.name(h), lw.bad(t))
    case Nil{}:
      Nil{}

# The gate, with the laws ------------------------------------------------------------

def lw.gs.its(+g: F.Gs) -> List<&2, T.BItem>:
  match g:
    case F.Gs{k, o, d}:
      k

def lw.gs.out(+g: F.Gs) -> List<&2, F.Dr>:
  match g:
    case F.Gs{k, o, d}:
      o

# a law the gate refuses takes out its def
# a def the fuel wrote (Fold.bend: NAME.fu, a group's NAME.mu and its
# types and projections): its own item, not a law or a lifted def
def lw.fuelname(+n: List<&2, U32>) -> Bool:
  Bool.or(S.infix(n, S.b(".mu")), S.suffix(n, S.b(".fu")))

def lw.who(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{+n}:
      Some{F.fd.bpick(Bool.or(lw.tydef(n), lw.fuelname(n)), n, lw.undot(n))}
    case None{}:
      None{}

def lw.whykind(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case Some{+n}:
      F.fd.bpick(Bool.and(lw.dotted(n), Bool.not(lw.tydef(n))), S.b("law:"), S.b("check:"))
    case None{}:
      S.b("check:")

# the names of the items that are not laws
def lw.defnames(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case +h <> t:
      +n = F.fd.item.name(h)
      +r = lw.defnames(t)
      F.fd.bpicks(Bool.and(lw.dotted(n), Bool.not(lw.tydef(n))), r, n <> r)
    case Nil{}:
      Nil{}

def lw.prune.go(its: List<&2, T.BItem>, +defs: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match its:
    case +h <> t:
      +n = F.fd.item.name(h)
      F.fd.without.put(Bool.and(lw.dotted(n), Bool.not(S.mem(lw.undot(n), defs))), h, lw.prune.go(t, defs))
    case Nil{}:
      Nil{}

# the laws whose def is gone go too (a law names its def only in its
# type, where the gate's closure, Fold's fd.hits, does not look)
def lw.prune(+its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  lw.prune.go(its, lw.defnames(its))

def lw.pruned(g: F.Gs) -> F.Gs:
  match g:
    case F.Gs{k, o, d}:
      F.Gs{lw.prune(k), o, d}

# The cache (bend/Cache.bend) -------------------------------------------------
#
# With CATA_CACHE=DIR every oracle's answer is kept in DIR under the digest
# of what the oracle read, and asked again only when no run asked it
# before.  bend's check of a module's file: bend's identity (its resolved
# path, a store path), the file's text, and the digests of the files it
# imports, each file's digest that of its own text and its imports' (the
# package's files are a DAG, and their digests a Merkle DAG: a file's
# digest names every byte bend reads for it but Base, which is bend's).
# GHC's answers: GHC's identity and words, the module's source path, the
# digest of the package's Haskell sources up to the module (modules.txt's
# order, so every module it imports), and the script.  An answer read back
# is the same bytes, so a cached run's outputs are an uncached run's
# (tests/cache/run.zsh compares every file).  Not kept: an answer that ran
# out of time (status 124 or 125, or a script's `timeout`), and a check
# whose answer names its file or a missing one.
#
# cc: the directory (empty: no cache) and bend's and GHC's identities (and
# back: CATA_BEND2HS is set, see lw.back); mk: the files the run wrote,
# with their digests; hs: the sources' digest.
type Cc is Data:
  Cc{dir: List<&2, U32>, bend: List<&2, U32>, ghc: List<&2, U32>, back: Bool}

type Mk is Data:
  Mk{a: List<&2, U32>, h: List<&2, U32>}

type Kc is Data:
  Kc{cc: Cc, mk: List<&2, Mk>, hs: List<&2, U32>}

def lw.kc0() -> Kc:
  Kc{Cc{Nil{}, Nil{}, Nil{}, False{}}, Nil{}, Nil{}}

def lw.kc.cc(+ck: Kc) -> Cc:
  match ck:
    case Kc{cc, mk, hs}:
      cc

def lw.kc.mk(+ck: Kc) -> List<&2, Mk>:
  match ck:
    case Kc{cc, mk, hs}:
      mk

def lw.kc.hs(+ck: Kc) -> List<&2, U32>:
  match ck:
    case Kc{cc, mk, hs}:
      hs

def lw.kc.with.mk(ck: Kc, mk2: List<&2, Mk>) -> Kc:
  match ck:
    case Kc{cc, mk, hs}:
      Kc{cc, mk2, hs}

def lw.kc.with.hs(ck: Kc, hs2: List<&2, U32>) -> Kc:
  match ck:
    case Kc{cc, mk, hs}:
      Kc{cc, mk, hs2}

def lw.cc.dir(+cc: Cc) -> List<&2, U32>:
  match cc:
    case Cc{d, b, g, k}:
      d

def lw.cc.bend(+cc: Cc) -> List<&2, U32>:
  match cc:
    case Cc{d, b, g, k}:
      b

def lw.cc.ghc(+cc: Cc) -> List<&2, U32>:
  match cc:
    case Cc{d, b, g, k}:
      g

def lw.cc.back(+cc: Cc) -> Bool:
  match cc:
    case Cc{d, b, g, k}:
      k

def lw.cc.with.back(cc: Cc, on: Bool) -> Cc:
  match cc:
    case Cc{d, b, g, k}:
      Cc{d, b, g, on}

def lw.kc.dir(+ck: Kc) -> List<&2, U32>:
  lw.cc.dir(lw.kc.cc(ck))

def lw.kc.back(+ck: Kc) -> Bool:
  match ck:
    case Kc{cc, mk, hs}:
      lw.cc.back(cc)

def lw.kc.with.back(ck: Kc, on: Bool) -> Kc:
  match ck:
    case Kc{cc, mk, hs}:
      Kc{lw.cc.with.back(cc, on), mk, hs}

def lw.kc.on(+ck: Kc) -> Bool:
  Bool.not(List.is_empty(&2, U32, lw.kc.dir(ck)))

# a text's first lines, up to its first line of code (not blank, not a
# comment, not an import) and that one too, latest first: where bend reads
# a file's imports (nl: the next byte ends the line; stop: the last line
# was code)
def lw.kc.code(+l: List<&2, U32>) -> Bool:
  Bool.not(Bool.or(List.is_empty(&2, U32, l), Bool.or(S.head.is(l, 35), S.prefix(l, S.b("import")))))

def lw.kc.head(xs: List<&2, U32>, line: List<&2, U32>, acc: List<&2, List<&2, U32>>, nl: Bool, stop: Bool) -> List<&2, List<&2, U32>>:
  match xs nl stop:
    case _ _ True{}:
      acc
    case Nil{} _ False{}:
      acc
    case c <> +t True{} False{}:
      +l = List.reverse(&2, U32, line)
      lw.kc.head(t, Nil{}, l <> acc, S.head.is(t, 10), lw.kc.code(l))
    case +c <> +t False{} False{}:
      lw.kc.head(t, c <> line, acc, S.head.is(t, 10), False{})

def lw.kc.cons(x: List<&2, U32>, r: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match r:
    case Some{xs}:
      Some{x <> xs}
    case None{}:
      None{}

# a line's import: `import ./X.bend as A` is X's, `import Base` none, any
# other import unknown (r is None: the text is not cached)
def lw.kc.imp.at(dot: Bool, base: Bool, imp: Bool, +l: List<&2, U32>, r: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match dot base imp:
    case True{} _ _:
      lw.kc.cons(S.until(S.strip(l, S.b("import ./")), 46), r)
    case False{} True{} _:
      r
    case False{} False{} True{}:
      None{}
    case False{} False{} False{}:
      r

def lw.kc.imps(ls: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match ls:
    case Nil{}:
      Some{Nil{}}
    case +l <> t:
      lw.kc.imp.at(S.prefix(l, S.b("import ./")), S.eq(l, S.b("import Base")), S.prefix(l, S.b("import")), l, lw.kc.imps(t))

def lw.mk.find(ms: List<&2, Mk>, +a: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      None{}
    case Mk{+x, h} <> t:
      Bool.pick(Maybe<&2, List<&2, U32>>, S.eq(x, a), Some{h}, lw.mk.find(t, a))

def lw.kc.digs.at(m: Maybe<&2, List<&2, U32>>, r: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{h}:
      lw.kc.cons(h, r)

# the digests of the files named, in their order (None: one is not known)
def lw.kc.digs(+ms: List<&2, Mk>, xs: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +x <> t:
      lw.kc.digs.at(lw.mk.find(ms, x), lw.kc.digs(ms, t))

def lw.kc.digs.of(+ms: List<&2, Mk>, m: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      lw.kc.digs(ms, xs)

# the digests of the files a text imports
def lw.kc.deps(+ms: List<&2, Mk>, +text: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  lw.kc.digs.of(ms, lw.kc.imps(lw.kc.head(text, Nil{}, Nil{}, S.head.is(text, 10), False{})))

# a file's digest: its text's and its imports'
def lw.kc.file.key(+text: List<&2, U32>, d: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, U32>>:
  match d:
    case None{}:
      None{}
    case Some{ds}:
      Some{C.ch.key(S.b("cata file 1") <> text <> ds)}

def lw.kc.mk.put(k: Maybe<&2, List<&2, U32>>, +a: List<&2, U32>, ms: List<&2, Mk>) -> List<&2, Mk>:
  match k:
    case None{}:
      ms
    case Some{h}:
      Mk{a, h} <> ms

# the files written, with one more (its alias and text)
def lw.kc.add(on: Bool, +ck: Kc, +a: List<&2, U32>, +text: List<&2, U32>) -> List<&2, Mk>:
  match on:
    case False{}:
      lw.kc.mk(ck)
    case True{}:
      lw.kc.mk.put(lw.kc.file.key(text, lw.kc.deps(lw.kc.mk(ck), text)), a, lw.kc.mk(ck))

def lw.kc.wrote(wrote: Bool, +ck: Kc, +a: List<&2, U32>, +text: List<&2, U32>) -> List<&2, Mk>:
  match wrote:
    case False{}:
      lw.kc.mk(ck)
    case True{}:
      lw.kc.add(lw.kc.on(ck), ck, a, text)

# an oracle's answer as a value (its status, a newline, its text) and back
def lw.kc.out.val(+o: S.Out) -> List<&2, U32>:
  List.append(&2, U32, S.b(U32.show(S.Out.status(o))), 10 <> S.Out.text(o))

def lw.kc.out.n(c: C.ChN) -> S.Out:
  match c:
    case C.ChN{n, rest}:
      S.Out{U32.from_nat(n), rest}

def lw.kc.out.of(+v: List<&2, U32>) -> S.Out:
  lw.kc.out.n(C.ch.split.num(v))

def lw.kc.put(keep: Bool, +dir: String, +key: List<&2, U32>, +o: S.Out) -> IO(Unit):
  match keep:
    case True{}:
      C.ch.put(dir, key, lw.kc.out.val(o))
    case False{}:
      IO.pure(Unit, Unit{})

# bend's check of a text (None: not cached)
def lw.kc.bkey.of(+b: List<&2, U32>, +text: List<&2, U32>, d: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, U32>>:
  match d:
    case None{}:
      None{}
    case Some{ds}:
      Some{C.ch.key(S.b("cata bend-check 1") <> b <> S.b("--check-only 300") <> text <> ds)}

def lw.kc.bkey.at(on: Bool, +ck: Kc, +text: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match on:
    case False{}:
      None{}
    case True{}:
      lw.kc.bkey.of(lw.cc.bend(lw.kc.cc(ck)), text, lw.kc.deps(lw.kc.mk(ck), text))

def lw.kc.bkey(+ck: Kc, +text: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  lw.kc.bkey.at(lw.kc.on(ck), ck, text)

def lw.kc.bend.keep(+o: S.Out, +path: String) -> Bool:
  +st = S.Out.status(o)
  +tx = S.Out.text(o)
  Bool.not(Bool.or(Bool.or(U32.is_eq(st, 124), U32.is_eq(st, 125)), Bool.or(S.infix(tx, S.b(S.base(path))), S.infix(tx, S.b("no such file")))))

def lw.kc.bend.run(+bend: String, +path: String) -> IO(S.Out):
  S.run(".", Nil{}, 300, bend, [path, "--check-only"], Nil{})

def lw.kc.bend.got(got: Maybe<&2, List<&2, U32>>, +dir: String, +key: List<&2, U32>, +bend: String, +path: String) -> IO(S.Out):
  match got:
    case Some{v}:
      IO.pure(S.Out, lw.kc.out.of(v))
    case None{}:
      do IO<S.Out>:
        +o : S.Out <- lw.kc.bend.run(bend, path)
        lw.kc.put(lw.kc.bend.keep(o, path), dir, key, o)
        return o

def lw.kc.bend.key(k: Maybe<&2, List<&2, U32>>, +dir: String, +bend: String, +path: String) -> IO(S.Out):
  match k:
    case None{}:
      lw.kc.bend.run(bend, path)
    case Some{+key}:
      do IO<S.Out>:
        got : Maybe<&2, List<&2, U32>> <- C.ch.get(dir, key)
        lw.kc.bend.got(got, dir, key, bend, path)

# bend's check of the file at path, whose text is text
def lw.kc.bend(+ck: Kc, +bend: String, +path: String, +text: List<&2, U32>) -> IO(S.Out):
  lw.kc.bend.key(lw.kc.bkey(ck, text), S.str(lw.kc.dir(ck)), bend, path)

# a round's check: bend's answer and the text it checked
type Io is Data:
  Io{out: S.Out, text: List<&2, U32>}

def lw.io.out(+r: Io) -> List<&2, U32>:
  match r:
    case Io{o, t}:
      S.Out.text(o)

def lw.io.text(+r: Io) -> List<&2, U32>:
  match r:
    case Io{o, t}:
      t

def lw.gate.io.text(+ck: Kc, +bend: String, +path: String, +text: List<&2, U32>) -> IO(Io):
  do IO<Io>:
    S.write(path, text)
    +o : S.Out <- lw.kc.bend(ck, bend, path, text)
    return Io{o, text}

# one round's check, Fold's fd.gate.io with the file rendered once (the
# round's step reads the same text) and bend's answer from the cache when
# it has it (nothing once done)
def lw.gate.io(+ck: Kc, g: F.Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>) -> IO(Io):
  match g:
    case F.Gs{its, o, True{}}:
      IO.pure(Io, Io{S.Out{0, S.b("ALL PROOFS CHECK")}, Nil{}})
    case F.Gs{its, o, False{}}:
      lw.gate.io.text(ck, bend, path, F.fd.render(file, m, ims, its))

# the gate's repair: fuel for a self-call Bend refuses (Fold.bend's
# fd.gate.fix), else the drop
def lw.gate.fix(can: Bool, +who: Maybe<&2, List<&2, U32>>, +its: List<&2, T.BItem>, o: List<&2, F.Dr>, +why: List<&2, U32>, +dt: List<&2, T.BItem>) -> F.Gs:
  match can:
    case True{}:
      F.Gs{F.fd.fu.swap(its, F.fd.fu.name(who), List.append(&2, T.BItem, its, dt)), o, False{}}
    case False{}:
      lw.pruned(F.fd.gate.drop(lw.who(who), its, o, lw.cat(lw.whykind(who), why)))

def lw.gate.step(g: F.Gs, +r: Io, +dt: List<&2, T.BItem>) -> F.Gs:
  match g:
    case F.Gs{its, o, True{}}:
      F.Gs{its, o, True{}}
    case F.Gs{+its, +o, False{}}:
      +out = lw.io.out(r)
      +ls = S.split(out, 10)
      +who = F.fd.gate.who2(F.fd.tpl.loc(ls), ls, lw.io.text(r), its)
      +why = F.fd.errwhy(ls)
      Bool.pick(F.Gs, S.prefix(out, S.b("ALL PROOFS CHECK")), F.Gs{its, o, True{}}, lw.gate.fix(F.fd.fu.can(who, why, its, dt), who, its, o, why, dt))

def lw.gate(fuel: Nat, g: F.Gs, +ck: Kc, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +dt: List<&2, T.BItem>) -> IO(F.Gs):
  match fuel:
    case 0n:
      IO.pure(F.Gs, g)
    case 1n+p:
      +g1 = g
      do IO<F.Gs>:
        +r : Io <- lw.gate.io(ck, g1, bend, path, file, m, ims)
        S.add(path ++ ".log", S.append(S.lines.take(lw.io.out(r), 12n), [10, 10]))
        lw.gate(p, lw.gate.step(g1, r, dt), ck, bend, path, file, m, ims, dt)

def lw.drop1(g: F.Gs, +n: List<&2, U32>, w: List<&2, U32>) -> F.Gs:
  match g:
    case F.Gs{k, o, d}:
      F.fd.gate.drop(Some{n}, k, o, w)

def lw.undone(g: F.Gs) -> F.Gs:
  match g:
    case F.Gs{k, o, d}:
      F.Gs{k, o, False{}}

def lw.done.if(done: Bool, g: F.Gs) -> F.Gs:
  match g:
    case F.Gs{k, o, d}:
      F.Gs{k, o, done}

# drop each def whose law has no Bend answer, with what uses it
def lw.drops(ds: List<&2, F.Dr>, g: F.Gs) -> F.Gs:
  match ds:
    case F.Dr{n, w} <> t:
      lw.drops(t, lw.drop1(g, n, w))
    case Nil{}:
      g

# The ledger ---------------------------------------------------------------------------

def lw.line(+file: List<&2, U32>, n: List<&2, U32>, st: String, w: List<&2, U32>) -> List<&2, U32>:
  lw.cat(S.join([file, n, S.b(st), w], 9), [10])

def lw.nlaws(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Nat:
  match its:
    case T.BiDef{+k, ps, r, b, d} <> t:
      Nat.add(Bool.pick(Nat, Bool.and(lw.dotted(k), Bool.and(S.eq(lw.undot(k), n), lw.islaw(k))), 1n, 0n), lw.nlaws(t, n))
    case _ <> t:
      lw.nlaws(t, n)
    case Nil{}:
      0n

# why a def that checks has no law
def lw.nowhy(ps: List<&2, Pl>, +n: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case PlNo{+b, w} <> t:
      F.fd.bpick(S.eq(b, n), w, lw.nowhy(t, n))
    case Pl{+b, r, ls} <> t:
      F.fd.bpick(S.eq(b, n), S.b("nolaw:no-answer"), lw.nowhy(t, n))
    case Nil{}:
      S.b("nolaw:unplanned")

def lw.ledger.def(isl: Bool, nl: Nat, +file: List<&2, U32>, n: List<&2, U32>, why: List<&2, U32>) -> List<&2, U32>:
  match isl nl:
    case True{} _:
      Nil{}
    case False{} 0n:
      lw.line(file, n, "ok-check", why)
    case False{} 1n+p:
      lw.line(file, n, "ok-law", lw.cat(S.b("laws:"), lw.nshow(1n+p)))

def lw.ledger.ok(its: List<&2, T.BItem>, +all: List<&2, T.BItem>, +file: List<&2, U32>, +ps: List<&2, Pl>, +fb: List<&2, U32>) -> List<&2, U32>:
  match its:
    case T.BiDef{+n, xs, r, b, d} <> t:
      lw.cat(lw.ledger.def(lw.dotted(n), lw.nlaws(all, n), file, n, lw.first(fb, lw.nowhy(ps, n))), lw.ledger.ok(t, all, file, ps, fb))
    case T.BiType{+n, xs, k, cs, d} <> t:
      lw.cat(F.fd.bpick(Bool.or(lw.fuelname(n), F.fd.isgen(d)), Nil{}, lw.line(file, n, "ok-type", Nil{})), lw.ledger.ok(t, all, file, ps, fb))
    case _ <> t:
      lw.ledger.ok(t, all, file, ps, fb)
    case Nil{}:
      Nil{}

def lw.ledger.out(ds: List<&2, F.Dr>, +file: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case F.Dr{+n, w} <> t:
      lw.cat(F.fd.bpick(lw.dotted(n), Nil{}, lw.line(file, n, "out", w)), lw.ledger.out(t, file))
    case Nil{}:
      Nil{}

# The module -----------------------------------------------------------------------------

# the module's source: (hs-export 1 (ghc V) (file PATH))
def lw.src(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case +h <> t:
      V.sv.str(V.sv.at(h, 3n), 1n)
    case Nil{}:
      Nil{}

# GHC's words: the ghc, then any flags for it (a package's -i and
# -package-db; -fobject-code -outputdir DIR compiles the modules it imports
# once, for every module of the package, while *SRC keeps the module itself
# interpreted, with every top-level name in scope)
def lw.word(+w: List<&2, U32>, t: List<String>) -> List<String>:
  match w:
    case Nil{}:
      t
    case c <> r:
      S.str(c <> r) <> t

def lw.words(ws: List<&2, List<&2, U32>>) -> List<String>:
  match ws:
    case h <> t:
      lw.word(h, lw.words(t))
    case Nil{}:
      Nil{}

def lw.ghc.prog(ws: List<&2, List<&2, U32>>) -> String:
  match ws:
    case h <> t:
      S.str(h)
    case Nil{}:
      "ghc"

def lw.ghc.flags(ws: List<&2, List<&2, U32>>) -> List<String>:
  match ws:
    case h <> t:
      lw.words(t)
    case Nil{}:
      Nil{}

def lw.ghc.exec(+ghc: String, +src: String, +script: List<&2, U32>) -> IO(S.Out):
  +ws = S.split(S.b(ghc), 32)
  S.run(".", Nil{}, 3600, lw.ghc.prog(ws), List.append(&1, String, ["--interactive", "-v0", "-w", "-ignore-dot-ghci"], List.append(&1, String, lw.ghc.flags(ws), ["*" ++ src, "+RTS", "-M2g", "-RTS"])), script)

# GHC's answers, kept unless a call or the script ran out of time
def lw.kc.ghc.keep(+o: S.Out) -> Bool:
  +st = S.Out.status(o)
  Bool.not(Bool.or(Bool.or(U32.is_eq(st, 124), U32.is_eq(st, 125)), S.infix(S.Out.text(o), S.b(" timeout\n"))))

def lw.kc.ghc.got(got: Maybe<&2, List<&2, U32>>, +dir: String, +key: List<&2, U32>, +ghc: String, +src: String, +script: List<&2, U32>) -> IO(S.Out):
  match got:
    case Some{v}:
      IO.pure(S.Out, lw.kc.out.of(v))
    case None{}:
      do IO<S.Out>:
        +o : S.Out <- lw.ghc.exec(ghc, src, script)
        lw.kc.put(lw.kc.ghc.keep(o), dir, key, o)
        return o

# GHC's words in its key: all but -outputdir and its directory, where GHC
# keeps the modules it compiled (they change no answer: GHC compiles a
# module again when its source or flags change), so that runs with their
# own directories share answers (od: the last word was -outputdir)
def lw.kc.ghc.word(od: Bool, +w: List<&2, U32>, r: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match od:
    case True{}:
      r
    case False{}:
      w <> r

def lw.kc.ghc.words(ws: List<&2, List<&2, U32>>, od: Bool) -> List<&2, List<&2, U32>>:
  match ws od:
    case Nil{} _:
      Nil{}
    case w <> t True{}:
      lw.kc.ghc.words(t, False{})
    case +w <> t False{}:
      +o = S.eq(w, S.b("-outputdir"))
      lw.kc.ghc.word(o, w, lw.kc.ghc.words(t, o))

def lw.kc.ghc.at(on: Bool, +ck: Kc, +ghc: String, +src: String, +script: List<&2, U32>) -> IO(S.Out):
  match on:
    case False{}:
      lw.ghc.exec(ghc, src, script)
    case True{}:
      +key = C.ch.key([S.b("cata ghc 1"), lw.cc.ghc(lw.kc.cc(ck)), S.join(lw.kc.ghc.words(S.split(S.b(ghc), 32), False{}), 32), S.b(src), lw.kc.hs(ck), script])
      +dir = S.str(lw.kc.dir(ck))
      do IO<S.Out>:
        got : Maybe<&2, List<&2, U32>> <- C.ch.get(dir, key)
        lw.kc.ghc.got(got, dir, key, ghc, src, script)

def lw.ghc.run(has: Bool, +ck: Kc, +ghc: String, +src: String, +gpath: String, +opath: String, +script: List<&2, U32>) -> IO(List<&2, U32>):
  match has:
    case True{}:
      do IO<List<&2, U32>>:
        S.write(gpath, script)
        +o : S.Out <- lw.kc.ghc.at(lw.kc.on(ck), ck, ghc, src, script)
        S.write(opath, S.Out.text(o))
        return S.Out.text(o)
    case False{}:
      IO.pure(List<&2, U32>, Nil{})

def lw.names(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case h <> t:
      F.fd.item.name(h) <> lw.names(t)
    case Nil{}:
      Nil{}

# what a module kept, and the files written with its own
type Lk is Data:
  Lk{its: List<&2, T.BItem>, mk: List<&2, Mk>}

def lw.lk.its(+k: Lk) -> List<&2, T.BItem>:
  match k:
    case Lk{its, mk}:
      its

def lw.lk.mk(+k: Lk) -> List<&2, Mk>:
  match k:
    case Lk{its, mk}:
      mk

# the module written, its ledger, and the items it kept (ims: the aliases
# of its package's earlier files, which it may import; fb: its laws were
# set aside, see lw.lost)
# bend2hs (Back.bend), with CATA_BEND2HS set: the module's kept items as
# Haskell, OUT/hs/NAME.hs, its module named as the Haskell module (nm: its
# Haskell name and its defs', types' and constructors'), for
# tests/back/run.zsh to run the laws' GHCi script against
def lw.back(on: Bool, +out: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +its: List<&2, T.BItem>, +nm: K.BkN) -> IO(Unit):
  match on:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        S.mkdir(out ++ "/hs")
        S.write(out ++ "/hs/" ++ S.str(S.until(S.b(S.base(path)), 46)) ++ ".hs", K.bk.module(file, its, nm))

# the module's defs by their Haskell names (each TbFun's), for bend2hs
def lw.back.as(tbs: List<&2, F.Tb>) -> List<&2, K.BkA>:
  match tbs:
    case F.TbFun{+n, tvs, f} <> t:
      K.BkA{n, F.fd.vname(n)} <> lw.back.as(t)
    case _ <> t:
      lw.back.as(t)
    case Nil{}:
      Nil{}

# a type's constructors by their Haskell names, (con NAME ...) each
def lw.back.cs(+ty: List<&2, U32>, cs: X.Sx) -> List<&2, K.BkA>:
  match cs:
    case X.SxCons{+c, t}:
      +n = V.sv.str(c, 1n)
      K.BkA{n, F.fd.cname(ty, n)} <> lw.back.cs(ty, t)
    case _:
      Nil{}

# the module's types by their Haskell names
def lw.back.tn(ds: List<&2, Dd>) -> List<&2, K.BkA>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{+n, tvs, cs} <> t:
      K.BkA{n, F.fd.tyname(n)} <> lw.back.tn(t)

# the module's constructors by their Haskell names
def lw.back.cn(ds: List<&2, Dd>) -> List<&2, K.BkA>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{+n, tvs, cs} <> t:
      List.append(&2, K.BkA, lw.back.cs(n, cs), lw.back.cn(t))

# the partial defs (Fold's fd.pt: Either<String, A>, h's error as Inl), by
# their Bend names, as the laws' script has them (lw.kept.pt, before the
# gate: a def the fuel rule wraps keeps its name)
def lw.back.pt.if(p: Bool, +b: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match p:
    case True{}:
      b <> rest
    case False{}:
      rest

def lw.back.pts(tbs: List<&2, F.Tb>, +its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match tbs:
    case F.TbFun{+n, tvs, f} <> t:
      +b = F.fd.vname(n)
      lw.back.pt.if(lw.kept.pt(its, b), b, lw.back.pts(t, its))
    case _ <> t:
      lw.back.pts(t, its)
    case Nil{}:
      Nil{}

# h's types as G takes them back (Back.bend's BkT), from the export: what
# a type tree is, read off its head (Bd), then the walk, one def taking it
# as a parameter.  Base's types by their key M.N (Bb): a Haskell name, a
# list, String, a tuple, or one G does not know
type Bb is Data:
  BbH{n: List<&2, U32>}
  BbL{}
  BbStr{}
  BbTup{}
  BbNo{}

def lw.back.bb(+k: List<&2, U32>) -> Bb:
  Bool.pick(Bb, S.eq(k, S.b("GHC.Types.Int")), BbH{S.b("Int")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Num.Integer.Integer")), BbH{S.b("Integer")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Num.Natural.Natural")), BbH{S.b("Natural")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Types.Char")), BbH{S.b("Char")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Types.Bool")), BbH{S.b("Bool")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Types.Float")), BbH{S.b("Float")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Types.Ordering")), BbH{S.b("Ordering")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Tuple.Unit")), BbH{S.b("()")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Internal.Base.String")), BbStr{}, Bool.pick(Bb, S.eq(k, S.b("GHC.Types.List")), BbL{}, Bool.pick(Bb, S.eq(k, S.b("GHC.Internal.Maybe.Maybe")), BbH{S.b("Maybe")}, Bool.pick(Bb, S.eq(k, S.b("GHC.Internal.Data.Either.Either")), BbH{S.b("Either")}, Bool.pick(Bb, Bool.or(S.eq(k, S.b("GHC.Tuple.Tuple2")), Bool.or(S.eq(k, S.b("GHC.Tuple.Tuple3")), Bool.or(S.eq(k, S.b("GHC.Tuple.Tuple4")), S.eq(k, S.b("GHC.Tuple.Tuple5"))))), BbTup{}, BbNo{})))))))))))))

def lw.back.hd(a: K.BkT) -> K.BkT:
  match a:
    case K.BkTArgs{h, r}:
      h
    case _:
      K.BkTNo{}

def lw.back.base.of(b: Bb, a: K.BkT) -> K.BkT:
  match b:
    case BbH{n}:
      K.BkTh{n, a}
    case BbL{}:
      K.BkTList{lw.back.hd(a)}
    case BbStr{}:
      K.BkTList{K.BkTh{S.b("Char"), K.BkTNil{}}}
    case BbTup{}:
      K.BkTTup{a}
    case BbNo{}:
      K.BkTNo{}

# a type variable, a synonym of the module (its parameters, its body, the
# arguments), a type of the module, base's, a function, an argument spine,
# or none G takes
type Bd is Data:
  BdTv{n: List<&2, U32>}
  BdSyn{tvs: List<&2, List<&2, U32>>, body: X.Sx, args: X.Sx}
  BdOwn{n: List<&2, U32>, args: X.Sx}
  BdBase{b: Bb, args: X.Sx}
  BdFun{a: X.Sx, b: X.Sx}
  BdChain{x: X.Sx}
  BdNo{}

def lw.back.bd.tc(own: Bool, found: Maybe<&2, Sy>, +x: X.Sx) -> Bd:
  match own found:
    case True{} Some{Sy{n, tvs, body}}:
      BdSyn{tvs, body, lw.drop3(x)}
    case True{} None{}:
      BdOwn{V.sv.str(x, 2n), lw.drop3(x)}
    case False{} _:
      BdBase{lw.back.bb(lw.cat3(V.sv.str(x, 1n), [46], V.sv.str(x, 2n))), lw.drop3(x)}

def lw.back.bd.of(k: Hh, +m: List<&2, U32>, ss: List<&2, Sy>, +x: X.Sx) -> Bd:
  match k:
    case HhTv{}:
      BdTv{V.sv.str(x, 1n)}
    case HhTc{}:
      lw.back.bd.tc(S.eq(V.sv.str(x, 1n), m), lw.syn.find(ss, V.sv.str(x, 2n)), x)
    case HhFun{}:
      BdFun{V.sv.at(x, 1n), V.sv.at(x, 2n)}
    case _:
      BdNo{}

def lw.back.bd(+m: List<&2, U32>, ss: List<&2, Sy>, +x: X.Sx) -> Bd:
  lw.back.bd.of(lw.hh(V.sv.hd(x)), m, ss, x)

# a synonym's parameters bound to its arguments
type Bs is Data:
  Bs{v: List<&2, U32>, t: K.BkT}

def lw.back.sub(xs: List<&2, Bs>, +v: List<&2, U32>) -> K.BkT:
  match xs:
    case Nil{}:
      K.BkTv{F.fd.tvname(v)}
    case Bs{+k, t} <> r:
      Bool.pick(K.BkT, S.eq(k, v), t, lw.back.sub(r, v))

def lw.back.zip(tvs: List<&2, List<&2, U32>>, a: K.BkT) -> List<&2, Bs>:
  match tvs a:
    case v <> t K.BkTArgs{h, r}:
      Bs{v, h} <> lw.back.zip(t, r)
    case _ _:
      Nil{}

# h's type: its synonyms expanded (ss: the module's), its type variables
# by sub (a synonym's parameters) or as their Bend names, base's by
# Haskell's names, the module's by their Bend names, any other BkTNo
def lw.back.bkt(fuel: Nat, +m: List<&2, U32>, +ss: List<&2, Sy>, +sub: List<&2, Bs>, d: Bd) -> K.BkT:
  match fuel d:
    case 0n _:
      K.BkTNo{}
    case 1n+(+p) BdChain{X.SxCons{h, t}}:
      K.BkTArgs{lw.back.bkt(p, m, ss, sub, lw.back.bd(m, ss, h)), lw.back.bkt(p, m, ss, sub, BdChain{t})}
    case 1n+p BdChain{x}:
      K.BkTNil{}
    case 1n+p BdTv{n}:
      lw.back.sub(sub, n)
    case 1n+(+p) BdSyn{tvs, body, args}:
      lw.back.bkt(p, m, ss, lw.back.zip(tvs, lw.back.bkt(p, m, ss, sub, BdChain{args})), lw.back.bd(m, ss, body))
    case 1n+p BdOwn{n, args}:
      K.BkTc{F.fd.tyname(n), lw.back.bkt(p, m, ss, sub, BdChain{args})}
    case 1n+p BdBase{b, args}:
      lw.back.base.of(b, lw.back.bkt(p, m, ss, sub, BdChain{args}))
    case 1n+(+p) BdFun{a, b}:
      K.BkTFun{lw.back.bkt(p, m, ss, sub, lw.back.bd(m, ss, a)), lw.back.bkt(p, m, ss, sub, lw.back.bd(m, ss, b))}
    case 1n+p BdNo{}:
      K.BkTNo{}

# a constructor's fields' h types, (con NAME FIELDS TYPES EX)
def lw.back.fts(+m: List<&2, U32>, +ss: List<&2, Sy>, tys: X.Sx) -> List<&2, K.BkT>:
  match tys:
    case X.SxCons{+t, r}:
      lw.back.bkt(64n, m, ss, Nil{}, lw.back.bd(m, ss, t)) <> lw.back.fts(m, ss, r)
    case _:
      Nil{}

def lw.back.cf(+m: List<&2, U32>, +ss: List<&2, Sy>, +ty: List<&2, U32>, cs: X.Sx) -> List<&2, K.BkF>:
  match cs:
    case X.SxCons{+c, t}:
      K.BkF{F.fd.cname(ty, V.sv.str(c, 1n)), lw.back.fts(m, ss, V.sv.at(c, 3n))} <> lw.back.cf(m, ss, ty, t)
    case _:
      Nil{}

def lw.back.nf(+m: List<&2, U32>, +ss: List<&2, Sy>, ds: List<&2, Dd>) -> List<&2, K.BkF>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{+n, tvs, cs} <> t:
      List.append(&2, K.BkF, lw.back.cf(m, ss, n, cs), lw.back.nf(m, ss, t))

# A type's kind variables.  hs-export lists them with its type variables
# (data NAME (TV...) ...) but drops them where the type is applied (tc's
# invisible arguments), and they come first.  So a type has k of them when
# its first k variables are in no field and no use applies it to more
# than its count less k (ar: the most arguments any (tc m n ...) has)
def lw.back.ar.here(+x: X.Sx, +m: List<&2, U32>, +n: List<&2, U32>) -> Nat:
  Bool.pick(Nat, Bool.and(V.sv.is(V.sv.hd(x), "tc"), Bool.and(S.eq(V.sv.str(x, 1n), m), S.eq(V.sv.str(x, 2n), n))), Nat.sub(X.tsx.len(x), 3n), 0n)

def lw.back.ar.go(x: X.Sx, here: Nat, +m: List<&2, U32>, +n: List<&2, U32>) -> Nat:
  match x:
    case X.SxCons{+h, t}:
      Nat.max(here, Nat.max(lw.back.ar.go(h, lw.back.ar.here(h, m, n), m, n), lw.back.ar.go(t, 0n, m, n)))
    case _:
      here

def lw.back.ars(xs: List<&2, X.Sx>, +m: List<&2, U32>, +n: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      Nat.max(lw.back.ar.go(h, lw.back.ar.here(h, m, n), m, n), lw.back.ars(t, m, n))

# whether (tv v) is anywhere in x
def lw.back.uses.go(x: X.Sx, here: Bool, +v: List<&2, U32>) -> Bool:
  match x:
    case X.SxCons{+h, t}:
      Bool.or(here, Bool.or(lw.back.uses.go(h, Bool.and(V.sv.is(V.sv.hd(h), "tv"), S.eq(V.sv.str(h, 1n), v)), v), lw.back.uses.go(t, False{}, v)))
    case _:
      here

def lw.back.lead(tvs: List<&2, List<&2, U32>>, +lim: Nat, +cs: X.Sx) -> Nat:
  match tvs lim:
    case +v <> t 1n+p:
      +k = lw.back.lead(t, p, cs)
      Bool.pick(Nat, lw.back.uses.go(cs, False{}, v), 0n, 1n+k)
    case _ _:
      0n

def lw.back.kd(ds: List<&2, Dd>, +xs: List<&2, X.Sx>, +m: List<&2, U32>) -> List<&2, K.BkD>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{+n, +tvs, +cs} <> t:
      +d = lw.back.lead(tvs, Nat.sub(List.length(&2, List<&2, U32>, tvs), lw.back.ars(xs, m, n)), cs)
      +b = F.fd.tyname(n)
      K.BkD{b, d} <> K.BkD{lw.cat(b, S.b(".fn")), d} <> lw.back.kd(t, xs, m)

# what G needs of the module (Back.bend's BkN), when CATA_BEND2HS is set
# (on): nothing is computed when it is not
def lw.back.nm(on: Bool, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +tbs: List<&2, F.Tb>, +dds: List<&2, Dd>, +its: List<&2, T.BItem>, +xs: List<&2, X.Sx>) -> K.BkN:
  match on:
    case True{}:
      +ss = lw.syns(xs)
      K.BkN{m, lw.back.as(tbs), lw.back.tn(dds), lw.back.cn(dds), lw.back.pts(tbs, its), lw.back.nf(m, ss, dds), lw.back.kd(dds, xs, m), ims}
    case False{}:
      K.BkN{m, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def lw.fin(+ck: Kc, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +fb: Bool, +g: F.Gs, +ps: List<&2, Pl>, +nm: K.BkN) -> IO(Lk):
  +its = lw.gs.its(g)
  +wrote = F.fd.wrote(pkg, its)
  +text = F.fd.render(file, m, ims, its)
  do IO<Lk>:
    F.fd.module.write(wrote, path, text)
    S.add(out ++ "/ledger.tsv", lw.cat(lw.ledger.ok(its, its, file, ps, F.fd.bpick(fb, S.b("nolaw:law-gate-failed"), Nil{})), lw.ledger.out(lw.gs.out(g), file)))
    lw.back(lw.kc.back(ck), out, path, file, m, its, nm)
    return Lk{its, lw.kc.wrote(wrote, ck, S.until(S.b(S.base(path)), 46), text)}

def lw.start(g: F.Gs, laws: List<&2, T.BItem>, +bad: List<&2, F.Dr>) -> F.Gs:
  match g:
    case F.Gs{k, o, d}:
      lw.undone(lw.pruned(lw.drops(bad, F.Gs{List.append(&2, T.BItem, k, laws), o, False{}})))

# whether the one gate (the fold's defs and their laws, checked together)
# lost every def the fold had while there were laws: Bend died on the file
# or ran out of time, so no item was to blame (or every def failed).  Then
# the defs are gated again without their laws, and keep none.
def lw.lost(+laws: Bool, +g0: F.Gs, +g2: F.Gs) -> Bool:
  Bool.and(laws, Bool.and(F.fd.hasdef(lw.gs.its(g0)), Bool.not(F.fd.hasdef(lw.gs.its(g2)))))

# The laws again, one def's at a time, when the one gate was lost: a law
# Bend cannot run (a Nat too large to count, a stack) took every law of its
# module with it. Each def's laws are gated with what is kept so far (g);
# a check that dies keeps none of them, one that refuses a law drops the def
# as the one gate does.
def lw.lawsof(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, T.BItem>:
  match its:
    case +h <> t:
      +k = F.fd.item.name(h)
      F.fd.without.put(Bool.not(Bool.and(lw.dotted(k), S.eq(lw.undot(k), n))), h, lw.lawsof(t, n))
    case Nil{}:
      Nil{}

def lw.each.got(none: Bool, g: F.Gs, g2: F.Gs) -> F.Gs:
  match none g2:
    case False{} F.Gs{+k, o, True{}}:
      Bool.pick(F.Gs, F.fd.hasdef(k), F.Gs{k, o, True{}}, g)
    case _ _:
      g

def lw.each(ds: List<&2, T.BItem>, +laws: List<&2, T.BItem>, +g: F.Gs, +ck: Kc, +bend: String, +try: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +dt: List<&2, T.BItem>) -> IO(F.Gs):
  match ds:
    case Nil{}:
      IO.pure(F.Gs, g)
    case +h <> t:
      +ls = lw.lawsof(laws, F.fd.item.name(h))
      +none = List.is_empty(&2, T.BItem, ls)
      do IO<F.Gs>:
        +g2 : F.Gs <- lw.gate(Bool.pick(Nat, none, 0n, Nat.mul(3n, 1n+List.length(&2, T.BItem, ls))), lw.start(g, ls, Nil{}), ck, bend, try, file, m, ims, dt)
        lw.each(t, laws, lw.each.got(none, g, g2), ck, bend, try, file, m, ims, dt)

def lw.after(lost: Bool, +good: List<&2, T.BItem>, +ck: Kc, +bend: String, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +try: String, +g0: F.Gs, +g2: F.Gs, +ps: List<&2, Pl>, +dt: List<&2, T.BItem>, +nm: K.BkN) -> IO(Lk):
  match lost:
    case True{}:
      do IO<Lk>:
        +g1 : F.Gs <- F.fd.gate(Nat.mul(3n, 1n+List.length(&2, T.BItem, lw.gs.its(g0))), g0, bend, try, file, m, ims, dt)
        g3 : F.Gs <- lw.each(lw.gs.its(g1), good, lw.done.if(True{}, g1), ck, bend, try, file, m, ims, dt)
        lw.fin(ck, out, file, m, ims, pkg, path, True{}, g3, ps, nm)
    case False{}:
      lw.fin(ck, out, file, m, ims, pkg, path, False{}, g2, ps, nm)

# The gate, once: the fold's defs (g0, before any check) and the laws GHC's
# answers give, together.  A def Bend refuses goes with its laws and what
# uses it; a law Bend refuses takes its def out (law:).  So a module whose
# defs and laws all hold costs one check.
def lw.laws2(+rounds: Nat, +ck: Kc, +bend: String, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +try: String, +g0: F.Gs, +ps: List<&2, Pl>, +laws: List<&2, T.BItem>, +dt: List<&2, T.BItem>, +nm: K.BkN) -> IO(Lk):
  +good = lw.good(laws)
  +g1 = lw.start(g0, good, lw.bad(laws))
  +n = List.length(&2, T.BItem, lw.gs.its(g1))
  do IO<Lk>:
    +g2 : F.Gs <- lw.gate(Bool.pick(Nat, Nat.is_eq(rounds, 0n), Nat.mul(3n, 1n+n), rounds), lw.done.if(Nat.is_eq(n, 0n), g1), ck, bend, try, file, m, ims, dt)
    lw.after(lw.lost(Bool.not(List.is_empty(&2, T.BItem, good)), g0, g2), good, ck, bend, out, file, m, ims, pkg, path, try, g0, g2, ps, dt, nm)

# GHC's answers for the fold's defs (g0, before any check), then the gate
def lw.laws(+rounds: Nat, +ck: Kc, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +xs: List<&2, X.Sx>, +tbs: List<&2, F.Tb>, +path: String, +try: String, +g0: F.Gs, +dt: List<&2, T.BItem>) -> IO(Lk):
  +le = {Le{m, lw.syns(xs), Nil{}} : Le}
  +dds = lw.dds(xs)
  +ps = lw.plans(tbs, lw.gs.its(g0), le, dds, m)
  do IO<Lk>:
    txt : List<&2, U32> <- lw.ghc.run(lw.any.pl(ps), ck, ghc, S.str(lw.src(xs)), out ++ "/" ++ S.str(base) ++ ".ghci", out ++ "/" ++ S.str(base) ++ ".ghc", lw.script(m, dds, ps))
    lw.laws2(rounds, ck, bend, out, file, m, ims, pkg, path, try, g0, ps, lw.items(ps, lw.ols(S.split(txt, 10)), lw.has.str(xs, S.b("HsInt"))), dt, lw.back.nm(lw.kc.back(ck), m, ims, tbs, dds, lw.gs.its(g0), xs))

# the items before the gate, and the ones it drops before its first check
# (dep: what they use that is out), as OUT/NAME_all.bend and
# OUT/NAME_drops.tsv: what a gate's ledger does not list (a group's .mu, a
# lifted def)
def lw.drs.text(ds: List<&2, F.Dr>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case F.Dr{n, w} <> t:
      S.append(n, 9 <> S.append(w, 10 <> lw.drs.text(t)))

def lw.gs.drs(g: F.Gs) -> List<&2, F.Dr>:
  match g:
    case F.Gs{its, o, d}:
      o

# the cache's state for a module: HsPrelude's digest once it is written,
# and the package's sources' digest with the module's source (each module
# alone: its own)
def lw.kc.pre(has: Bool, +ck: Kc, +out: String) -> IO(Kc):
  match has:
    case True{}:
      IO.pure(Kc, ck)
    case False{}:
      do IO<Kc>:
        +pre : List<&2, U32> <- S.read(out ++ "/HsPrelude.bend")
        return lw.kc.with.mk(ck, lw.kc.add(True{}, ck, S.b("HsPrelude"), pre))

def lw.kc.has(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case Some{h}:
      True{}
    case None{}:
      False{}

def lw.kc.module.at(on: Bool, +ck: Kc, +pkg: Bool, +out: String, +src: List<&2, U32>) -> IO(Kc):
  match on:
    case False{}:
      IO.pure(Kc, ck)
    case True{}:
      do IO<Kc>:
        +ck2 : Kc <- lw.kc.pre(lw.kc.has(lw.mk.find(lw.kc.mk(ck), S.b("HsPrelude"))), ck, out)
        +hsrc : List<&2, U32> <- S.read(S.str(src))
        return lw.kc.with.hs(ck2, C.ch.key([S.b("cata hs 1"), Bool.pick(List<&2, U32>, pkg, lw.kc.hs(ck2), Nil{}), src, hsrc]))

def lw.kc.module(+ck: Kc, +pkg: Bool, +out: String, +src: List<&2, U32>) -> IO(Kc):
  lw.kc.module.at(lw.kc.on(ck), ck, pkg, out, src)

# a module's answer: its package after it, and the cache's state
type Lm is Data:
  Lm{px: F.Px, ck: Kc, dm: Map<&2, List<&2, Bool>>}

def lw.lm.px(+r: Lm) -> F.Px:
  match r:
    case Lm{px, ck, dm}:
      px

def lw.lm.ck(+r: Lm) -> Kc:
  match r:
    case Lm{px, ck, dm}:
      ck

# the bindings read at Integer so far (Survey's sv.dfl)
def lw.lm.dm(+r: Lm) -> Map<&2, List<&2, Bool>>:
  match r:
    case Lm{px, ck, dm}:
      dm

# the module BendRt (prelude/Back/BendRt.hs, in F(G(b))'s package: tests/
# back/round.zsh): its kept items and its wrappers' rewrites as laws
# (Fold's fd.rt.laws), OUT/BendRt_rt.bend.  Any other module: nothing.
def lw.rt.write(isrt: Bool, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>) -> IO(Unit):
  match isrt:
    case True{}:
      S.write(out ++ "/BendRt_rt.bend", F.fd.render(file, m, ims, List.append(&2, T.BItem, its, F.fd.rt.laws(its))))
    case False{}:
      IO.pure(Unit, Unit{})

# a module: fold it as Fold.bend does, ask GHC for its defs' laws, and gate
# the defs and laws together (px: what its package's modules before it
# gave, F.fd.px0() for a module alone); the package after it
def lw.module(+rounds: Nat, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, bytes: List<&2, U32>, +pkg: Bool, +px: F.Px, +ck: Kc, dm: Map<&2, List<&2, Bool>>) -> IO(Lm):
  +d = V.sv.dfl.module(V.sv.read(bytes), dm)
  +xs = V.sv.dfl.dm.xs(d)
  +m = V.sv.modname(xs)
  +tbs = F.fd.tbs(xs)
  +cs = F.fd.ctrs(xs)
  +ds = F.fd.dfs(tbs)
  +env = F.fd.syns(Nat.add(F.fd.nsyn(xs), List.length(&2, F.Sy, F.fd.px.sy(px))), xs, F.fd.env0(m, cs, ds, px))
  +g2 = F.fd.tpl.settle(F.fd.hm.all(F.fd.allgots(xs, tbs, env)), F.fd.px.tfs(px))
  +gs = F.fd.tpl.fin(g2, List.append(&2, F.Tf, F.fd.tfs(g2), F.fd.px.tfs(px)))
  +its = F.fd.mod.its(gs, xs, m, env, px)
  +ims = F.fd.ims(px)
  +path = out ++ "/" ++ S.str(base) ++ ".bend"
  +try = out ++ "/" ++ S.str(base) ++ "_try.bend"
  do IO<Lm>:
    F.fd.hsprelude.write(out)
    +ck1 : Kc <- lw.kc.module(ck, pkg, out, lw.src(xs))
    S.write(out ++ "/" ++ S.str(base) ++ "_all.bend", F.fd.render(file, m, ims, its))
    +g0 : F.Gs <- IO.pure(F.Gs, F.fd.predrop(its, F.fd.got.outs(gs)))
    S.write(out ++ "/" ++ S.str(base) ++ "_drops.tsv", lw.drs.text(lw.gs.drs(g0)))
    +kept : Lk <- lw.laws(rounds, ck1, bend, ghc, out, file, base, m, ims, pkg, xs, tbs, path, try, g0, F.fd.px.dt(px))
    lw.rt.write(F.fd.is(m, "BendRt"), out, file, m, ims, lw.lk.its(kept))
    return Lm{F.fd.px.next(pkg, px, m, base, xs, gs, F.fd.tfs(g2), cs, ds, lw.lk.its(kept)), lw.kc.with.mk(ck1, lw.lk.mk(kept)), V.sv.dfl.next(pkg, V.sv.dfl.dm.m(d))}

def lw.run(xs: List<String>, +rounds: Nat, +bend: String, +ghc: String, +out: String, +pkg: Bool, +px: F.Px, +ck: Kc, dm: Map<&2, List<&2, Bool>>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +r : Lm <- lw.module(rounds, bend, ghc, out, S.b(f), F.fd.base(S.b(f)), bytes, pkg, px, ck, dm)
        lw.run(t, rounds, bend, ghc, out, pkg, lw.lm.px(r), lw.lm.ck(r), lw.lm.dm(r))

# the cache's settings (CATA_CACHE: its directory, made if missing), with
# bend's and GHC's identities: each resolved (PATH, then links)
def lw.kc.which.got(m: Maybe<&2, String>, +p: String) -> IO(String):
  match m:
    case Some{q}:
      S.realpath(q)
    case None{}:
      IO.pure(String, p)

def lw.kc.which(+p: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- S.which(p)
    lw.kc.which.got(m, p)

def lw.kc.start.at(on: Bool, +dir: String, +bend: String, +ghc: String) -> IO(Kc):
  match on:
    case False{}:
      IO.pure(Kc, lw.kc0())
    case True{}:
      do IO<Kc>:
        S.mkdir(dir)
        +b : String <- lw.kc.which(bend)
        +g : String <- lw.kc.which(lw.ghc.prog(S.split(S.b(ghc), 32)))
        return Kc{Cc{S.b(dir), S.b(b), S.b(g), False{}}, Nil{}, Nil{}}

def lw.kc.start(+dir: String, +bend: String, +ghc: String) -> IO(Kc):
  lw.kc.start.at(Bool.not(List.is_empty(&2, U32, S.b(dir))), dir, bend, ghc)

def lw.main.go(pkg: Bool, args: List<String>, +rounds: Nat, +bend: String, +ghc: String, +ck: Kc) -> IO(Unit):
  match args:
    case out <> files:
      lw.run(files, rounds, bend, ghc, out, pkg, F.fd.px0(), ck, V.sv.dfl0())
    case Nil{}:
      IO.print("usage: law [--package] OUT FILE.sexp...  (BEND: the bend to check with, GHC: the ghc and any flags for it, CATA_CACHE: a directory to keep their answers in)")

def lw.main.pkg(pkg: Bool, a: String, rest: List<String>, +rounds: Nat, +bend: String, +ghc: String, +ck: Kc) -> IO(Unit):
  match pkg:
    case True{}:
      lw.main.go(True{}, rest, rounds, bend, ghc, ck)
    case False{}:
      lw.main.go(False{}, a <> rest, rounds, bend, ghc, ck)

# `law OUT FILE...` takes each module alone; `law --package OUT FILE...`
# one package's modules in dependency order (hs-export --package's
# modules.txt), each using what the ones before it kept (GHC then needs the
# package's -i and -package-db after the ghc)
def lw.main(args: List<String>, +rounds: Nat, +bend: String, +ghc: String, +ck: Kc) -> IO(Unit):
  match args:
    case +a <> rest:
      lw.main.pkg(S.eq(S.b(a), S.b("--package")), a, rest, rounds, bend, ghc, ck)
    case Nil{}:
      lw.main.go(False{}, Nil{}, rounds, bend, ghc, ck)

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    +bend : String <- S.env("BEND", "bend")
    +ghc : String <- S.env("GHC", "ghc")
    rounds : Nat <- S.env.nat("FOLD_ROUNDS", 0n)
    +dir : String <- S.env("CATA_CACHE", "")
    +back : String <- S.env("CATA_BEND2HS", "")
    +ck : Kc <- lw.kc.start(dir, bend, ghc)
    lw.main(List.tail(&1, String, argv), rounds, bend, ghc, lw.kc.with.back(ck, Bool.not(List.is_empty(&2, U32, S.b(back)))))
