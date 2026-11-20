import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X
import ./a2b/ToBend/Ast.bend as T
import ./Survey.bend as V
import ./Fold.bend as F

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

# the name before the first dot
def lw.undot(xs: List<&2, U32>) -> List<&2, U32>:
  S.until(xs, 46)

# Haskell types ------------------------------------------------------------

# A Haskell type at the instance the laws use (every type variable Int).
# HyNat keeps the Haskell name (Int, Integer or Natural) for GHCi; a
# user type's arguments and a constructor's fields are an HyArgs spine.
type Hy is Data:
  HyNat{hs: List<&2, U32>}
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
  [BkE{"GHC.Types.Int", BkInt{}}, BkE{"GHC.Num.Integer.Integer", BkInteger{}}, BkE{"GHC.Num.Natural.Natural", BkNatural{}}, BkE{"GHC.Types.Bool", BkBool{}}, BkE{"GHC.Types.Char", BkChar{}}, BkE{"GHC.Types.List", BkList{}}, BkE{"GHC.Internal.Base.String", BkStr{}}, BkE{"GHC.Internal.IO.FilePath", BkStr{}}, BkE{"GHC.Internal.Maybe.Maybe", BkMaybe{}}, BkE{"GHC.Internal.Data.Either.Either", BkEither{}}, BkE{"GHC.Tuple.Tuple2", BkT2{}}, BkE{"GHC.Tuple.Tuple3", BkT3{}}, BkE{"GHC.Tuple.Unit", BkUnit{}}, BkE{"GHC.Types.Ordering", BkCmp{}}]

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
def lw.va.hs(v: Va, mode: Vm) -> List<&2, U32>:
  match v mode:
    case VaNat{n} _:
      lw.nshow(n)
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

# an answer in Bend; a negative number has none (the fold's Int is Nat).
# It recurses on the tree's own parts (a string's answer is as long as the
# string)
def lw.out(x: X.Sx, k: Ok, mode: Vm) -> T.Bt:
  match x k mode:
    case X.SxCons{+h, t} _ VmSp{}:
      T.BtArgs{lw.out(h, lw.okind(h), VmVal{}), lw.out(t, OkNo{}, VmSp{})}
    case _ _ VmSp{}:
      T.BtANil{}
    case X.SxCons{+h, t} _ VmList{}:
      T.BtCon{S.b("Con"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}), T.BtArgs{lw.out(t, OkNo{}, VmList{}), T.BtANil{}}}}
    case _ _ VmList{}:
      F.fd.con0("Nil")
    case X.SxCons{+h, X.SxNil{}} _ VmTup{}:
      lw.out(h, lw.okind(h), VmVal{})
    case X.SxCons{+h, t} _ VmTup{}:
      T.BtCon{S.b("Tuple"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}), T.BtArgs{lw.out(t, OkNo{}, VmTup{}), T.BtANil{}}}}
    case _ _ VmTup{}:
      F.fd.con0("Unit")
    case +y OkNat{} _:
      T.BtNat{X.tsx.atom.of(X.tsx.at(1n, y))}
    case _ OkNeg{} _:
      T.BtTodo{S.b("law:negative-answer")}
    case +y OkChar{} _:
      F.fd.char(X.tsx.nat(X.tsx.at(1n, y)))
    case X.SxCons{h, t} OkList{} _:
      lw.out(t, OkNo{}, VmList{})
    case X.SxCons{h, t} OkTup{} _:
      lw.out(t, OkNo{}, VmTup{})
    case X.SxCons{h, X.SxCons{c, t}} OkCon{} _:
      T.BtCon{X.tsx.str.of(c), lw.out(t, OkNo{}, VmSp{})}
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

# a parameter of the def: a type (Data), passed Nat; else a value
def lw.kinds(ps: List<&2, T.BParam>) -> List<&2, Bool>:
  match ps:
    case T.BParam{m, x, T.BtVar{k}} <> t:
      S.eq(k, S.b("Data")) <> lw.kinds(t)
    case _ <> t:
      False{} <> lw.kinds(t)
    case Nil{}:
      Nil{}

def lw.tpls(ps: List<&2, T.BParam>) -> List<&2, Bool>:
  match ps:
    case T.BParam{T.BmTpl{}, x, ty} <> t:
      True{} <> lw.tpls(t)
    case _ <> t:
      False{} <> lw.tpls(t)
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
def lw.bargs(ks: List<&2, Bool>, ts: List<&2, Bool>, vs: Va) -> List<&2, T.Bt>:
  match ks ts vs:
    case True{} <> k2 t <> t2 _:
      lw.wrap(t, F.fd.ty0("Nat")) <> lw.bargs(k2, t2, vs)
    case False{} <> k2 t <> t2 VaArgs{v, r}:
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

def lw.bcall(+b: List<&2, U32>, +ks: List<&2, Bool>, ts: List<&2, Bool>, +vs: Va) -> T.Bt:
  lw.apply(lw.vdrop(lw.nvals(ks), vs), T.tba.call(T.BtVar{b}, lw.bargs(ks, ts, vs)))

def lw.lcs(ins: List<&2, Va>, +k: Nat, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, Bool>) -> List<&2, Lc>:
  match ins:
    case VaTup{+s} <> t:
      Lc{k, lw.cat(f, lw.va.hs(s, VmSp{})), lw.bcall(b, ks, ts, s)} <> lw.lcs(t, 1n+k, b, f, ks, ts)
    case _ <> t:
      lw.lcs(t, k, b, f, ks, ts)
    case Nil{}:
      Nil{}

def lw.plan.ins(ins: List<&2, Va>, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, Bool>, ret: T.Bt) -> Pl:
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

def lw.plan.of(why: List<&2, U32>, +b: List<&2, U32>, +h: Hy, +m: List<&2, U32>, +hsn: List<&2, U32>, +le: Le, +dds: List<&2, Dd>, +ps: List<&2, T.BParam>) -> Pl:
  match why:
    case Nil{}:
      +f = lw.cat3(S.b("(("), lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41]))
      lw.plan.ins(List.take(&2, Va, lw.vals(40n, 2n, le, dds, QFields{lw.args(h)}), 8n), b, f, lw.kinds(ps), lw.tpls(ps), lw.bty(lw.res(h)))
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
def lw.plan.tb(found: Maybe<&2, List<&2, T.BParam>>, +n: List<&2, U32>, +f: X.Sx, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>) -> List<&2, Pl>:
  match found:
    case Some{+ps}:
      +h = lw.ty(le, V.sv.at(f, 2n))
      [lw.plan.of(lw.plan.why(h, lw.kinds(ps)), F.fd.vname(n), h, m, n, le, dds, ps)]
    case None{}:
      Nil{}

def lw.plans(tbs: List<&2, F.Tb>, +its: List<&2, T.BItem>, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>) -> List<&2, Pl>:
  match tbs:
    case F.TbFun{+n, tvs, +f} <> t:
      List.append(&2, Pl, lw.plan.tb(lw.kept(its, F.fd.vname(n)), n, f, le, dds, m), lw.plans(t, its, le, dds, m))
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
  ":set -XScopedTypeVariables -XFlexibleInstances -XFlexibleContexts\nimport qualified Prelude as LawP\nimport qualified System.Timeout as LawT\nimport qualified Control.Exception as LawE\nimport qualified System.IO as LawIO\nimport qualified Numeric.Natural as LawN\n:{\nclass LawSx a where\n  lawSx :: a -> LawP.String\n:}\n:{\nlawI :: LawP.Integer -> LawP.String\nlawI n = if n LawP.< 0 then \"(neg \" LawP.++ LawP.show (LawP.negate n) LawP.++ \")\" else \"(nat \" LawP.++ LawP.show n LawP.++ \")\"\n:}\n:{\nlawC :: LawP.String -> [LawP.String] -> LawP.String\nlawC c xs = \"(con \\\"\" LawP.++ c LawP.++ \"\\\"\" LawP.++ LawP.concatMap (\\x -> ' ' : x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx LawP.Int where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Integer where\n  lawSx n = lawI n\n:}\n:{\ninstance LawSx LawN.Natural where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Bool where\n  lawSx b = if b then lawC \"True\" [] else lawC \"False\" []\n:}\n:{\ninstance LawSx LawP.Char where\n  lawSx c = \"(char \" LawP.++ LawP.show (LawP.fromEnum c) LawP.++ \")\"\n:}\n:{\ninstance LawSx () where\n  lawSx _ = lawC \"Unit\" []\n:}\n:{\ninstance LawSx LawP.Ordering where\n  lawSx o = case o of { LawP.LT -> lawC \"LT\" []; LawP.EQ -> lawC \"EQ\" []; LawP.GT -> lawC \"GT\" [] }\n:}\n:{\ninstance LawSx a => LawSx [a] where\n  lawSx xs = \"(list\" LawP.++ LawP.concatMap (\\x -> ' ' : lawSx x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx a => LawSx (LawP.Maybe a) where\n  lawSx m = case m of { LawP.Nothing -> lawC \"None\" []; LawP.Just x -> lawC \"Some\" [lawSx x] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (LawP.Either a b) where\n  lawSx e = case e of { LawP.Left x -> lawC \"Inl\" [lawSx x]; LawP.Right y -> lawC \"Inr\" [lawSx y] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (a, b) where\n  lawSx (a, b) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \")\"\n:}\n:{\ninstance (LawSx a, LawSx b, LawSx c) => LawSx (a, b, c) where\n  lawSx (a, b, c) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \" \" LawP.++ lawSx c LawP.++ \")\"\n:}\n:{\nlawRun :: LawSx b => LawP.String -> LawP.Int -> b -> LawP.IO ()\nlawRun n k v = do\n  r <- LawE.try (LawT.timeout 2000000 (let s = lawSx v in LawE.evaluate (LawP.length s) LawP.>> LawP.return s))\n  case r of\n    LawP.Left (e :: LawE.SomeException) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" err\")\n    LawP.Right LawP.Nothing -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" timeout\")\n    LawP.Right (LawP.Just s) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" ok \" LawP.++ s)\n  LawIO.hFlush LawIO.stdout\n:}\n"

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

def lw.script(+m: List<&2, U32>, ds: List<&2, Dd>, ps: List<&2, Pl>) -> List<&2, U32>:
  lw.cat3(S.b(lw.ghci.pre()), lw.insts(m, ds), lw.lines(ps))

# The laws ---------------------------------------------------------------------------

def lw.lawname(+b: List<&2, U32>, k: Nat) -> List<&2, U32>:
  lw.cat3(b, S.b(".ex"), lw.nshow(k))

# the law, once GHC's answer reads as a tree
def lw.law.sx(m: Maybe<&2, X.Sx>, +b: List<&2, U32>, +ret: T.Bt, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>) -> List<&2, T.BItem>:
  match m:
    case Some{+x}:
      +doc = lw.cat3(S.b("GHC: "), hs, lw.cat(S.b(") = "), v))
      T.BiDef{lw.lawname(b, k), Nil{}, T.BtEq{ret, call, lw.out(x, lw.okind(x), VmVal{})}, T.BtExpr{T.BtRefl{}}, doc <> Nil{}} <> Nil{}
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

def lw.law.ok(ok: Bool, +b: List<&2, U32>, +ret: T.Bt, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>) -> List<&2, T.BItem>:
  match ok:
    case True{}:
      lw.law.sx(X.tsx.one(v), b, ret, k, hs, call, v)
    case False{}:
      Nil{}

def lw.law(o: Maybe<&2, Ol>, +b: List<&2, U32>, +ret: T.Bt, k: Nat, +hs: List<&2, U32>, call: T.Bt) -> List<&2, T.BItem>:
  match o:
    case Some{Ol{ob, ok, +st, +v}}:
      lw.law.ok(Bool.and(V.sv.is(st, "ok"), Bool.not(Bool.or(lw.bignum(v), lw.bignum(hs)))), b, ret, k, hs, call, v)
    case None{}:
      Nil{}

def lw.laws.lc(ls: List<&2, Lc>, +b: List<&2, U32>, +ret: T.Bt, +os: List<&2, Ol>) -> List<&2, T.BItem>:
  match ls:
    case Lc{+k, hs, c} <> t:
      List.append(&2, T.BItem, lw.law(lw.ol.find(os, b, lw.nshow(k)), b, ret, k, hs, c), lw.laws.lc(t, b, ret, os))
    case Nil{}:
      Nil{}

def lw.items(ps: List<&2, Pl>, +os: List<&2, Ol>) -> List<&2, T.BItem>:
  match ps:
    case Pl{+b, +r, ls} <> t:
      List.append(&2, T.BItem, lw.laws.lc(ls, b, r, os), lw.items(t, os))
    case _ <> t:
      lw.items(t, os)
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
def lw.who(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{n}:
      Some{lw.undot(n)}
    case None{}:
      None{}

def lw.whykind(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case Some{n}:
      F.fd.bpick(lw.dotted(n), S.b("law:"), S.b("check:"))
    case None{}:
      S.b("check:")

# the names of the items that are not laws
def lw.defnames(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case +h <> t:
      +n = F.fd.item.name(h)
      +r = lw.defnames(t)
      F.fd.bpicks(lw.dotted(n), r, n <> r)
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

def lw.gate.step(g: F.Gs, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +out: List<&2, U32>) -> F.Gs:
  match g:
    case F.Gs{its, o, True{}}:
      F.Gs{its, o, True{}}
    case F.Gs{+its, +o, False{}}:
      +ls = S.split(out, 10)
      +who = F.fd.gate.who(F.fd.errline(ls), F.fd.render(file, m, ims, its))
      Bool.pick(F.Gs, S.prefix(out, S.b("ALL PROOFS CHECK")), F.Gs{its, o, True{}}, lw.pruned(F.fd.gate.drop(lw.who(who), its, o, lw.cat(lw.whykind(who), F.fd.errwhy(ls)))))

def lw.gate(fuel: Nat, g: F.Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>) -> IO(F.Gs):
  match fuel:
    case 0n:
      IO.pure(F.Gs, g)
    case 1n+p:
      +g1 = g
      do IO<F.Gs>:
        o : S.Out <- F.fd.gate.io(g1, bend, path, file, m, ims)
        lw.gate(p, lw.gate.step(g1, file, m, ims, S.Out.text(o)), bend, path, file, m, ims)

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
    case T.BiType{n, xs, k, cs, d} <> t:
      lw.cat(lw.line(file, n, "ok-type", Nil{}), lw.ledger.ok(t, all, file, ps, fb))
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

def lw.ghc.run(has: Bool, +ghc: String, +src: String, +gpath: String, +opath: String, +script: List<&2, U32>) -> IO(List<&2, U32>):
  match has:
    case True{}:
      +ws = S.split(S.b(ghc), 32)
      do IO<List<&2, U32>>:
        S.write(gpath, script)
        +o : S.Out <- S.run(".", Nil{}, 3600, lw.ghc.prog(ws), List.append(&1, String, ["--interactive", "-v0", "-w", "-ignore-dot-ghci"], List.append(&1, String, lw.ghc.flags(ws), ["*" ++ src, "+RTS", "-M2g", "-RTS"])), script)
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

# the module written, its ledger, and the items it kept (ims: the aliases
# of its package's earlier files, which it may import; fb: its laws were
# set aside, see lw.lost)
def lw.fin(+out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +fb: Bool, +g: F.Gs, +ps: List<&2, Pl>) -> IO(List<&2, T.BItem>):
  +its = lw.gs.its(g)
  do IO<List<&2, T.BItem>>:
    F.fd.module.write(F.fd.wrote(pkg, its), path, F.fd.render(file, m, ims, its))
    S.add(out ++ "/ledger.tsv", lw.cat(lw.ledger.ok(its, its, file, ps, F.fd.bpick(fb, S.b("nolaw:law-gate-failed"), Nil{})), lw.ledger.out(lw.gs.out(g), file)))
    return its

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

def lw.after(lost: Bool, +bend: String, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +try: String, +g0: F.Gs, +g2: F.Gs, +ps: List<&2, Pl>) -> IO(List<&2, T.BItem>):
  match lost:
    case True{}:
      do IO<List<&2, T.BItem>>:
        g1 : F.Gs <- F.fd.gate(1n+List.length(&2, T.BItem, lw.gs.its(g0)), g0, bend, try, file, m, ims)
        lw.fin(out, file, m, ims, pkg, path, True{}, g1, ps)
    case False{}:
      lw.fin(out, file, m, ims, pkg, path, False{}, g2, ps)

# The gate, once: the fold's defs (g0, before any check) and the laws GHC's
# answers give, together.  A def Bend refuses goes with its laws and what
# uses it; a law Bend refuses takes its def out (law:).  So a module whose
# defs and laws all hold costs one check.
def lw.laws2(+rounds: Nat, +bend: String, +out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +path: String, +try: String, +g0: F.Gs, +ps: List<&2, Pl>, +laws: List<&2, T.BItem>) -> IO(List<&2, T.BItem>):
  +good = lw.good(laws)
  +g1 = lw.start(g0, good, lw.bad(laws))
  +n = List.length(&2, T.BItem, lw.gs.its(g1))
  do IO<List<&2, T.BItem>>:
    +g2 : F.Gs <- lw.gate(Bool.pick(Nat, Nat.is_eq(rounds, 0n), 1n+n, rounds), lw.done.if(Nat.is_eq(n, 0n), g1), bend, try, file, m, ims)
    lw.after(lw.lost(Bool.not(List.is_empty(&2, T.BItem, good)), g0, g2), bend, out, file, m, ims, pkg, path, try, g0, g2, ps)

# GHC's answers for the fold's defs (g0, before any check), then the gate
def lw.laws(+rounds: Nat, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +xs: List<&2, X.Sx>, tbs: List<&2, F.Tb>, +path: String, +try: String, +g0: F.Gs) -> IO(List<&2, T.BItem>):
  +le = {Le{m, lw.syns(xs), Nil{}} : Le}
  +dds = lw.dds(xs)
  +ps = lw.plans(tbs, lw.gs.its(g0), le, dds, m)
  do IO<List<&2, T.BItem>>:
    txt : List<&2, U32> <- lw.ghc.run(lw.any.pl(ps), ghc, S.str(lw.src(xs)), out ++ "/" ++ S.str(base) ++ ".ghci", out ++ "/" ++ S.str(base) ++ ".ghc", lw.script(m, dds, ps))
    lw.laws2(rounds, bend, out, file, m, ims, pkg, path, try, g0, ps, lw.items(ps, lw.ols(S.split(txt, 10))))

# a module: fold it as Fold.bend does, ask GHC for its defs' laws, and gate
# the defs and laws together (px: what its package's modules before it
# gave, F.fd.px0() for a module alone); the package after it
def lw.module(+rounds: Nat, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, bytes: List<&2, U32>, +pkg: Bool, +px: F.Px) -> IO(F.Px):
  +xs = X.tsx.read(bytes)
  +m = V.sv.modname(xs)
  +tbs = F.fd.tbs(xs)
  +cs = F.fd.ctrs(xs)
  +ds = F.fd.dfs(tbs)
  +env = F.fd.syns(Nat.add(F.fd.nsyn(xs), List.length(&2, F.Sy, F.fd.px.sy(px))), xs, F.fd.env0(m, cs, ds, px))
  +g2 = F.fd.tpl.settle(F.fd.allgots(xs, tbs, env), F.fd.px.tfs(px))
  +gs = F.fd.tpl.fin(g2, List.append(&2, F.Tf, F.fd.tfs(g2), F.fd.px.tfs(px)))
  +its = F.fd.got.items(gs)
  +ims = F.fd.ims(px)
  +path = out ++ "/" ++ S.str(base) ++ ".bend"
  +try = out ++ "/" ++ S.str(base) ++ "_try.bend"
  do IO<F.Px>:
    F.fd.hsprelude.write(out)
    +kept : List<&2, T.BItem> <- lw.laws(rounds, bend, ghc, out, file, base, m, ims, pkg, xs, tbs, path, try, F.fd.predrop(its, F.fd.got.outs(gs)))
    return F.fd.px.next(pkg, px, m, base, xs, gs, F.fd.tfs(g2), cs, ds, kept)

def lw.run(xs: List<String>, +rounds: Nat, +bend: String, +ghc: String, +out: String, +pkg: Bool, +px: F.Px) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +p2 : F.Px <- lw.module(rounds, bend, ghc, out, S.b(f), F.fd.base(S.b(f)), bytes, pkg, px)
        lw.run(t, rounds, bend, ghc, out, pkg, p2)

def lw.main.go(pkg: Bool, args: List<String>, +rounds: Nat, +bend: String, +ghc: String) -> IO(Unit):
  match args:
    case out <> files:
      lw.run(files, rounds, bend, ghc, out, pkg, F.fd.px0())
    case Nil{}:
      IO.print("usage: law [--package] OUT FILE.sexp...  (BEND: the bend to check with, GHC: the ghc and any flags for it)")

def lw.main.pkg(pkg: Bool, a: String, rest: List<String>, +rounds: Nat, +bend: String, +ghc: String) -> IO(Unit):
  match pkg:
    case True{}:
      lw.main.go(True{}, rest, rounds, bend, ghc)
    case False{}:
      lw.main.go(False{}, a <> rest, rounds, bend, ghc)

# `law OUT FILE...` takes each module alone; `law --package OUT FILE...`
# one package's modules in dependency order (hs-export --package's
# modules.txt), each using what the ones before it kept (GHC then needs the
# package's -i and -package-db after the ghc)
def lw.main(args: List<String>, +rounds: Nat, +bend: String, +ghc: String) -> IO(Unit):
  match args:
    case +a <> rest:
      lw.main.pkg(S.eq(S.b(a), S.b("--package")), a, rest, rounds, bend, ghc)
    case Nil{}:
      lw.main.go(False{}, Nil{}, rounds, bend, ghc)

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    bend : String <- S.env("BEND", "bend")
    ghc : String <- S.env("GHC", "ghc")
    rounds : Nat <- S.env.nat("FOLD_ROUNDS", 0n)
    lw.main(List.tail(&1, String, argv), rounds, bend, ghc)
