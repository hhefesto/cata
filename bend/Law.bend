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
  HyMap{k: Hy, v: Hy}
  HySet{k: Hy}
  HyFix{f: Hy}
  HyCof{f: Hy, a: Hy}
  HyState{lazy: Bool, s: Hy}
  HyExs{e: Hy, lazy: Bool, s: Hy, a: Hy}
  HyStA{lazy: Bool, s: Hy, a: Hy}
  HyPc{a: Hy}
  HyPin{}
  HyW8{}
  HyDig{}
  HyRat{}
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
  BkMap{}
  BkSet{}
  BkFix{}
  BkCof{}
  BkShowS{}
  BkExc{}
  BkStS{}
  BkStL{}
  BkPc{}
  BkPct{}
  BkW8{}
  BkDig{}
  BkRat{}
  BkNone{}

type BkE is Data:
  BkE{k: String, v: Bk}

def lw.bktab() -> List<&2, BkE>:
  [BkE{"GHC.Types.Int", BkInt{}}, BkE{"GHC.Num.Integer.Integer", BkInteger{}}, BkE{"GHC.Num.Natural.Natural", BkNatural{}}, BkE{"GHC.Types.Bool", BkBool{}}, BkE{"GHC.Types.Char", BkChar{}}, BkE{"GHC.Types.List", BkList{}}, BkE{"GHC.Internal.Base.String", BkStr{}}, BkE{"GHC.Internal.IO.FilePath", BkStr{}}, BkE{"GHC.Internal.Maybe.Maybe", BkMaybe{}}, BkE{"GHC.Internal.Data.Either.Either", BkEither{}}, BkE{"GHC.Tuple.Tuple2", BkT2{}}, BkE{"GHC.Tuple.Tuple3", BkT3{}}, BkE{"GHC.Tuple.Unit", BkUnit{}}, BkE{"GHC.Types.Ordering", BkCmp{}}, BkE{"HsPrelude.HsInt", BkHsInt{}}, BkE{"HsPrelude.HsInteger", BkHsInteger{}}, BkE{"Data.Map.Internal.Map", BkMap{}}, BkE{"Data.Set.Internal.Set", BkSet{}}, BkE{"Data.Fix.Fix", BkFix{}}, BkE{"Control.Comonad.Cofree.Cofree", BkCof{}}, BkE{"GHC.Internal.Show.ShowS", BkShowS{}}, BkE{"Control.Monad.Trans.Except.ExceptT", BkExc{}}, BkE{"Control.Monad.Trans.State.Strict.State", BkStS{}}, BkE{"Control.Monad.Trans.State.Lazy.State", BkStL{}}, BkE{"Text.Megaparsec.Parsec", BkPc{}}, BkE{"Text.Megaparsec.Internal.ParsecT", BkPct{}}, BkE{"GHC.Internal.Word.Word8", BkW8{}}, BkE{"HsPrelude.HsDigest", BkDig{}}, BkE{"HsPrelude.HsRational", BkRat{}}]

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
    case BkMap{} HyArgs{a, HyArgs{b, _}}:
      HyMap{a, b}
    case BkSet{} HyArgs{a, _}:
      HySet{a}
    case BkFix{} HyArgs{a, _}:
      HyFix{a}
    case BkCof{} HyArgs{a, HyArgs{b, _}}:
      HyCof{a, b}
    case BkShowS{} _:
      HyFun{HyList{HyChar{}}, HyList{HyChar{}}}
    case BkStS{} HyArgs{s, HyArgs{a, _}}:
      HyStA{False{}, s, a}
    case BkStS{} HyArgs{s, _}:
      HyState{False{}, s}
    case BkStL{} HyArgs{s, HyArgs{a, _}}:
      HyStA{True{}, s, a}
    case BkStL{} HyArgs{s, _}:
      HyState{True{}, s}
    case BkExc{} HyArgs{e, HyArgs{HyState{l, s}, HyArgs{a, _}}}:
      HyExs{e, l, s, a}
    case BkW8{} _:
      HyW8{}
    case BkDig{} _:
      HyDig{}
    case BkRat{} _:
      HyRat{}
    case BkPc{} HyArgs{e, HyArgs{s, HyArgs{a, _}}}:
      HyPc{a}
    case BkPct{} HyArgs{e, HyArgs{s, HyArgs{m, HyArgs{a, _}}}}:
      HyPc{a}
    case _ _:
      HyNo{lw.cat(S.b("type:"), key)}

# the module's type synonyms, and a type variable's instance
type Sy is Data:
  Sy{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, body: X.Sx}

type Sb is Data:
  Sb{v: List<&2, U32>, h: Hy}

# where a type is read: the module, its synonyms, the type variables bound,
# and the keys (M.T) of the data types of the package's modules before it
type Le is Data:
  Le{m: List<&2, U32>, syns: List<&2, Sy>, sub: List<&2, Sb>, pk: List<&2, List<&2, U32>>}

def lw.le.m(+le: Le) -> List<&2, U32>:
  match le:
    case Le{m, s, b, k}:
      m

def lw.le.syns(+le: Le) -> List<&2, Sy>:
  match le:
    case Le{m, s, b, k}:
      s

def lw.le.sub(+le: Le) -> List<&2, Sb>:
  match le:
    case Le{m, s, b, k}:
      b

def lw.le.pk(+le: Le) -> List<&2, List<&2, U32>>:
  match le:
    case Le{m, s, b, k}:
      k

def lw.le.with(le: Le, sub: List<&2, Sb>) -> Le:
  match le:
    case Le{m, s, b, k}:
      Le{m, s, sub, k}

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
  HmExt{m: Hm, ext: Hy}
  HmFun{a: X.Sx, b: X.Sx}
  HmIn{t: X.Sx}
  HmChain{x: X.Sx}
  HmNo{why: List<&2, U32>}

# a synonym by its name in the module, another module's by its key M.T
def lw.syn.pick(own: Bool, ss: List<&2, Sy>, +n: List<&2, U32>, +key: List<&2, U32>) -> Maybe<&2, Sy>:
  match own:
    case True{}:
      lw.syn.find(ss, n)
    case False{}:
      lw.syn.find(ss, key)

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
  +key = lw.cat3(mod, [46], name)
  lw.syn.of(lw.syn.pick(own, lw.le.syns(le), name, key), own, key, name, lw.drop3(x))

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

# a type of another module: one of the package's data types is a user type
# by its key M.T, else one of Base's
def lw.tc.pk(imp: Bool, +key: List<&2, U32>, args: Hy) -> Hy:
  match imp:
    case True{}:
      HyUser{key, args}
    case False{}:
      lw.base(lw.bk.find(lw.bktab(), key), key, args)

def lw.tc(own: Bool, imp: Bool, +key: List<&2, U32>, name: List<&2, U32>, args: Hy) -> Hy:
  match own:
    case True{}:
      HyUser{name, args}
    case False{}:
      lw.tc.pk(imp, key, args)

# a spine's elements past the first n (a synonym's arguments past its
# parameters)
def lw.sx.drop(n: Nat, +x: X.Sx) -> X.Sx:
  match n:
    case 0n:
      x
    case 1n+p:
      lw.sx.drop(p, X.tsx.args(x))

# two spines, one after the other
def lw.hy.cat(h: Hy, x: Hy) -> Hy:
  match h:
    case HyArgs{a, r}:
      HyArgs{a, lw.hy.cat(r, x)}
    case _:
      x

# a type tree as an Hy: synonyms of the module expanded, every type
# variable its instance (fuel: synonyms may name synonyms)
def lw.hy(fuel: Nat, +le: Le, m: Hm) -> Hy:
  match fuel m:
    case 0n _:
      HyNo{S.b("type-depth")}
    case 1n+p HmTv{n}:
      lw.sub.find(lw.le.sub(le), n)
    case 1n+p HmTc{own, +key, name, args}:
      lw.tc(own, S.mem(key, lw.le.pk(le)), key, name, lw.hy(p, le, HmChain{args}))
    case 1n+(+p) HmSyn{+tvs, body, +args}:
      +le2 = lw.le.with(le, lw.zip.sub(tvs, lw.hy(p, le, HmChain{args})))
      +ext = lw.hy(p, le, HmChain{lw.sx.drop(List.length(&2, List<&2, U32>, tvs), args)})
      lw.hy(p, le2, HmExt{lw.hm(le2, body), ext})
    case 1n+p HmExt{HmTc{own, +key, name, args}, ext}:
      lw.tc(own, S.mem(key, lw.le.pk(le)), key, name, lw.hy.cat(lw.hy(p, le, HmChain{args}), ext))
    case 1n+p HmExt{m2, HyANil{}}:
      lw.hy(p, le, m2)
    case 1n+p HmExt{m2, ext}:
      HyNo{S.b("type:synonym-applied")}
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
      lw.first(lw.notype(a), lw.notype(b))
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
    case HyMap{a, b}:
      lw.first(lw.notype(a), lw.notype(b))
    case HySet{a}:
      lw.notype(a)
    case HyFix{HyUser{n, args}}:
      lw.notype(args)
    case HyFix{f}:
      lw.first(lw.notype(f), S.b("functor"))
    case HyCof{HyUser{n, args}, a}:
      lw.first(lw.notype(args), lw.notype(a))
    case HyCof{f, a}:
      lw.first(lw.notype(f), S.b("functor"))
    case HyArgs{a, r}:
      lw.first(lw.notype(a), lw.notype(r))
    case HyState{l, s}:
      S.b("type:Control.Monad.Trans.State.State")
    case HyExs{e, l, s, a}:
      S.b("type:Control.Monad.Trans.Except.ExceptT")
    case HyStA{l, s, a}:
      S.b("type:Control.Monad.Trans.State.State")
    case HyPc{a}:
      lw.notype(a)
    case _:
      Nil{}

# A def's type with its answer an ExceptT e (State s) a as what running it
# answers: a function of the state, to Either e a and the state after (the
# prelude's hs.exs, as cata's Bend has it), so the laws' inputs take a state;
# a parser's as what running it on an input answers (HsPc.answer): the
# error's text, or the answer and the offset after it
def lw.flat(h: Hy) -> Hy:
  match h:
    case HyFun{a, b}:
      HyFun{a, lw.flat(b)}
    case HyExs{e, l, +s, a}:
      HyFun{s, HyT2{HyEither{e, a}, s}}
    case HyStA{l, +s, a}:
      HyFun{s, HyT2{a, s}}
    case HyPc{a}:
      HyFun{HyPin{}, HyEither{HyList{HyChar{}}, HyT2{a, HyInt{S.b("LawP.Int")}}}}
    case r:
      r

# what runs a def's answer: nothing, State (its laziness) under ExceptT, a
# parser (its answer's type)
type Rn is Data:
  RnNo{}
  RnExs{lazy: Bool}
  RnSt{lazy: Bool}
  RnPc{a: Hy}

def lw.run.of(h: Hy) -> Rn:
  match h:
    case HyExs{e, l, s, a}:
      RnExs{l}
    case HyStA{l, s, a}:
      RnSt{l}
    case HyPc{a}:
      RnPc{a}
    case _:
      RnNo{}

# GHCi's names x1 .. xn
def lw.xs(n: Nat, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      32 <> 120 <> lw.cat(lw.nshow(k), lw.xs(p, 1n+k))

# the def run, in GHCi: (\\lawG x1 .. xn lawS -> runState (runExceptT
# (lawG x1 .. xn)) lawS) applied to it, State's Strict or Lazy
def lw.exs.run(lazy: Bool, +n: Nat) -> List<&2, U32>:
  +xs = lw.xs(n, 1n)
  +rs = F.fd.bpick(lazy, S.b("Control.Monad.Trans.State.Lazy.runState"), S.b("Control.Monad.Trans.State.Strict.runState"))
  40 <> 92 <> lw.cat3(S.b("lawG"), xs, lw.cat3(S.b(" lawS -> "), rs, lw.cat3(S.b(" (Control.Monad.Trans.Except.runExceptT (lawG"), xs, S.b(")) lawS) ("))))

# the same at State alone
def lw.st.run(lazy: Bool, +n: Nat) -> List<&2, U32>:
  +xs = lw.xs(n, 1n)
  +rs = F.fd.bpick(lazy, S.b("Control.Monad.Trans.State.Lazy.runState"), S.b("Control.Monad.Trans.State.Strict.runState"))
  40 <> 92 <> lw.cat3(S.b("lawG"), xs, lw.cat3(S.b(" lawS -> "), rs, lw.cat3(S.b(" (lawG"), xs, S.b(") lawS) ("))))

# a parser run in GHCi on an input: the error's text, or the answer and the
# offset after it
def lw.pc.run(+n: Nat) -> List<&2, U32>:
  +xs = lw.xs(n, 1n)
  40 <> 92 <> lw.cat3(S.b("lawG"), xs, lw.cat3(S.b(" lawS -> LawP.either (\\lawE -> LawP.Left (Text.Megaparsec.errorBundlePretty lawE)) LawP.Right (Text.Megaparsec.runParser ((\\lawX lawO -> (lawX, lawO)) LawP.<$> lawG"), xs, S.b(" LawP.<*> Text.Megaparsec.getOffset) \"\" lawS)) (")))

def lw.nargs(h: Hy) -> Nat:
  match h:
    case HyArgs{a, r}:
      1n+lw.nargs(r)
    case _:
      0n

# Where a data type is: GHCi's module for its names, its name, and the
# prefix of its constructors' Bend names (an import's alias M_N and a dot,
# none for the module's own). A type of the module is found by its name, one
# of the package's modules before it by its key M.T.
type Dw is Data:
  Dw{hm: List<&2, U32>, ty: List<&2, U32>, pre: List<&2, U32>}

def lw.dw.hm(+w: Dw) -> List<&2, U32>:
  match w:
    case Dw{hm, ty, pre}:
      hm

def lw.dw.ty(+w: Dw) -> List<&2, U32>:
  match w:
    case Dw{hm, ty, pre}:
      ty

def lw.dw.pre(+w: Dw) -> List<&2, U32>:
  match w:
    case Dw{hm, ty, pre}:
      pre

# a key's last part (r: the key reversed)
def lw.key.nm(r: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Nil{}:
      acc
    case 46 <> t:
      acc
    case c <> t:
      lw.key.nm(t, c <> acc)

# what is before a key's last dot, reversed (none without a dot)
def lw.key.md(r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Nil{}:
      Nil{}
    case 46 <> t:
      t
    case c <> t:
      lw.key.md(t)

# a module's alias in Bend: its dots underscores (Telomare.IR.Loc is
# Telomare_IR_Loc)
def lw.alias(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case 46 <> t:
      95 <> lw.alias(t)
    case c <> t:
      c <> lw.alias(t)

def lw.dw.of(md: List<&2, U32>, m: List<&2, U32>, +r: List<&2, U32>) -> Dw:
  match md:
    case Nil{}:
      Dw{m, lw.key.nm(r, Nil{}), Nil{}}
    case h <> t:
      +x = List.reverse(&2, U32, h <> t)
      Dw{x, lw.key.nm(r, Nil{}), lw.cat(lw.alias(x), [46])}

def lw.dw(m: List<&2, U32>, n: List<&2, U32>) -> Dw:
  +r = List.reverse(&2, U32, n)
  lw.dw.of(lw.key.md(r), m, r)

# whether a key is GHC's Int (h's Map Int may be an IntMap, which Spec reads
# as a Map: its type is a wildcard in h's script; tests/back/lawg.sed writes
# G's, a Map)
def lw.isint(k: Hy) -> Bool:
  match k:
    case HyInt{s}:
      S.eq(s, S.b("LawP.Int"))
    case HyNat{s}:
      S.eq(s, S.b("LawP.Int"))
    case _:
      False{}

def lw.map.ty(i: Bool, k: List<&2, U32>, +v: List<&2, U32>) -> List<&2, U32>:
  match i:
    case True{}:
      lw.cat3(S.b("(_ "), v, [41])
    case False{}:
      lw.cat3(S.b("(LawM.Map "), k, 32 <> lw.cat(v, [41]))

def lw.set.ty(i: Bool, k: List<&2, U32>) -> List<&2, U32>:
  match i:
    case True{}:
      S.b("(_)")
    case False{}:
      lw.cat3(S.b("(LawS.Set "), k, [41])

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
      +w = lw.dw(m, n)
      40 <> lw.cat3(lw.dw.hm(w), 46 <> lw.dw.ty(w), lw.cat(lw.hs.ty(args, m), [41]))
    case HyMap{+a, b}:
      lw.map.ty(lw.isint(a), lw.hs.ty(a, m), lw.hs.ty(b, m))
    case HySet{+a}:
      lw.set.ty(lw.isint(a), lw.hs.ty(a, m))
    case HyFix{f}:
      lw.cat3(S.b("(Data.Fix.Fix "), lw.hs.ty(f, m), [41])
    case HyCof{f, a}:
      lw.cat3(S.b("(Control.Comonad.Cofree.Cofree "), lw.hs.ty(f, m), 32 <> lw.cat(lw.hs.ty(a, m), [41]))
    case HyState{l, s}:
      lw.cat3(F.fd.bpick(l, S.b("(Control.Monad.Trans.State.Lazy.State "), S.b("(Control.Monad.Trans.State.Strict.State ")), lw.hs.ty(s, m), [41])
    case HyExs{e, l, s, a}:
      +st = lw.cat3(F.fd.bpick(l, S.b("(Control.Monad.Trans.State.Lazy.State "), S.b("(Control.Monad.Trans.State.Strict.State ")), lw.hs.ty(s, m), [41])
      lw.cat3(S.b("(Control.Monad.Trans.Except.ExceptT "), lw.hs.ty(e, m), 32 <> lw.cat3(st, [32], lw.cat(lw.hs.ty(a, m), [41])))
    case HyStA{l, s, a}:
      lw.cat3(F.fd.bpick(l, S.b("(Control.Monad.Trans.State.Lazy.State "), S.b("(Control.Monad.Trans.State.Strict.State ")), lw.hs.ty(s, m), 32 <> lw.cat(lw.hs.ty(a, m), [41]))
    case HyPc{a}:
      lw.cat3(S.b("(Text.Megaparsec.Parsec Data.Void.Void LawP.String "), lw.hs.ty(a, m), [41])
    case HyPin{}:
      S.b("LawP.String")
    case HyW8{}:
      S.b("LawW.Word8")
    case HyDig{}:
      S.b("(Crypto.Hash.Digest Crypto.Hash.SHA256)")
    case HyRat{}:
      S.b("LawP.Rational")
    case HyFun{a, b}:
      40 <> lw.cat3(lw.hs.ty(a, m), S.b(" -> "), lw.cat(lw.hs.ty(b, m), [41]))
    case HyArgs{a, r}:
      32 <> lw.cat(lw.hs.ty(a, m), lw.hs.ty(r, m))
    case _:
      Nil{}

# a spine with x at its end (a functor's parameters and the recursion's)
def lw.bt.snoc(s: T.Bt, x: T.Bt) -> T.Bt:
  match s:
    case T.BtArgs{a, r}:
      T.BtArgs{a, lw.bt.snoc(r, x)}
    case _:
      T.BtArgs{x, T.BtANil{}}

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
      +w = lw.dw(Nil{}, n)
      T.BtTyApp{lw.cat(lw.dw.pre(w), F.fd.tyname(lw.dw.ty(w))), lw.bty(args)}
    case HyMap{a, b}:
      T.BtTyApp{S.b("HsPrelude.HsMap"), T.BtArgs{lw.bty(a), T.BtArgs{lw.bty(b), T.BtANil{}}}}
    case HySet{a}:
      T.BtTyApp{S.b("HsPrelude.HsSet"), T.BtArgs{lw.bty(a), T.BtANil{}}}
    case HyFix{HyUser{n, args}}:
      +w = lw.dw(Nil{}, n)
      T.BtTyApp{S.b("HsPrelude.Fix"), T.BtArgs{T.BtLam{T.BmLive{}, S.b("r_"), T.BtTyApp{lw.cat(lw.dw.pre(w), F.fd.tyname(lw.dw.ty(w))), lw.bt.snoc(lw.bty(args), T.BtVar{S.b("r_")})}}, T.BtANil{}}}
    case HyCof{HyUser{n, args}, a}:
      +w = lw.dw(Nil{}, n)
      T.BtTyApp{S.b("HsPrelude.Cofree"), T.BtArgs{T.BtLam{T.BmLive{}, S.b("r_"), T.BtTyApp{lw.cat(lw.dw.pre(w), F.fd.tyname(lw.dw.ty(w))), lw.bt.snoc(lw.bty(args), T.BtVar{S.b("r_")})}}, T.BtArgs{lw.bty(a), T.BtANil{}}}}
    case HyW8{}:
      F.fd.ty0("U32")
    case HyDig{}:
      F.fd.ty0("HsPrelude.HsDigest")
    case HyRat{}:
      F.fd.ty0("HsPrelude.HsRational")
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

def lw.dds.q(+m: List<&2, U32>, ds: List<&2, Dd>) -> List<&2, Dd>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{n, tvs, cs} <> t:
      Dd{lw.cat3(m, [46], n), tvs, cs} <> lw.dds.q(m, t)

# A package's synonyms are kept with its data types: (synonym BODY) for the
# constructors
def lw.syns.q(+m: List<&2, U32>, ss: List<&2, Sy>) -> List<&2, Dd>:
  match ss:
    case Nil{}:
      Nil{}
    case Sy{n, tvs, b} <> t:
      Dd{lw.cat3(m, [46], n), tvs, X.SxCons{X.SxAtom{S.b("synonym")}, X.SxCons{b, X.SxNil{}}}} <> lw.syns.q(m, t)

def lw.dd.syn(cs: X.Sx) -> Maybe<&2, X.Sx>:
  match cs:
    case X.SxCons{X.SxAtom{a}, X.SxCons{b, t}}:
      Some{b}
    case _:
      None{}

def lw.pu.put(m: Maybe<&2, X.Sx>, d: Dd, ds: List<&2, Dd>) -> List<&2, Dd>:
  match m:
    case Some{b}:
      ds
    case None{}:
      d <> ds

# the data types, and the synonyms, of a package's
def lw.pu.dds(ds: List<&2, Dd>) -> List<&2, Dd>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{n, tvs, +cs} <> t:
      lw.pu.put(lw.dd.syn(cs), Dd{n, tvs, cs}, lw.pu.dds(t))

def lw.pu.put.sy(m: Maybe<&2, X.Sx>, n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, ss: List<&2, Sy>) -> List<&2, Sy>:
  match m:
    case Some{b}:
      Sy{n, tvs, b} <> ss
    case None{}:
      ss

def lw.pu.syns(ds: List<&2, Dd>) -> List<&2, Sy>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{n, tvs, cs} <> t:
      lw.pu.put.sy(lw.dd.syn(cs), n, tvs, lw.pu.syns(t))

def lw.dd.keys(ds: List<&2, Dd>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      Nil{}
    case Dd{n, tvs, cs} <> t:
      n <> lw.dd.keys(t)


def lw.mods.add(c: Bool, s: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match c:
    case True{}:
      s <> acc
    case False{}:
      acc
# The modules whose types a tree names, (tc MOD NAME ..)
def lw.mods.go(x: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+s}, t}}:
      lw.mods.go(t, lw.mods.add(Bool.and(S.eq(a, S.b("tc")), Bool.not(S.mem(s, acc))), s, acc))
    case X.SxCons{h, t}:
      lw.mods.go(t, lw.mods.go(h, acc))
    case _:
      acc

def lw.mods.xs(xs: List<&2, X.Sx>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      lw.mods.xs(t, lw.mods.go(x, acc))

def lw.mods.dds(ds: List<&2, Dd>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      acc
    case Dd{n, tvs, cs} <> t:
      lw.mods.dds(t, lw.mods.go(cs, acc))

def lw.pd.if(u: Bool, d: Dd, acc: List<&2, Dd>) -> List<&2, Dd>:
  match u:
    case True{}:
      d <> acc
    case False{}:
      acc

# the package's types of the modules ms
def lw.pd.sel(pd: List<&2, Dd>, +ms: List<&2, List<&2, U32>>) -> List<&2, Dd>:
  match pd:
    case Nil{}:
      Nil{}
    case Dd{+n, tvs, cs} <> t:
      lw.pd.if(S.mem(List.reverse(&2, U32, lw.key.md(List.reverse(&2, U32, n))), ms), Dd{n, tvs, cs}, lw.pd.sel(t, ms))

# the package's types a module can name: of the modules its own types name,
# and theirs' fields (fuel rounds)
def lw.pd.use(fuel: Nat, +pd: List<&2, Dd>, +ms: List<&2, List<&2, U32>>) -> List<&2, Dd>:
  match fuel:
    case 0n:
      lw.pd.sel(pd, ms)
    case 1n+p:
      lw.pd.use(p, pd, lw.mods.dds(lw.pd.sel(pd, ms), ms))

# a package's next module sees this one's data types and synonyms (a module
# alone: none)
def lw.pd.next(pkg: Bool, +m: List<&2, U32>, +xs: List<&2, X.Sx>, pd: List<&2, Dd>) -> List<&2, Dd>:
  match pkg:
    case True{}:
      List.append(&2, Dd, lw.dds.q(m, lw.dds(xs)), List.append(&2, Dd, lw.syns.q(m, lw.syns(xs)), pd))
    case False{}:
      pd

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

def lw.ck(+w: Dw, +le: Le, +c: X.Sx) -> Ck:
  +n = V.sv.str(c, 1n)
  +ex = V.sv.at(c, 4n)
  Ck{lw.hsname(lw.dw.hm(w), n), lw.cat(lw.dw.pre(w), F.fd.cname(lw.dw.ty(w), n)), lw.ck.fs(Bool.not(Nat.is_eq(Nat.add(X.tsx.nat(V.sv.at(ex, 1n)), X.tsx.nat(V.sv.at(ex, 2n))), 0n)), le, V.sv.at(c, 3n))}

def lw.cks(+w: Dw, +le: Le, cs: X.Sx) -> List<&2, Ck>:
  match cs:
    case X.SxCons{+c, t}:
      lw.ck(w, le, c) <> lw.cks(w, le, t)
    case _:
      Nil{}

# a type's constructors at the arguments args
def lw.cks.of(found: Maybe<&2, Dd>, +le: Le, args: Hy) -> List<&2, Ck>:
  match found:
    case Some{Dd{n, tvs, cs}}:
      lw.cks(lw.dw(lw.le.m(le), n), lw.le.with(le, lw.zip.sub(tvs, args)), cs)
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

def lw.flats.put(c: Bool, x: Ck, xs: List<&2, Ck>) -> List<&2, Ck>:
  match c:
    case True{}:
      x <> xs
    case False{}:
      xs

# a type with values that need none of the package's types
def lw.hy.flat(h: Hy) -> Bool:
  match h:
    case HyUser{n, args}:
      False{}
    case HyFix{f}:
      False{}
    case HyCof{f, a}:
      False{}
    case HyNo{w}:
      False{}
    case HyEither{a, b}:
      Bool.or(lw.hy.flat(a), lw.hy.flat(b))
    case HyT2{a, b}:
      Bool.and(lw.hy.flat(a), lw.hy.flat(b))
    case HyT3{a, b, c}:
      Bool.and(lw.hy.flat(a), Bool.and(lw.hy.flat(b), lw.hy.flat(c)))
    case HyFun{a, b}:
      lw.hy.flat(b)
    case HyArgs{a, r}:
      Bool.and(lw.hy.flat(a), lw.hy.flat(r))
    case _:
      True{}

def lw.flats(cs: List<&2, Ck>) -> List<&2, Ck>:
  match cs:
    case Ck{hs, b, +fs} <> t:
      lw.flats.put(lw.hy.flat(fs), Ck{hs, b, fs}, lw.flats(t))
    case Nil{}:
      Nil{}

# no constructor without fields: those whose fields are base types, else the
# first
def lw.zone2(fl: List<&2, Ck>, cs: List<&2, Ck>) -> List<&2, Ck>:
  match fl cs:
    case h <> t _:
      h <> t
    case Nil{} h <> t:
      [h]
    case Nil{} Nil{}:
      Nil{}

def lw.zone(nu: List<&2, Ck>, +cs: List<&2, Ck>) -> List<&2, Ck>:
  match nu:
    case h <> t:
      h <> t
    case Nil{}:
      lw.zone2(lw.flats(cs), cs)

# below depth 3 only the constructors with no fields, where a type has some;
# a type with none keeps a constructor or two, three times (a record of
# records), then has no value
def lw.atd(d: Nat, +cs: List<&2, Ck>) -> List<&2, Ck>:
  match d:
    case 0n:
      lw.nullary(cs)
    case 1n+0n:
      lw.zone(lw.nullary(cs), cs)
    case 1n+(1n+0n):
      lw.zone(lw.nullary(cs), cs)
    case 1n+(1n+(1n+0n)):
      lw.zone(lw.nullary(cs), cs)
    case 1n+(1n+(1n+(1n+p))):
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
  VaMap{st: Bool, xs: Va}
  VaFn{n: Nat, v: Va}
  VaPin{s: List<&2, U32>}
  VaPc{eat: Bool, ty: T.Bt, v: Va}
  VaW8{n: Nat}
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

# a parser's values: v after the character a, or at once
def lw.pcs(+ty: T.Bt, vs: List<&2, Va>) -> List<&2, Va>:
  match vs:
    case +v <> t:
      VaPc{True{}, ty, v} <> VaPc{False{}, ty, v} <> lw.pcs(ty, t)
    case Nil{}:
      Nil{}

# a byte; a digest (its 32 bytes, all of them b); a rational n % d
def lw.w8s() -> List<&2, Va>:
  [VaW8{0n}, VaW8{1n}, VaW8{97n}, VaW8{255n}]

def lw.dig(+b: Nat) -> Va:
  VaCon{S.b("lawDig"), S.b("HsPrelude.HsDigest.D"), VaArgs{VaList{lw.spine(List.replicate(Va, 32n, VaW8{b}))}, VaANil{}}}

def lw.digs() -> List<&2, Va>:
  [lw.dig(0n), lw.dig(1n), lw.dig(255n)]

def lw.rat(neg: Bool, n: Nat, d: Nat) -> Va:
  VaCon{S.b("lawRat"), S.b("HsPrelude.HsRational"), VaArgs{VaInt{neg, n}, VaArgs{VaNat{d}, VaANil{}}}}

def lw.rats() -> List<&2, Va>:
  [lw.rat(False{}, 0n, 1n), lw.rat(False{}, 1n, 1n), lw.rat(False{}, 1n, 2n), lw.rat(True{}, 2n, 3n), lw.rat(False{}, 3n, 1n)]

# a parser's inputs: a program's shapes, small
def lw.pins.of(xs: List<String>) -> List<&2, Va>:
  match xs:
    case h <> t:
      VaPin{S.b(h)} <> lw.pins.of(t)
    case Nil{}:
      Nil{}

# each value as a spine of one
def lw.tup1(xs: List<&2, Va>) -> List<&2, Va>:
  match xs:
    case x <> t:
      VaTup{VaArgs{x, VaANil{}}} <> lw.tup1(t)
    case Nil{}:
      Nil{}

def lw.pins() -> List<&2, Va>:
  lw.pins.of(["", "a1 ", "12", "(a, 1)", "[a, 1]", "\"a b\"", "\\a -> a", "if a then b else c", "let a = 1\n    b = 2\nin a b", "case a of\n  b -> c\n  _ -> 1", "a = 1\nb = a\n", "{a, b, c}", "$2", "# a", "import A", "a b (c d)"])

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

# Haskell's order of two values where it is known here (numbers, characters,
# and lists and tuples of them; sp: two spines, in order)
type Cm is Data:
  CmLt{}
  CmEq{}
  CmGt{}
  CmNo{}

def lw.cm.nat(a: Nat, b: Nat) -> Cm:
  match a b:
    case 0n 0n:
      CmEq{}
    case 0n 1n+q:
      CmLt{}
    case 1n+p 0n:
      CmGt{}
    case 1n+p 1n+q:
      lw.cm.nat(p, q)

def lw.cm.int(na: Bool, a: Nat, nb: Bool, b: Nat) -> Cm:
  match na nb:
    case False{} False{}:
      lw.cm.nat(a, b)
    case True{} True{}:
      lw.cm.nat(b, a)
    case True{} False{}:
      CmLt{}
    case False{} True{}:
      CmGt{}

def lw.cm.lex(h: Cm, t: Cm) -> Cm:
  match h:
    case CmEq{}:
      t
    case d:
      d

def lw.cm(a: Va, b: Va, sp: Bool) -> Cm:
  match a b sp:
    case VaNat{x} VaNat{y} False{}:
      lw.cm.nat(x, y)
    case VaInt{na, x} VaInt{nb, y} False{}:
      lw.cm.int(na, x, nb, y)
    case VaChar{x} VaChar{y} False{}:
      lw.cm.nat(x, y)
    case VaList{x} VaList{y} False{}:
      lw.cm(x, y, True{})
    case VaTup{x} VaTup{y} False{}:
      lw.cm(x, y, True{})
    case VaANil{} VaANil{} True{}:
      CmEq{}
    case VaANil{} VaArgs{y, s} True{}:
      CmLt{}
    case VaArgs{x, r} VaANil{} True{}:
      CmGt{}
    case VaArgs{x, r} VaArgs{y, s} True{}:
      lw.cm.lex(lw.cm(x, y, False{}), lw.cm(r, s, True{}))
    case _ _ _:
      CmNo{}

def lw.kv(k: Va, v: Va) -> Va:
  VaTup{VaArgs{k, VaArgs{v, VaANil{}}}}

def lw.mp(st: Bool, xs: List<&2, Va>) -> Va:
  VaMap{st, lw.spine(xs)}

# a map (a set: st) of two entries, in their keys' order (none where it is
# not known)
def lw.mp2(c: Cm, st: Bool, a: Va, b: Va) -> List<&2, Va>:
  match c:
    case CmLt{}:
      [lw.mp(st, [a, b])]
    case CmGt{}:
      [lw.mp(st, [b, a])]
    case _:
      Nil{}

# Data.Map's maps of the keys ks and the values vs, smallest first (Bend's
# HsMap: the entries in ascending order of the key)
def lw.maps(ks: List<&2, Va>, vs: List<&2, Va>) -> List<&2, Va>:
  match ks vs:
    case +k0 <> +k1 <> r +v0 <> +v1 <> s:
      List.append(&2, Va, [lw.mp(False{}, Nil{}), lw.mp(False{}, [lw.kv(k0, v0)]), lw.mp(False{}, [lw.kv(k1, v1)]), lw.mp(False{}, [lw.kv(k0, v1)])], lw.mp2(lw.cm(k0, k1, False{}), False{}, lw.kv(k0, v0), lw.kv(k1, v1)))
    case +k0 <> r +v0 <> s:
      [lw.mp(False{}, Nil{}), lw.mp(False{}, [lw.kv(k0, v0)])]
    case _ _:
      [lw.mp(False{}, Nil{})]

def lw.sets(ks: List<&2, Va>) -> List<&2, Va>:
  match ks:
    case +k0 <> +k1 <> r:
      List.append(&2, Va, [lw.mp(True{}, Nil{}), lw.mp(True{}, [k0]), lw.mp(True{}, [k1])], lw.mp2(lw.cm(k0, k1, False{}), True{}, k0, k1))
    case +k0 <> r:
      [lw.mp(True{}, Nil{}), lw.mp(True{}, [k0])]
    case Nil{}:
      [lw.mp(True{}, Nil{})]

# a constructor at each tuple of its fields
def lw.mks(+hs: List<&2, U32>, +b: List<&2, U32>, xs: List<&2, Va>) -> List<&2, Va>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      List.append(&2, Va, lw.mk(hs, b, Some{x}), lw.mks(hs, b, t))

# A function input: the function of n arguments that answers v whatever
# they are (GHCi's \_ _ -> v, Bend's _ => _ => v), at two of its answer
# type's values
def lw.fn.n(h: Hy) -> Nat:
  match h:
    case HyFun{a, b}:
      1n+lw.fn.n(b)
    case _:
      0n

def lw.fns(+n: Nat, vs: List<&2, Va>) -> List<&2, Va>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      VaFn{n, v} <> lw.fns(n, t)

# a functor's type arguments and the recursion's (Fix f is f (Fix f))
def lw.hy.snoc(h: Hy, x: Hy) -> Hy:
  match h:
    case HyArgs{a, r}:
      HyArgs{a, lw.hy.snoc(r, x)}
    case _:
      HyArgs{x, HyANil{}}

# what to list: a type's values, the tuples of a spine of field types, or
# the k-th tuple of each constructor's fields
type Q is Data:
  QTy{h: Hy}
  QFields{fs: Hy}
  QCons{k: Nat, cs: List<&2, Ck>}

# the inputs of a type, smallest first; d: how many of the module's own
# types deep (lw.atd)
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
    case 1n+p QTy{HyPin{}}:
      lw.pins()
    case 1n+p QTy{HyPc{+a}}:
      lw.pcs(lw.bty(a), List.take(&2, Va, lw.vals(p, d, le, dds, QTy{a}), 2n))
    case 1n+p QTy{HyW8{}}:
      lw.w8s()
    case 1n+p QTy{HyDig{}}:
      lw.digs()
    case 1n+p QTy{HyRat{}}:
      lw.rats()
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
    case 1n+(+p) QTy{HyMap{a, b}}:
      lw.maps(lw.vals(p, d, le, dds, QTy{a}), lw.vals(p, d, le, dds, QTy{b}))
    case 1n+p QTy{HySet{a}}:
      lw.sets(lw.vals(p, d, le, dds, QTy{a}))
    case 1n+p QTy{HyFun{a, +b}}:
      lw.fns(1n+lw.fn.n(b), List.take(&2, Va, lw.vals(p, d, le, dds, QTy{lw.res(b)}), 2n))
    case 1n+p QTy{HyFix{HyUser{+n, +args}}}:
      lw.wrap1(S.b("lawFix"), S.b("HsPrelude.Fix.Fix"), lw.vals(p, d, le, dds, QTy{HyUser{n, lw.hy.snoc(args, HyFix{HyUser{n, args}})}}))
    case 1n+p QTy{HyCof{HyUser{+n, +args}, +a}}:
      lw.mks(S.b("lawCof"), S.b("HsPrelude.Cofree.Cofree"), lw.vals(p, d, le, dds, QFields{HyArgs{a, HyArgs{HyUser{n, lw.hy.snoc(args, HyCof{HyUser{n, args}, a})}, HyANil{}}}}))
    case 1n+(+p) QTy{HyUser{+n, args}}:
      +cs = lw.atd(d, lw.cks.of(lw.dd.find(dds, n), le, args))
      List.take(&2, Va, List.append(&2, Va, lw.vals(p, lw.dec(d), le, dds, QCons{0n, cs}), lw.vals(p, lw.dec(d), le, dds, QCons{1n, cs})), 6n)
    case 1n+p QTy{_}:
      Nil{}
    case 1n+p QFields{HyArgs{HyPin{}, HyANil{}}}:
      lw.tup1(lw.pins())
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
  VmMap{}
  VmSet{}

def lw.fn.us(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      95 <> 32 <> lw.fn.us(p)

def lw.fn.lam(n: Nat, b: T.Bt) -> T.Bt:
  match n:
    case 0n:
      b
    case 1n+p:
      T.BtLam{T.BmLive{}, S.b("_"), lw.fn.lam(p, b)}

# a value as GHCi reads it
# an integer input as GHCi reads it: -n in parentheses
def lw.va.int(neg: Bool, n: Nat) -> List<&2, U32>:
  match neg:
    case True{}:
      40 <> 45 <> lw.cat(lw.nshow(n), [41])
    case False{}:
      lw.nshow(n)

# a string as Haskell's literal
def lw.hs.lit(s: List<&2, U32>) -> List<&2, U32>:
  match s:
    case 10 <> t:
      92 <> 110 <> lw.hs.lit(t)
    case 34 <> t:
      92 <> 34 <> lw.hs.lit(t)
    case 92 <> t:
      92 <> 92 <> lw.hs.lit(t)
    case c <> t:
      c <> lw.hs.lit(t)
    case Nil{}:
      [34]

# a string as Bend's list of characters
def lw.bt.lit(s: List<&2, U32>) -> T.Bt:
  match s:
    case c <> t:
      T.BtCon{S.b("Con"), T.BtArgs{F.fd.char(U32.to_nat(c)), T.BtArgs{lw.bt.lit(t), T.BtANil{}}}}
    case Nil{}:
      F.fd.con0("Nil")

def lw.va.hs(v: Va, mode: Vm) -> List<&2, U32>:
  match v mode:
    case VaPin{s} _:
      34 <> lw.hs.lit(s)
    case VaPc{True{}, ty, v} _:
      40 <> lw.cat(lw.va.hs(v, VmVal{}), S.b(" LawP.<$ Text.Megaparsec.single 'a')"))
    case VaPc{False{}, ty, v} _:
      lw.cat3(S.b("(LawP.pure "), lw.va.hs(v, VmVal{}), [41])
    case VaW8{n} _:
      lw.nshow(n)
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
    case VaFn{+n, v} _:
      lw.cat3(S.b("(\\"), lw.fn.us(n), lw.cat3(S.b("-> "), lw.va.hs(v, VmVal{}), [41]))
    case VaMap{st, xs} _:
      40 <> lw.cat3(F.fd.bpick(st, S.b("lawSet "), S.b("lawMap ")), 91 <> lw.cat(lw.tail1(lw.va.hs(xs, VmComma{})), [93]), [41])
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
    case VaPin{s} _:
      F.fd.callS("HsPrelude.HsPc.st0", [F.fd.con0("Nil"), lw.bt.lit(s)])
    case VaPc{True{}, ty, v} _:
      F.fd.callS("HsPrelude.HsPc.const", [ty, F.fd.ty0("Char"), lw.va.bt(v, VmVal{}), F.fd.callS("HsPrelude.HsPc.char", [F.fd.char(97n)])])
    case VaPc{False{}, ty, v} _:
      F.fd.callS("HsPrelude.HsPc.pure", [ty, lw.va.bt(v, VmVal{})])
    case VaW8{n} _:
      T.BtVar{lw.nshow(n)}
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
    case VaFn{n, v} _:
      lw.fn.lam(n, lw.va.bt(v, VmVal{}))
    case VaMap{True{}, xs} _:
      lw.va.bt(xs, VmSet{})
    case VaMap{False{}, xs} _:
      lw.va.bt(xs, VmMap{})
    case VaArgs{VaTup{VaArgs{k, VaArgs{v, VaANil{}}}}, r} VmMap{}:
      T.BtCon{S.b("HsPrelude.HsMap.Bin"), T.BtArgs{lw.va.bt(k, VmVal{}), T.BtArgs{lw.va.bt(v, VmVal{}), T.BtArgs{lw.va.bt(r, VmMap{}), T.BtANil{}}}}}
    case VaANil{} VmMap{}:
      F.fd.con0("HsPrelude.HsMap.Tip")
    case VaArgs{k, r} VmSet{}:
      T.BtCon{S.b("HsPrelude.HsSet.Bin"), T.BtArgs{lw.va.bt(k, VmVal{}), T.BtArgs{lw.va.bt(r, VmSet{}), T.BtANil{}}}}
    case VaANil{} VmSet{}:
      F.fd.con0("HsPrelude.HsSet.Tip")
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

# the answer's type, walked with it: a list's element, a tuple's and a
# constructor's fields (a spine), a spine's head and rest; HyNo where it is
# not known (another module's type)
def lw.ot.no() -> Hy:
  HyNo{Nil{}}

def lw.ot.hd(h: Hy) -> Hy:
  match h:
    case HyArgs{a, r}:
      a
    case _:
      lw.ot.no()

def lw.ot.tl(h: Hy) -> Hy:
  match h:
    case HyArgs{a, r}:
      r
    case _:
      lw.ot.no()

def lw.ot.elem(h: Hy) -> Hy:
  match h:
    case HyList{a}:
      a
    case _:
      lw.ot.no()

def lw.ot.tup(h: Hy) -> Hy:
  match h:
    case HyT2{a, b}:
      HyArgs{a, HyArgs{b, HyANil{}}}
    case HyT3{a, b, c}:
      HyArgs{a, HyArgs{b, HyArgs{c, HyANil{}}}}
    case _:
      lw.ot.no()

def lw.ot.ck(cs: List<&2, Ck>, +c: List<&2, U32>) -> Hy:
  match cs:
    case Ck{hs, b, fs} <> t:
      Bool.pick(Hy, S.eq(b, c), fs, lw.ot.ck(t, c))
    case Nil{}:
      lw.ot.no()

def lw.ot.con(h: Hy, +c: List<&2, U32>, +le: Le, +dds: List<&2, Dd>) -> Hy:
  match h:
    case HyMaybe{a}:
      HyArgs{a, HyANil{}}
    case HyEither{a, b}:
      HyArgs{Bool.pick(Hy, S.eq(c, S.b("Inl")), a, b), HyANil{}}
    case HyUser{+n, args}:
      lw.ot.ck(lw.cks.of(lw.dd.find(dds, n), le, args), c)
    case HyMap{+a, +b}:
      Bool.pick(Hy, S.eq(c, S.b("HsPrelude.HsMap.Bin")), HyArgs{a, HyArgs{b, HyArgs{HyMap{a, b}, HyANil{}}}}, HyANil{})
    case HySet{+a}:
      Bool.pick(Hy, S.eq(c, S.b("HsPrelude.HsSet.Bin")), HyArgs{a, HyArgs{HySet{a}, HyANil{}}}, HyANil{})
    case HyFix{HyUser{+n, +args}}:
      HyArgs{HyUser{n, lw.hy.snoc(args, HyFix{HyUser{n, args}})}, HyANil{}}
    case HyCof{HyUser{+n, +args}, +a}:
      HyArgs{a, HyArgs{HyUser{n, lw.hy.snoc(args, HyCof{HyUser{n, args}, a})}, HyANil{}}}
    case HyDig{}:
      HyArgs{HyList{HyW8{}}, HyANil{}}
    case HyRat{}:
      HyArgs{HyInt{S.b("LawP.Integer")}, HyArgs{HyNat{S.b("LawP.Integer")}, HyANil{}}}
    case _:
      lw.ot.no()

# whether a number answer is an HsInt: by its type (a data type's Natural
# field is a Nat in a module with HsInt: sg), where that is known
def lw.ot.sg(h: Hy, sg: Bool) -> Bool:
  match h:
    case HyNat{s}:
      False{}
    case HyInt{s}:
      True{}
    case _:
      sg

# a number answer: a byte's is a U32
def lw.out.nat(h: Hy, sg: Bool, +n: List<&2, U32>) -> T.Bt:
  match h:
    case HyW8{}:
      T.BtVar{n}
    case +r:
      lw.out.num(lw.ot.sg(r, sg), False{}, n)

# an answer in Bend, ty its type; a negative number has none where the
# fold's Int is Nat.  It recurses on the tree's own parts (a string's answer
# is as long as the string)
def lw.out(x: X.Sx, k: Ok, mode: Vm, +ty: Hy, +sg: Bool, +le: Le, +dds: List<&2, Dd>) -> T.Bt:
  match x k mode:
    case X.SxCons{+h, t} _ VmSp{}:
      T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, lw.ot.hd(ty), sg, le, dds), lw.out(t, OkNo{}, VmSp{}, lw.ot.tl(ty), sg, le, dds)}
    case _ _ VmSp{}:
      T.BtANil{}
    case X.SxCons{+h, t} _ VmList{}:
      T.BtCon{S.b("Con"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, ty, sg, le, dds), T.BtArgs{lw.out(t, OkNo{}, VmList{}, ty, sg, le, dds), T.BtANil{}}}}
    case _ _ VmList{}:
      F.fd.con0("Nil")
    case X.SxCons{+h, X.SxNil{}} _ VmTup{}:
      lw.out(h, lw.okind(h), VmVal{}, lw.ot.hd(ty), sg, le, dds)
    case X.SxCons{+h, t} _ VmTup{}:
      T.BtCon{S.b("Tuple"), T.BtArgs{lw.out(h, lw.okind(h), VmVal{}, lw.ot.hd(ty), sg, le, dds), T.BtArgs{lw.out(t, OkNo{}, VmTup{}, lw.ot.tl(ty), sg, le, dds), T.BtANil{}}}}
    case _ _ VmTup{}:
      F.fd.con0("Unit")
    case +y OkNat{} _:
      lw.out.nat(ty, sg, X.tsx.atom.of(X.tsx.at(1n, y)))
    case +y OkNeg{} _:
      lw.out.num(lw.ot.sg(ty, sg), True{}, X.tsx.atom.of(X.tsx.at(1n, y)))
    case +y OkChar{} _:
      F.fd.char(X.tsx.nat(X.tsx.at(1n, y)))
    case X.SxCons{h, t} OkList{} _:
      lw.out(t, OkNo{}, VmList{}, lw.ot.elem(ty), sg, le, dds)
    case X.SxCons{h, t} OkTup{} _:
      lw.out(t, OkNo{}, VmTup{}, lw.ot.tup(ty), sg, le, dds)
    case X.SxCons{h, X.SxCons{c, t}} OkCon{} _:
      +cn = X.tsx.str.of(c)
      T.BtCon{cn, lw.out(t, OkNo{}, VmSp{}, lw.ot.con(ty, cn, le, dds), sg, le, dds)}
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
  Pl{b: List<&2, U32>, ret: T.Bt, hy: Hy, ls: List<&2, Lc>}
  PlNo{b: List<&2, U32>, why: List<&2, U32>}

# a parameter's term in a law's call when it is no value: a type (Data) is
# Nat, a dictionary (Fold's fd.dc: eq_A, cmp_A) Nat's == or compare; and
# whether it is a template
type La is Data:
  La{t: Bool, d: T.Bt, i: Nat}

def lw.dterm(k: Nat) -> T.Bt:
  match k:
    case 0n:
      F.fd.ty0("Nat")
    case 1n:
      F.fd.v("Nat.is_eq")
    case _:
      F.fd.v("Nat.cmp")

def lw.hd.nat(xs: List<&2, Nat>) -> Nat:
  match xs:
    case x <> t:
      x
    case Nil{}:
      0n

# each parameter: whether a template, its default, and (a value's) which
# input it takes, by its place in h's order (hp)
def lw.tpls(ps: List<&2, T.BParam>, +hp: List<&2, Nat>) -> List<&2, La>:
  match ps:
    case T.BParam{T.BmTpl{}, +x, +ty} <> t:
      +i = lw.hd.nat(hp)
      La{True{}, lw.dterm(K.bk.dc.isdict(T.BParam{T.BmTpl{}, x, ty})), i} <> lw.tpls(t, List.drop(&2, Nat, hp, 1n))
    case _ <> t:
      +i = lw.hd.nat(hp)
      La{False{}, F.fd.ty0("Nat"), i} <> lw.tpls(t, List.drop(&2, Nat, hp, 1n))
    case Nil{}:
      Nil{}

# Fold writes the doc Back reads (a checked law: the same text)
def lw.ord.head() -> {F.fd.tpl.doc.head() == K.bk.o.head() : String}:
  {==}

# the def n's places, by its doc (Back's bk.o.docs)
def lw.kept.ord.at(c: Bool, +d: List<&2, List<&2, U32>>, r: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      K.bk.o.or(K.bk.o.docs(d), r)
    case False{}:
      r

def lw.kept.ord(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, Nat>:
  match its:
    case T.BiDef{k, ps, r, b, d} <> t:
      lw.kept.ord.at(S.eq(k, n), d, lw.kept.ord(t, n))
    case _ <> t:
      lw.kept.ord(t, n)
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

def lw.va.nth(vs: Va, i: Nat) -> Va:
  match vs i:
    case VaArgs{v, r} 0n:
      v
    case VaArgs{v, r} 1n+p:
      lw.va.nth(r, p)
    case _ _:
      VaANil{}

# the def's arguments: Nat at each type parameter, at the others the input
# at the parameter's place in h's order (a template parameter is passed as
# one)
def lw.bargs(ks: List<&2, Bool>, ts: List<&2, La>, +vs: Va) -> List<&2, T.Bt>:
  match ks ts:
    case True{} <> k2 La{t, d, i} <> t2:
      lw.wrap(t, d) <> lw.bargs(k2, t2, vs)
    case False{} <> k2 La{t, d, i} <> t2:
      lw.wrap(t, lw.va.bt(lw.va.nth(vs, i), VmVal{})) <> lw.bargs(k2, t2, vs)
    case _ _:
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

# the input a spine ends with, a parser's, as Bend's list of characters
def lw.pin.last(vs: Va) -> T.Bt:
  match vs:
    case VaArgs{VaPin{s}, VaANil{}}:
      lw.bt.lit(s)
    case VaArgs{v, r}:
      lw.pin.last(r)
    case _:
      F.fd.con0("Nil")

# the call's answer as the law states it: a parser's reply as HsPc.answer
# writes it (A: its answer's type)
def lw.call.of(w: Maybe<&2, T.Bt>, c: T.Bt, vs: Va) -> T.Bt:
  match w:
    case Some{a}:
      F.fd.callS("HsPrelude.HsPc.answer", [a, c, lw.pin.last(vs)])
    case None{}:
      c

def lw.lcs(ins: List<&2, Va>, +k: Nat, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, La>, +w: Maybe<&2, T.Bt>) -> List<&2, Lc>:
  match ins:
    case VaTup{+s} <> t:
      Lc{k, lw.cat(f, lw.va.hs(s, VmSp{})), lw.call.of(w, lw.bcall(b, ks, ts, s), s)} <> lw.lcs(t, 1n+k, b, f, ks, ts, w)
    case _ <> t:
      lw.lcs(t, k, b, f, ks, ts, w)
    case Nil{}:
      Nil{}

def lw.plan.ins(ins: List<&2, Va>, +b: List<&2, U32>, +f: List<&2, U32>, +ks: List<&2, Bool>, +ts: List<&2, La>, ret: T.Bt, hy: Hy, +w: Maybe<&2, T.Bt>) -> Pl:
  match ins:
    case Nil{}:
      PlNo{b, S.b("nolaw:no-input")}
    case +h <> t:
      Pl{b, ret, hy, lw.lcs(h <> t, 1n, b, f, ks, ts, w)}

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

# its answer, as a type of the laws' (lw.out): Either String A
def lw.pt.hy(pt: Bool, +r: Hy) -> Hy:
  Bool.pick(Hy, pt, HyEither{HyList{HyChar{}}, r}, r)

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

# the law's type: the def's answer's, as Fold writes it; an ExceptT run
# from a state answers Fold's state pair, Sigma<&1, &1, Either<E, A>, _ =>
# S> (fd.ty.st)
def lw.ret.of(h: Hy, hf: Hy) -> T.Bt:
  match h:
    case HyExs{e, l, s, a}:
      F.fd.spair(F.fd.either(lw.bty(e), lw.bty(a)), lw.bty(s))
    case HyStA{l, s, a}:
      F.fd.spair(lw.bty(a), lw.bty(s))
    case _:
      lw.bty(hf)

# how many inputs: a parser's are the shapes of lw.pins
def lw.plan.many(w: Maybe<&2, T.Bt>) -> Nat:
  match w:
    case Some{a}:
      16n
    case None{}:
      8n

def lw.plan.go(+f: List<&2, U32>, +pt: Bool, +b: List<&2, U32>, +hf: Hy, +rt: T.Bt, +le: Le, +dds: List<&2, Dd>, +ps: List<&2, T.BParam>, +ord: List<&2, Nat>, +w: Maybe<&2, T.Bt>) -> Pl:
  lw.plan.ins(List.take(&2, Va, lw.vals(40n, 5n, le, dds, QFields{lw.args(hf)}), lw.plan.many(w)), b, f, K.bk.o.kinds(ps), lw.tpls(ps, K.bk.o.hp(K.bk.o.fit(ord, ps), K.bk.o.kinds(ps))), lw.pt.ret(pt, rt), lw.pt.hy(pt, lw.res(hf)), w)

# the GHCi call's head (h's type named, an ExceptT's or a parser's run
# applied to it: a partial parser's not yet) and the plan at the type as run
# (lw.flat)
def lw.plan.of2(x: Rn, +pt: Bool, +b: List<&2, U32>, +h: Hy, +hf: Hy, +m: List<&2, U32>, +hsn: List<&2, U32>, +le: Le, +dds: List<&2, Dd>, +ps: List<&2, T.BParam>, +ord: List<&2, Nat>) -> Pl:
  match x pt:
    case RnNo{} _:
      lw.plan.go(lw.cat3(lw.pt.open(pt), lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41])), pt, b, hf, lw.ret.of(lw.res(h), lw.res(hf)), le, dds, ps, ord, None{})
    case RnExs{l} _:
      lw.plan.go(lw.cat3(lw.pt.open(pt), lw.exs.run(l, lw.nargs(lw.args(h))), lw.cat3(lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41]), [41])), pt, b, hf, lw.ret.of(lw.res(h), lw.res(hf)), le, dds, ps, ord, None{})
    case RnSt{l} _:
      lw.plan.go(lw.cat3(lw.pt.open(pt), lw.st.run(l, lw.nargs(lw.args(h))), lw.cat3(lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41]), [41])), pt, b, hf, lw.ret.of(lw.res(h), lw.res(hf)), le, dds, ps, ord, None{})
    case RnPc{a} False{}:
      lw.plan.go(lw.cat3(lw.pt.open(pt), lw.pc.run(lw.nargs(lw.args(h))), lw.cat3(lw.hsname(m, hsn), lw.cat3(S.b(" :: "), lw.hs.ty(h, m), [41]), [41])), pt, b, hf, lw.ret.of(lw.res(h), lw.res(hf)), le, dds, ps, ord, Some{lw.bty(a)})
    case RnPc{a} True{}:
      PlNo{b, S.b("nolaw:partial-Parsec")}

def lw.plan.of(why: List<&2, U32>, +b: List<&2, U32>, +h: Hy, +m: List<&2, U32>, +hsn: List<&2, U32>, +le: Le, +dds: List<&2, Dd>, +ps: List<&2, T.BParam>, +pt: Bool, +ord: List<&2, Nat>) -> Pl:
  match why:
    case Nil{}:
      lw.plan.of2(lw.run.of(lw.res(h)), pt, b, h, lw.flat(h), m, hsn, le, dds, ps, ord)
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
def lw.plan.tb(found: Maybe<&2, List<&2, T.BParam>>, +n: List<&2, U32>, +f: X.Sx, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>, pt: Bool, +ord: List<&2, Nat>) -> List<&2, Pl>:
  match found:
    case Some{+ps}:
      +h = lw.ty(le, V.sv.at(f, 2n))
      [lw.plan.of(lw.plan.why(lw.flat(h), K.bk.o.kinds(ps)), F.fd.vname(n), h, m, n, le, dds, ps, pt, ord)]
    case None{}:
      Nil{}

def lw.plans(tbs: List<&2, F.Tb>, +its: List<&2, T.BItem>, +le: Le, +dds: List<&2, Dd>, +m: List<&2, U32>) -> List<&2, Pl>:
  match tbs:
    case F.TbFun{+n, tvs, +f} <> t:
      List.append(&2, Pl, lw.plan.tb(lw.kept(its, F.fd.vname(n)), n, f, le, dds, m, lw.kept.pt(its, F.fd.vname(n)), lw.kept.ord(its, F.fd.vname(n))), lw.plans(t, its, le, dds, m))
    case _ <> t:
      lw.plans(t, its, le, dds, m)
    case Nil{}:
      Nil{}

def lw.any.pl(ps: List<&2, Pl>) -> Bool:
  match ps:
    case Pl{b, r, hy, ls} <> t:
      True{}
    case _ <> t:
      lw.any.pl(t)
    case Nil{}:
      False{}

# The GHCi script ------------------------------------------------------------------

# Everything the script names is qualified (LawP is the Prelude), so a
# module that defines its own Maybe, or hides the Prelude's, changes
# nothing here.  Each answer is printed with lawSx; lawRun gives each call
# 2 s and 500 MB of allocation (a loop that keeps all it makes would fill
# GHC's 2 GB heap before the clock stops it) and turns an exception (error,
# a failed pattern) into `err`.
# Data.Map's, Data.Set's, Fix's and Cofree's values: an input is written
# with lawMap, lawSet, lawFix and lawCof, its type with a wildcard (_ k v),
# so the one script runs against h (containers', data-fix's, free's types)
# and against G(F(h)) (BendRt's B'HsPrelude'HsMap ..); an answer prints as
# Bend's HsPrelude.HsMap.Bin .. on either. A block whose names are not in
# scope (BendRt's for h, data-fix's for a module without it) fails alone.
def lw.ghci.pre.k() -> String:
  ":{\ninstance (LawSx k, LawSx v) => LawSx (LawM.Map k v) where\n  lawSx m = LawP.foldr (\\(k, v) r -> lawC \"HsPrelude.HsMap.Bin\" [lawSx k, lawSx v, r]) (lawC \"HsPrelude.HsMap.Tip\" []) (LawM.toAscList m)\n:}\n:{\ninstance LawSx k => LawSx (LawS.Set k) where\n  lawSx s = LawP.foldr (\\k r -> lawC \"HsPrelude.HsSet.Bin\" [lawSx k, r]) (lawC \"HsPrelude.HsSet.Tip\" []) (LawS.toAscList s)\n:}\n:{\ninstance LawSx (f (Data.Fix.Fix f)) => LawSx (Data.Fix.Fix f) where\n  lawSx (Data.Fix.Fix x) = lawC \"HsPrelude.Fix.Fix\" [lawSx x]\n:}\n:{\ninstance (LawSx a, LawSx (f (Control.Comonad.Cofree.Cofree f a))) => LawSx (Control.Comonad.Cofree.Cofree f a) where\n  lawSx (a Control.Comonad.Cofree.:< x) = lawC \"HsPrelude.Cofree.Cofree\" [lawSx a, lawSx x]\n:}\n"

def lw.ghci.pre.g() -> String:
  ":{\ninstance (LawSx k, LawSx v) => LawSx (B'HsPrelude'HsMap k v) where\n  lawSx m = case m of { B'HsPrelude'HsMap'Tip -> lawC \"HsPrelude.HsMap.Tip\" []; B'HsPrelude'HsMap'Bin k v r -> lawC \"HsPrelude.HsMap.Bin\" [lawSx k, lawSx v, lawSx r] }\n:}\n:{\ninstance LawSx k => LawSx (B'HsPrelude'HsSet k) where\n  lawSx s = case s of { B'HsPrelude'HsSet'Tip -> lawC \"HsPrelude.HsSet.Tip\" []; B'HsPrelude'HsSet'Bin k r -> lawC \"HsPrelude.HsSet.Bin\" [lawSx k, lawSx r] }\n:}\n:{\ninstance LawSx (f (B'HsPrelude'Fix f)) => LawSx (B'HsPrelude'Fix f) where\n  lawSx (B'HsPrelude'Fix'Fix x) = lawC \"HsPrelude.Fix.Fix\" [lawSx x]\n:}\n:{\ninstance (LawSx a, LawSx (f (B'HsPrelude'Cofree f a))) => LawSx (B'HsPrelude'Cofree f a) where\n  lawSx (B'HsPrelude'Cofree'Cofree a x) = lawC \"HsPrelude.Cofree.Cofree\" [lawSx a, lawSx x]\n:}\n"

def lw.ghci.pre.c() -> String:
  ":{\ntype LawFixT = Data.Fix.Fix\n:}\n:{\ntype LawFixT = B'HsPrelude'Fix\n:}\n:{\ntype LawCofT = Control.Comonad.Cofree.Cofree\n:}\n:{\ntype LawCofT = B'HsPrelude'Cofree\n:}\n:{\nclass LawMapC t k v | t -> k v where\n  lawMap :: [(k, v)] -> t\n:}\n:{\nclass LawSetC s k | s -> k where\n  lawSet :: [k] -> s\n:}\n:{\nclass LawFixC t where\n  lawFix :: f (t f) -> t f\n:}\n:{\nclass LawCofC t where\n  lawCof :: a -> f (t f a) -> t f a\n:}\n:{\ninstance LawMapC (LawM.Map k v) k v where\n  lawMap = LawM.fromDistinctAscList\n:}\n:{\ninstance LawMapC (Data.IntMap.IntMap v) LawP.Int v where\n  lawMap = Data.IntMap.fromDistinctAscList\n:}\n:{\ninstance LawSetC (LawS.Set k) k where\n  lawSet = LawS.fromDistinctAscList\n:}\n:{\ninstance LawSetC Data.IntSet.IntSet LawP.Int where\n  lawSet = Data.IntSet.fromDistinctAscList\n:}\n:{\ninstance LawFixC Data.Fix.Fix where\n  lawFix = Data.Fix.Fix\n:}\n:{\ninstance LawCofC Control.Comonad.Cofree.Cofree where\n  lawCof = (Control.Comonad.Cofree.:<)\n:}\n:{\ninstance LawMapC (B'HsPrelude'HsMap k v) k v where\n  lawMap = LawP.foldr (\\(k, v) r -> B'HsPrelude'HsMap'Bin k v r) B'HsPrelude'HsMap'Tip\n:}\n:{\ninstance LawSetC (B'HsPrelude'HsSet k) k where\n  lawSet = LawP.foldr B'HsPrelude'HsSet'Bin B'HsPrelude'HsSet'Tip\n:}\n:{\ninstance LawFixC B'HsPrelude'Fix where\n  lawFix = B'HsPrelude'Fix'Fix\n:}\n:{\ninstance LawCofC B'HsPrelude'Cofree where\n  lawCof = B'HsPrelude'Cofree'Cofree\n:}\n"

# a byte, a digest (crypton's, its hex shown) and a rational
def lw.ghci.pre.d() -> String:
  ":{\ninstance LawSx v => LawSx (Data.IntMap.IntMap v) where\n  lawSx m = LawP.foldr (\\(k, v) r -> lawC \"HsPrelude.HsMap.Bin\" [lawSx k, lawSx v, r]) (lawC \"HsPrelude.HsMap.Tip\" []) (Data.IntMap.toAscList m)\n:}\n:{\ninstance LawSx Data.IntSet.IntSet where\n  lawSx s = LawP.foldr (\\k r -> lawC \"HsPrelude.HsSet.Bin\" [lawSx k, r]) (lawC \"HsPrelude.HsSet.Tip\" []) (Data.IntSet.toAscList s)\n:}\n:{\ninstance LawSx LawW.Word8 where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx a => LawSx (LawR.Ratio a) where\n  lawSx r = lawC \"HsPrelude.HsRational\" [lawSx (LawR.numerator r), lawSx (LawR.denominator r)]\n:}\n:{\nlawRat :: LawP.Integer -> LawP.Integer -> LawP.Rational\nlawRat n d = n LawR.% d\n:}\n:{\nlawHex :: LawP.String -> [LawP.Int]\nlawHex s = case s of { a : b : r -> (16 LawP.* Data.Char.digitToInt a LawP.+ Data.Char.digitToInt b) : lawHex r; _ -> [] }\n:}\n:{\ninstance LawSx (Crypto.Hash.Digest a) where\n  lawSx d = lawC \"HsPrelude.HsDigest.D\" [lawSx (lawHex (LawP.show d))]\n:}\n:{\nclass LawDigC d where\n  lawDig :: [LawW.Word8] -> d\n:}\n:{\ninstance Crypto.Hash.HashAlgorithm a => LawDigC (Crypto.Hash.Digest a) where\n  lawDig bs = case Crypto.Hash.digestFromByteString (Data.ByteString.pack bs) of { LawP.Just d -> d; LawP.Nothing -> LawP.error \"lawDig\" }\n:}\n:{\ninstance LawSx B'HsPrelude'HsDigest where\n  lawSx (B'HsPrelude'HsDigest'D bs) = lawC \"HsPrelude.HsDigest.D\" [lawSx bs]\n:}\n:{\ninstance LawDigC B'HsPrelude'HsDigest where\n  lawDig bs = B'HsPrelude'HsDigest'D (LawP.map LawP.fromIntegral bs)\n:}\n"

def lw.ghci.pre0() -> String:
  ":set -XScopedTypeVariables -XFlexibleInstances -XFlexibleContexts -XUndecidableInstances -XPartialTypeSignatures -XFunctionalDependencies -Wno-partial-type-signatures\nimport qualified Prelude as LawP\nimport qualified System.Timeout as LawT\nimport qualified Control.Exception as LawE\nimport qualified System.IO as LawIO\nimport qualified System.Mem as LawSM\nimport qualified Data.Word as LawW\nimport qualified Data.Ratio as LawR\nimport qualified Numeric.Natural as LawN\nimport qualified System.IO.Unsafe as LawU\nimport qualified Data.Map as LawM\nimport qualified Data.Set as LawS\n:{\nclass LawSx a where\n  lawSx :: a -> LawP.String\n:}\n:{\nlawI :: LawP.Integer -> LawP.String\nlawI n = if n LawP.< 0 then \"(neg \" LawP.++ LawP.show (LawP.negate n) LawP.++ \")\" else \"(nat \" LawP.++ LawP.show n LawP.++ \")\"\n:}\n:{\nlawC :: LawP.String -> [LawP.String] -> LawP.String\nlawC c xs = \"(con \\\"\" LawP.++ c LawP.++ \"\\\"\" LawP.++ LawP.concatMap (\\x -> ' ' : x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx LawP.Int where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Integer where\n  lawSx n = lawI n\n:}\n:{\ninstance LawSx LawN.Natural where\n  lawSx n = lawI (LawP.toInteger n)\n:}\n:{\ninstance LawSx LawP.Bool where\n  lawSx b = if b then lawC \"True\" [] else lawC \"False\" []\n:}\n:{\ninstance LawSx LawP.Char where\n  lawSx c = \"(char \" LawP.++ LawP.show (LawP.fromEnum c) LawP.++ \")\"\n:}\n:{\ninstance LawSx () where\n  lawSx _ = lawC \"Unit\" []\n:}\n:{\ninstance LawSx LawP.Ordering where\n  lawSx o = case o of { LawP.LT -> lawC \"LT\" []; LawP.EQ -> lawC \"EQ\" []; LawP.GT -> lawC \"GT\" [] }\n:}\n:{\ninstance LawSx a => LawSx [a] where\n  lawSx xs = \"(list\" LawP.++ LawP.concatMap (\\x -> ' ' : lawSx x) xs LawP.++ \")\"\n:}\n:{\ninstance LawSx a => LawSx (LawP.Maybe a) where\n  lawSx m = case m of { LawP.Nothing -> lawC \"None\" []; LawP.Just x -> lawC \"Some\" [lawSx x] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (LawP.Either a b) where\n  lawSx e = case e of { LawP.Left x -> lawC \"Inl\" [lawSx x]; LawP.Right y -> lawC \"Inr\" [lawSx y] }\n:}\n:{\ninstance (LawSx a, LawSx b) => LawSx (a, b) where\n  lawSx (a, b) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \")\"\n:}\n:{\ninstance (LawSx a, LawSx b, LawSx c) => LawSx (a, b, c) where\n  lawSx (a, b, c) = \"(tuple \" LawP.++ lawSx a LawP.++ \" \" LawP.++ lawSx b LawP.++ \" \" LawP.++ lawSx c LawP.++ \")\"\n:}\n:{\nlawRun :: LawSx b => LawP.String -> LawP.Int -> b -> LawP.IO ()\nlawRun n k v = do\n  LawSM.setAllocationCounter 500000000\n  r <- LawE.try (LawT.timeout 2000000 (LawE.bracket_ LawSM.enableAllocationLimit LawSM.disableAllocationLimit (let s = lawSx v in LawE.evaluate (LawP.length s) LawP.>> LawP.return s)))\n  case r of\n    LawP.Left (e :: LawE.SomeException) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ (case LawE.fromException e of { LawP.Just LawE.AllocationLimitExceeded -> \" timeout\"; LawP.Nothing -> \" err\" }))\n    LawP.Right LawP.Nothing -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" timeout\")\n    LawP.Right (LawP.Just s) -> LawP.putStrLn (\"@law \" LawP.++ n LawP.++ \" \" LawP.++ LawP.show k LawP.++ \" ok \" LawP.++ s)\n  LawIO.hFlush LawIO.stdout\n:}\n:{\nnewtype LawEw a = LawEw a\n:}\n:{\ninstance LawSx a => LawSx (LawEw a) where\n  lawSx (LawEw v) = LawU.unsafePerformIO (LawE.try (let s = lawSx v in LawE.evaluate (LawP.length s) LawP.>> LawP.return s) LawP.>>= \\r -> case r of { LawP.Left (e :: LawE.SomeException) -> case LawE.fromException e of { LawP.Just (LawE.ErrorCall m) -> LawP.return (lawC \"Inl\" [lawSx m]); LawP.Nothing -> case LawE.fromException e of { LawP.Just (a :: LawE.ArithException) -> LawP.return (lawC \"Inl\" [lawSx (LawP.show a)]); LawP.Nothing -> case LawE.fromException e of { LawP.Just (LawE.PatternMatchFail p) -> LawP.return (lawC \"Inl\" [lawSx (let { lawPm t = if LawP.take 14 t LawP.== \"Non-exhaustive\" then LawP.filter (LawP./= (LawP.toEnum 10)) t else case t of { [] -> []; _ : u -> lawPm u } } in lawPm p)]); LawP.Nothing -> LawE.throwIO e } } }; LawP.Right s -> LawP.return (lawC \"Inr\" [s]) })\n:}\n"

def lw.ghci.pre() -> String:
  lw.ghci.pre0() ++ lw.ghci.pre.k() ++ lw.ghci.pre.g() ++ lw.ghci.pre.c() ++ lw.ghci.pre.d()

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
def lw.alt(+w: Dw, +c: X.Sx) -> List<&2, U32>:
  +n = V.sv.str(c, 1n)
  +vs = lw.vars(X.tsx.len(V.sv.at(c, 3n)), 0n)
  lw.cat3(S.b("    "), lw.hsname(lw.dw.hm(w), n), lw.cat3(S.join(S.b("") <> vs, 32), S.b(" -> lawC \""), lw.cat3(lw.cat(lw.dw.pre(w), F.fd.cname(lw.dw.ty(w), n)), S.b("\" ["), lw.cat(S.join(lw.sxs(vs), 44), S.b("]\n")))))

def lw.alts(+w: Dw, cs: X.Sx) -> List<&2, U32>:
  match cs:
    case X.SxCons{+c, t}:
      lw.cat(lw.alt(w, c), lw.alts(w, t))
    case _:
      Nil{}

def lw.ctx(tvs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match tvs:
    case Nil{}:
      Nil{}
    case +h <> t:
      40 <> lw.cat(S.join(lw.ctxs(h <> t), 44), S.b(") => "))

# The types lawSx must have an instance at for one at h: h's own parts where
# h is a list, a Maybe, a pair, a map .. (the script's instances), h itself
# where it is a data type's (an instance of the script, in any order), a
# type variable or a fixed point
def lw.cx(h: Hy, +m: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match h:
    case HyNat{s}:
      [s]
    case HyList{a}:
      lw.cx(a, m)
    case HyMaybe{a}:
      lw.cx(a, m)
    case HyEither{a, b}:
      List.append(&2, List<&2, U32>, lw.cx(a, m), lw.cx(b, m))
    case HyT2{a, b}:
      List.append(&2, List<&2, U32>, lw.cx(a, m), lw.cx(b, m))
    case HyT3{a, b, c}:
      List.append(&2, List<&2, U32>, lw.cx(a, m), List.append(&2, List<&2, U32>, lw.cx(b, m), lw.cx(c, m)))
    case HyMap{a, b}:
      List.append(&2, List<&2, U32>, lw.cx(a, m), lw.cx(b, m))
    case HySet{a}:
      lw.cx(a, m)
    case HyUser{n, args}:
      [lw.hs.ty(HyUser{n, args}, m)]
    case HyFix{f}:
      [lw.cat3(S.b("(LawFixT "), lw.hs.ty(f, m), [41])]
    case HyCof{f, a}:
      [lw.cat3(S.b("(LawCofT "), lw.hs.ty(f, m), 32 <> lw.cat(lw.hs.ty(a, m), [41]))]
    case HyArgs{a, r}:
      List.append(&2, List<&2, U32>, lw.cx(a, m), lw.cx(r, m))
    case _:
      Nil{}

# each constraint once, and none with a wildcard (an IntMap's or a Map's)
def lw.cx.put(no: Bool, x: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match no:
    case True{}:
      acc
    case False{}:
      x <> acc

def lw.cx.set(xs: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case +x <> t:
      lw.cx.set(t, lw.cx.put(Bool.or(S.mem(x, acc), S.infix(x, S.b("(_"))), x, acc))
    case Nil{}:
      acc

# a data type's variables as themselves
def lw.tv.sub(tvs: List<&2, List<&2, U32>>) -> List<&2, Sb>:
  match tvs:
    case +v <> t:
      Sb{v, HyNat{v}} <> lw.tv.sub(t)
    case Nil{}:
      Nil{}

def lw.cx.cons(cs: X.Sx, +le: Le, +m: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match cs:
    case X.SxCons{+c, t}:
      List.append(&2, List<&2, U32>, lw.cx(lw.hy(64n, le, HmChain{V.sv.at(c, 3n)}), m), lw.cx.cons(t, le, m))
    case _:
      Nil{}

# lawSx for one of the module's data types: its context, what its fields'
# types need, so the instances go in any order (types that name each other
# too), each in its own block (one GHCi refuses, a type with a function
# field say, costs only its own laws)
def lw.inst(+m: List<&2, U32>, +le: Le, d: Dd) -> List<&2, U32>:
  match d:
    case Dd{n, +tvs, +cs}:
      +w = lw.dw(m, n)
      lw.cat3(S.b("instance "), lw.ctx(lw.cx.set(lw.cx.cons(cs, lw.le.with(le, lw.tv.sub(tvs)), m), Nil{})), lw.cat3(S.b("LawSx ("), lw.cat3(lw.dw.hm(w), 46 <> lw.dw.ty(w), S.join(S.b("") <> tvs, 32)), lw.cat(S.b(") where\n  lawSx v = case v of\n"), lw.alts(w, cs))))

# the same with a context of the type's variables only
def lw.inst0(+m: List<&2, U32>, d: Dd) -> List<&2, U32>:
  match d:
    case Dd{n, +tvs, cs}:
      +w = lw.dw(m, n)
      lw.cat3(S.b("instance "), lw.ctx(tvs), lw.cat3(S.b("LawSx ("), lw.cat3(lw.dw.hm(w), 46 <> lw.dw.ty(w), S.join(S.b("") <> tvs, 32)), lw.cat(S.b(") where\n  lawSx v = case v of\n"), lw.alts(w, cs))))

def lw.insts.cx(+m: List<&2, U32>, +le: Le, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case d <> t:
      lw.cat3(S.b(":{\n"), lw.inst(m, le, d), lw.cat(S.b(":}\n"), lw.insts.cx(m, le, t)))
    case Nil{}:
      Nil{}

def lw.insts.one(+m: List<&2, U32>, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case d <> t:
      lw.cat(lw.inst0(m, d), lw.insts.one(m, t))
    case Nil{}:
      Nil{}

def lw.insts.each(+m: List<&2, U32>, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case d <> t:
      lw.cat3(S.b(":{\n"), lw.inst0(m, d), lw.cat(S.b(":}\n"), lw.insts.each(m, t)))
    case Nil{}:
      Nil{}

# the instances by their contexts; then in one block (G's types are its own:
# a context's h types may have no instance there) and each in its own block
# twice, where GHCi takes them (it lets an instance shadow the same one
# declared before)
def lw.insts.all(+m: List<&2, U32>, +le: Le, +ds: List<&2, Dd>) -> List<&2, U32>:
  lw.cat3(lw.insts.cx(m, le, ds), lw.cat3(S.b(":{\n"), lw.insts.one(m, ds), S.b(":}\n")), lw.cat(lw.insts.each(m, ds), lw.insts.each(m, ds)))

def lw.insts(+m: List<&2, U32>, +le: Le, ds: List<&2, Dd>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      lw.insts.all(m, le, d <> t)

# lawRun "f" 3 ((M.f :: T) a b)
def lw.lines.lc(ls: List<&2, Lc>, +b: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Lc{k, hs, c} <> t:
      lw.cat3(S.b("lawRun \""), b, lw.cat3(S.b("\" "), lw.nshow(k), lw.cat3([32], hs, lw.cat(S.b(")\n"), lw.lines.lc(t, b)))))
    case Nil{}:
      Nil{}

def lw.lines(ps: List<&2, Pl>) -> List<&2, U32>:
  match ps:
    case Pl{+b, r, hy, ls} <> t:
      lw.cat(lw.lines.lc(ls, b), lw.lines(t))
    case _ <> t:
      lw.lines(t)
    case Nil{}:
      Nil{}

# (the last line ends GHCi at once: a law out of time whose thread never
# allocates, `replace "" "" s`, is left running, and GHC's own exit waits
# for it, hs1003's 00632)

# the package's types' instances first, then the module's own
def lw.script.pk(+m: List<&2, U32>, +le: Le, pu: List<&2, Dd>, ds: List<&2, Dd>, ps: List<&2, Pl>) -> List<&2, U32>:
  lw.cat3(S.b(lw.ghci.pre()), lw.cat(lw.insts(m, le, pu), lw.insts(m, le, ds)), lw.cat(lw.lines(ps), S.b(":!kill -9 $PPID\n")))

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
def lw.law.sx(m: Maybe<&2, X.Sx>, +b: List<&2, U32>, +ret: T.Bt, +hy: Hy, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>, sg: Bool, +le: Le, +dds: List<&2, Dd>) -> List<&2, T.BItem>:
  match m:
    case Some{+x}:
      +doc = lw.cat3(S.b("GHC: "), hs, lw.cat(S.b(") = "), v))
      T.BiDef{lw.lawname(b, k), Nil{}, T.BtEq{ret, call, lw.out(x, lw.okind(x), VmVal{}, hy, Bool.and(sg, Bool.not(S.mem(S.b("Nat"), T.tba.refs(ret, Nil{})))), le, dds)}, T.BtExpr{T.BtRefl{}}, doc <> Nil{}} <> Nil{}
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

def lw.law.ok(ok: Bool, +b: List<&2, U32>, +ret: T.Bt, +hy: Hy, k: Nat, hs: List<&2, U32>, call: T.Bt, +v: List<&2, U32>, sg: Bool, +le: Le, +dds: List<&2, Dd>) -> List<&2, T.BItem>:
  match ok:
    case True{}:
      lw.law.sx(X.tsx.one(v), b, ret, hy, k, hs, call, v, sg, le, dds)
    case False{}:
      Nil{}

def lw.law(o: Maybe<&2, Ol>, +b: List<&2, U32>, +ret: T.Bt, +hy: Hy, k: Nat, +hs: List<&2, U32>, call: T.Bt, sg: Bool, +le: Le, +dds: List<&2, Dd>) -> List<&2, T.BItem>:
  match o:
    case Some{Ol{ob, ok, +st, +v}}:
      lw.law.ok(Bool.and(V.sv.is(st, "ok"), Bool.not(Bool.or(lw.bignum(v), lw.bignum(hs)))), b, ret, hy, k, hs, call, v, sg, le, dds)
    case None{}:
      Nil{}

def lw.laws.lc(ls: List<&2, Lc>, +b: List<&2, U32>, +ret: T.Bt, +hy: Hy, +os: List<&2, Ol>, +sg: Bool, +le: Le, +dds: List<&2, Dd>) -> List<&2, T.BItem>:
  match ls:
    case Lc{+k, hs, c} <> t:
      List.append(&2, T.BItem, lw.law(lw.ol.find(os, b, lw.nshow(k)), b, ret, hy, k, hs, c, sg, le, dds), lw.laws.lc(t, b, ret, hy, os, sg, le, dds))
    case Nil{}:
      Nil{}

def lw.items(ps: List<&2, Pl>, +os: List<&2, Ol>, +sg: Bool, +le: Le, +dds: List<&2, Dd>) -> List<&2, T.BItem>:
  match ps:
    case Pl{+b, +r, +hy, ls} <> t:
      List.append(&2, T.BItem, lw.laws.lc(ls, b, r, hy, os, sg, le, dds), lw.items(t, os, sg, le, dds))
    case _ <> t:
      lw.items(t, os, sg, le, dds)
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
    case Pl{+b, r, hy, ls} <> t:
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

# h's type for F's Nat, where the module tells: F takes Int, Integer and
# Natural all to Nat (so an export that has an Int or an Integer does not),
# but in a package the specialiser has written Int and Integer as HsInt
# already, and what is left is Natural's.  Empty: G does not know (and a
# module that declares a Natural of its own hides BendRt's).
def lw.back.own(ds: List<&2, Dd>, +n: List<&2, U32>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Dd{+m, tvs, cs} <> t:
      Bool.or(S.eq(m, n), lw.back.own(t, n))

# h's number type for Nat by what the export names: no Int and no Integer,
# Natural; Int alone, Int
def lw.back.nt.of(i: Bool, z: Bool, n: Bool, +dds: List<&2, Dd>) -> List<&2, U32>:
  match i z n:
    case False{} False{} _:
      Bool.pick(List<&2, U32>, lw.back.own(dds, S.b("Natural")), Nil{}, S.b("Natural"))
    case True{} False{} False{}:
      Bool.pick(List<&2, U32>, lw.back.own(dds, S.b("Int")), Nil{}, S.b("Int"))
    case _ _ _:
      Nil{}

def lw.back.nt(+dds: List<&2, Dd>, +xs: List<&2, X.Sx>) -> List<&2, U32>:
  lw.back.nt.of(lw.has.str(xs, S.b("Int")), lw.has.str(xs, S.b("Integer")), lw.has.str(xs, S.b("Natural")), dds)

# what G needs of the module (Back.bend's BkN), when CATA_BEND2HS is set
# (on): nothing is computed when it is not
def lw.back.nm(on: Bool, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +tbs: List<&2, F.Tb>, +dds: List<&2, Dd>, +its: List<&2, T.BItem>, +xs: List<&2, X.Sx>) -> K.BkN:
  match on:
    case True{}:
      +ss = lw.syns(xs)
      K.BkN{m, lw.back.as(tbs), lw.back.tn(dds), lw.back.cn(dds), lw.back.pts(tbs, its), lw.back.nf(m, ss, dds), lw.back.kd(dds, xs, m), ims, lw.back.nt(dds, xs)}
    case False{}:
      K.BkN{m, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

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
def lw.laws(+rounds: Nat, +ck: Kc, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +pkg: Bool, +xs: List<&2, X.Sx>, +tbs: List<&2, F.Tb>, +path: String, +try: String, +g0: F.Gs, +dt: List<&2, T.BItem>, +pd: List<&2, Dd>) -> IO(Lk):
  +pu0 = lw.pd.use(3n, pd, lw.mods.xs(xs, Nil{}))
  +pu = lw.pu.dds(pu0)
  +le = {Le{m, List.append(&2, Sy, lw.syns(xs), lw.pu.syns(pu0)), Nil{}, lw.dd.keys(pu)} : Le}
  +dds = List.append(&2, Dd, lw.dds(xs), pu)
  +ps = lw.plans(tbs, lw.gs.its(g0), le, dds, m)
  do IO<Lk>:
    txt : List<&2, U32> <- lw.ghc.run(lw.any.pl(ps), ck, ghc, S.str(lw.src(xs)), out ++ "/" ++ S.str(base) ++ ".ghci", out ++ "/" ++ S.str(base) ++ ".ghc", lw.script.pk(m, le, pu, lw.dds(xs), ps))
    lw.laws2(rounds, ck, bend, out, file, m, ims, pkg, path, try, g0, ps, lw.items(ps, lw.ols(S.split(txt, 10)), lw.has.str(xs, S.b("HsInt")), le, dds), dt, lw.back.nm(lw.kc.back(ck), m, ims, tbs, lw.dds(xs), lw.gs.its(g0), xs))

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
  Lm{px: F.Px, ck: Kc, dm: Map<&2, List<&2, Bool>>, pd: List<&2, Dd>}

def lw.lm.px(+r: Lm) -> F.Px:
  match r:
    case Lm{px, ck, dm, pd}:
      px

def lw.lm.ck(+r: Lm) -> Kc:
  match r:
    case Lm{px, ck, dm, pd}:
      ck

# the bindings read at Integer so far (Survey's sv.dfl)
def lw.lm.dm(+r: Lm) -> Map<&2, List<&2, Bool>>:
  match r:
    case Lm{px, ck, dm, pd}:
      dm

# the data types of the package's modules so far, each by its key M.T
def lw.lm.pd(+r: Lm) -> List<&2, Dd>:
  match r:
    case Lm{px, ck, dm, pd}:
      pd

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
def lw.module(+rounds: Nat, +bend: String, +ghc: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, bytes: List<&2, U32>, +pkg: Bool, +px: F.Px, +ck: Kc, dm: Map<&2, List<&2, Bool>>, +pd: List<&2, Dd>) -> IO(Lm):
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
    +kept : Lk <- lw.laws(rounds, ck1, bend, ghc, out, file, base, m, ims, pkg, xs, tbs, path, try, g0, F.fd.px.dt(px), pd)
    lw.rt.write(F.fd.is(m, "BendRt"), out, file, m, ims, lw.lk.its(kept))
    return Lm{F.fd.px.next(pkg, px, m, base, xs, gs, F.fd.tfs(g2), cs, ds, lw.lk.its(kept)), lw.kc.with.mk(ck1, lw.lk.mk(kept)), V.sv.dfl.next(pkg, V.sv.dfl.dm.m(d)), lw.pd.next(pkg, m, xs, pd)}

def lw.run(xs: List<String>, +rounds: Nat, +bend: String, +ghc: String, +out: String, +pkg: Bool, +px: F.Px, +ck: Kc, dm: Map<&2, List<&2, Bool>>, pd: List<&2, Dd>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +r : Lm <- lw.module(rounds, bend, ghc, out, S.b(f), F.fd.base(S.b(f)), bytes, pkg, px, ck, dm, pd)
        lw.run(t, rounds, bend, ghc, out, pkg, lw.lm.px(r), lw.lm.ck(r), lw.lm.dm(r), lw.lm.pd(r))

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
      lw.run(files, rounds, bend, ghc, out, pkg, F.fd.px0(), ck, V.sv.dfl0(), Nil{})
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
