import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X
import ./a2b/ToBend/Ast.bend as T
import ./a2b/ToBend/Print.bend as P
import ./a2b/ToBend/Order.bend as O
import ./Survey.bend as V
import ./Prelude.bend as PR

# Fold: cata hs, step 2 (PLAN.md, "Step 2: the fold").  It folds the
# bindings of an hs-export module (tools/hs-export/FORMAT.md) that the
# survey (Survey.bend) puts in the first version into ToBend's syntax tree
# (a2b/ToBend/Ast.bend), prints them (a2b/ToBend/Print.bend), and keeps
# the ones Bend's checker accepts:
#
#   fold OUT FILE.sexp...
#
# writes OUT/NAME.bend for each module with at least one def that checks
# (OUT/NAME_try.bend is the last file the gate tried),
# and appends to OUT/ledger.tsv, for every binding a user wrote, one line
#
#   FILE  NAME  ok|out  WHY
#
# BEND names the bend to check with; FOLD_ROUNDS (default: as many as there
# are items) caps the gate's rounds, to see a first failure.
#
# WHY is empty for ok; for out it is `survey` (the survey left it out; its
# reasons are in survey.tsv), `fold:..` (a form this fold does not write
# yet), `dep:NAME` (it uses a binding that is out) or `check:LINE` (the
# first line of Bend's error).  No model is asked anything: a binding the
# rules do not take goes to the ledger.
#
# How Haskell is written in Bend (the rules, each forced by Bend 2.0.39):
#   - Int and Integer are Nat (the survey keeps out whatever subtracts),
#     Bool, Char and Float are Bend's, every list is List<&2, T> (Data, so
#     it may be copied), String is List<&2, Char>, Maybe and Either are
#     Bend's at &2, a pair is Sigma<&2, &2, A, _ => B>, Ordering is Cmp;
#   - a type variable is an erased parameter -A: Data, passed explicitly at
#     every call (GHC's type applications say which);
#   - a constructor is TYPE.CON (Bend's constructor names are global);
#   - clauses become one match on the parameters they split, in parameter
#     order, patterns nested as written;
#   - a guard or an if is Bool.if(R, c, u => a, u => b), the branches
#     thunks, as Base's List.any.if writes it (Bend has no if, and matches
#     only parameters); R is the type of the binding's right-hand side;
#   - where and let are lets in front of the body;
#   - a variable used twice is +x (every type here is Data);
#   - a higher-order Base function takes its function as a template
#     (~f), so the function must be closed: a lambda over locals is out
#     (but at first, second and bimap, which call it once, plain f).
# Every def is prefixed `fd.`.

# Text ---------------------------------------------------------------------

def fd.is(+x: List<&2, U32>, s: String) -> Bool:
  S.eq(x, S.b(s))

def fd.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def fd.cat3(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> List<&2, U32>:
  fd.cat(a, fd.cat(b, c))

def fd.bpick(c: Bool, a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, c, a, b)

def fd.nshow(n: Nat) -> List<&2, U32>:
  S.b(Nat.show(n))

# Names --------------------------------------------------------------------

# a symbol of an operator's name, and the word it is written as
type Sym is Data:
  Sym{c: U32, w: String}

def fd.syms() -> List<&2, Sym>:
  [Sym{39, "q"}, Sym{43, "plus"}, Sym{45, "minus"}, Sym{42, "times"}, Sym{47, "slash"}, Sym{60, "lt"}, Sym{62, "gt"}, Sym{61, "eq"}, Sym{33, "bang"}, Sym{46, "dot"}, Sym{124, "bar"}, Sym{38, "amp"}, Sym{36, "dollar"}, Sym{35, "hash"}, Sym{37, "pct"}, Sym{94, "hat"}, Sym{126, "tilde"}, Sym{64, "at"}, Sym{63, "qm"}, Sym{58, "colon"}, Sym{92, "bslash"}]

def fd.sym.find(xs: List<&2, Sym>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      S.b("sym")
    case Sym{k, w} <> t:
      fd.bpick(U32.is_eq(k, c), S.b(w), fd.sym.find(t, c))

# a letter, a digit or _
def fd.namec(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90))), Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), U32.is_eq(c, 95)))

def fd.name.ch(ok: Bool, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      c <> rest
    case False{}:
      95 <> fd.cat(fd.sym.find(fd.syms(), c), rest)

def fd.name.go(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> t:
      fd.name.ch(fd.namec(c), c, fd.name.go(t))

# whether a name starts as a Bend name does (a letter or _)
def fd.name.lead(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      Bool.and(fd.namec(c), Bool.or(U32.is_lt(c, 48), U32.is_gt(c, 57)))
    case Nil{}:
      False{}

def fd.keywords() -> List<&2, List<&2, U32>>:
  V.sv.strs(["def", "type", "match", "case", "law", "import", "do", "return", "for", "exs", "where", "is", "as", "with", "Type", "Data", "Quant", "Kind", "Set", "Empty", "Unit", "main", "if", "else", "then", "let", "in", "true", "false"])

def fd.name.kw(+x: List<&2, U32>) -> List<&2, U32>:
  fd.bpick(S.mem(x, fd.keywords()), fd.cat(x, S.b("_")), x)

def fd.name.op(lead: Bool, x: List<&2, U32>) -> List<&2, U32>:
  match lead:
    case True{}:
      x
    case False{}:
      fd.cat(S.b("op"), x)

# a Haskell name as a Bend name: an operator's symbols spelled out
# (<+> is op_lt_plus_gt), a prime as _q, a Bend keyword with _ after
def fd.vname(+x: List<&2, U32>) -> List<&2, U32>:
  fd.name.kw(fd.name.op(fd.name.lead(x), fd.name.go(x)))

def fd.upper(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      Bool.pick(U32, Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), U32.sub(c, 32), c) <> t
    case Nil{}:
      Nil{}

# a type variable: a capital (a is A)
def fd.tvname(+x: List<&2, U32>) -> List<&2, U32>:
  fd.upper(fd.name.go(x))

def fd.basetys() -> List<&2, List<&2, U32>>:
  V.sv.strs(["Empty", "Unit", "Bool", "Cmp", "Either", "Sigma", "Nat", "Maybe", "Result", "Poll", "List", "Word", "U32", "F32", "Char", "String", "Array", "Image", "Event", "Map", "Set", "Equal", "IO", "File", "Socket", "Window", "Chan", "Process", "App", "Audio", "Pair", "Kind", "Type", "Data", "Quant", "TCP", "UDP", "Bits", "Int", "I32", "Out"])

# a type's name; one Base has too gets _ after
def fd.tyname(+x: List<&2, U32>) -> List<&2, U32>:
  +y = fd.vname(x)
  fd.bpick(S.mem(y, fd.basetys()), fd.cat(y, S.b("_")), y)

# a constructor: TYPE.CON
def fd.cname(+t: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  fd.cat3(fd.tyname(t), S.b("."), fd.vname(c))

# Terms --------------------------------------------------------------------

def fd.v(s: String) -> T.Bt:
  T.BtVar{S.b(s)}

def fd.ty0(s: String) -> T.Bt:
  T.BtTyApp{S.b(s), T.BtANil{}}

def fd.todo(s: String) -> T.Bt:
  T.BtTodo{S.b(s)}

def fd.callS(f: String, xs: List<&2, T.Bt>) -> T.Bt:
  T.tba.call(T.BtVar{S.b(f)}, xs)

def fd.con0(s: String) -> T.Bt:
  T.BtCon{S.b(s), T.BtANil{}}

def fd.tpl0(t: T.Bt) -> T.Bt:
  T.BtTplArg{t}

def fd.tpls(xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case h <> t:
      fd.tpl0(h) <> fd.tpls(t)
    case Nil{}:
      Nil{}

# ~A: Data for each
def fd.tvtpls(tvs: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match tvs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BParam{T.BmTpl{}, h, fd.v("Data")} <> fd.tvtpls(t)

def fd.bpicks(c: Bool, a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  Bool.pick(List<&2, List<&2, U32>>, c, a, b)

def fd.uses.name(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case +h <> t:
      Bool.or(S.mem(n, T.tba.item.fold(~T.tba.refs, h, Nil{})), fd.uses.name(t, n))
    case Nil{}:
      False{}

# List<&2, A>
def fd.list(a: T.Bt) -> T.Bt:
  T.BtTyApp{S.b("List"), T.tba.args([fd.v("&2"), a])}

# Sigma<&2, &2, A, _ => B>: a pair Bend may copy
def fd.pair(a: T.Bt, b: T.Bt) -> T.Bt:
  T.BtTyApp{S.b("Sigma"), T.tba.args([fd.v("&2"), fd.v("&2"), a, T.BtLam{T.BmLive{}, S.b("_"), b}])}

# a spine's elements
def fd.spine(t: T.Bt) -> List<&2, T.Bt>:
  match t:
    case T.BtArgs{a, rest}:
      a <> fd.spine(rest)
    case _:
      Nil{}

# f applied to xs, or f when there are none
def fd.apply(f: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case Nil{}:
      f
    case h <> t:
      T.BtApp{f, T.tba.args(h <> t)}

# a body is a statement: a match, a let, or one expression
def fd.stmt(t: T.Bt) -> T.Bt:
  match t:
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, cs}
    case T.BtLet{x, v, b}:
      T.BtLet{x, v, b}
    case T.BtExpr{e}:
      T.BtExpr{e}
    case e:
      T.BtExpr{e}

# a statement where only an expression may stand (a thunk's body, a let's
# value): a match or a let there is out
def fd.expr(t: T.Bt) -> T.Bt:
  match t:
    case T.BtMatch{xs, cs}:
      fd.todo("fold:match-in-expression")
    case T.BtLet{x, v, b}:
      fd.todo("fold:let-in-expression")
    case T.BtExpr{e}:
      e
    case e:
      e

# Types --------------------------------------------------------------------

type Tk is Data:
  TkNat{}
  TkShowS{}
  TkBool{}
  TkChar{}
  TkF32{}
  TkList{}
  TkStr{}
  TkMaybe{}
  TkEither{}
  TkT2{}
  TkT3{}
  TkUnit{}
  TkCmp{}
  TkFix{}
  TkCofree{}
  TkCofreeF{}
  TkBase{}
  TkState{}
  TkStateT{}
  TkIdentity{}
  TkExceptT{}
  TkReaderT{}
  TkReader{}
  TkWriterT{}
  TkWriter{}
  TkMap{}
  TkEmpty{}
  TkHsInt{}
  TkDigest{}
  TkRat{}
  TkU32{}
  TkSet{}
  TkIntMap{}
  TkIntSet{}
  TkParsecT{}
  TkParsec{}
  TkPeb{}
  TkSPos{}
  TkPos{}
  TkToken{}
  TkTokens{}
  TkNone{}

type TkE is Data:
  TkE{k: String, v: Tk}

def fd.tktab() -> List<&2, TkE>:
  [TkE{"GHC.Types.Int", TkNat{}}, TkE{"GHC.Num.Integer.Integer", TkNat{}}, TkE{"GHC.Num.Natural.Natural", TkNat{}}, TkE{"GHC.Types.Bool", TkBool{}}, TkE{"GHC.Types.Char", TkChar{}}, TkE{"GHC.Types.Float", TkF32{}}, TkE{"GHC.Types.List", TkList{}}, TkE{"GHC.Internal.Base.String", TkStr{}}, TkE{"GHC.Internal.Show.ShowS", TkShowS{}}, TkE{"GHC.Internal.IO.FilePath", TkStr{}}, TkE{"GHC.Internal.Maybe.Maybe", TkMaybe{}}, TkE{"GHC.Internal.Data.Either.Either", TkEither{}}, TkE{"GHC.Tuple.Tuple2", TkT2{}}, TkE{"GHC.Tuple.Tuple3", TkT3{}}, TkE{"GHC.Tuple.Unit", TkUnit{}}, TkE{"GHC.Types.Ordering", TkCmp{}}, TkE{"Data.Fix.Fix", TkFix{}}, TkE{"Control.Comonad.Cofree.Cofree", TkCofree{}}, TkE{"Control.Comonad.Trans.Cofree.CofreeF", TkCofreeF{}}, TkE{"Data.Functor.Foldable.Base", TkBase{}}, TkE{"Control.Monad.Trans.State.Lazy.State", TkState{}}, TkE{"Control.Monad.Trans.State.Strict.State", TkState{}}, TkE{"Control.Monad.Trans.State.Lazy.StateT", TkStateT{}}, TkE{"Control.Monad.Trans.State.Strict.StateT", TkStateT{}}, TkE{"GHC.Internal.Data.Functor.Identity.Identity", TkIdentity{}}, TkE{"Control.Monad.Trans.Except.ExceptT", TkExceptT{}}, TkE{"Control.Monad.Trans.Reader.ReaderT", TkReaderT{}}, TkE{"Control.Monad.Trans.Reader.Reader", TkReader{}}, TkE{"Control.Monad.Trans.Writer.Strict.WriterT", TkWriterT{}}, TkE{"Control.Monad.Trans.Writer.Lazy.WriterT", TkWriterT{}}, TkE{"Control.Monad.Trans.Writer.Strict.Writer", TkWriter{}}, TkE{"Control.Monad.Trans.Writer.Lazy.Writer", TkWriter{}}, TkE{"Data.Map.Internal.Map", TkMap{}}, TkE{"Data.Set.Internal.Set", TkSet{}}, TkE{"Data.IntMap.Internal.IntMap", TkIntMap{}}, TkE{"Data.IntSet.Internal.IntSet", TkIntSet{}}, TkE{"Data.IntSet.Internal.Key", TkNat{}}, TkE{"Data.IntMap.Internal.Key", TkNat{}}, TkE{"GHC.Internal.Base.Void", TkEmpty{}}, TkE{"HsPrelude.HsInt", TkHsInt{}}, TkE{"HsPrelude.HsInteger", TkHsInt{}}, TkE{"HsPrelude.HsDigest", TkDigest{}}, TkE{"HsPrelude.HsRational", TkRat{}}, TkE{"GHC.Internal.Word.Word8", TkU32{}}, TkE{"Data.Sequence.Internal.Seq", TkList{}}, TkE{"Data.Sequence.Internal.ViewL", TkList{}}, TkE{"Text.Megaparsec.Internal.ParsecT", TkParsecT{}}, TkE{"Text.Megaparsec.Parsec", TkParsec{}}, TkE{"Text.Megaparsec.Error.ParseErrorBundle", TkPeb{}}, TkE{"Text.Megaparsec.Pos.SourcePos", TkSPos{}}, TkE{"Text.Megaparsec.Pos.Pos", TkPos{}}, TkE{"Text.Megaparsec.Stream.Token", TkToken{}}, TkE{"Text.Megaparsec.Stream.Tokens", TkTokens{}}]

def fd.tk.find(xs: List<&2, TkE>, +k: List<&2, U32>) -> Tk:
  match xs:
    case Nil{}:
      TkNone{}
    case TkE{s, v} <> t:
      Bool.pick(Tk, S.eq(S.b(s), k), v, fd.tk.find(t, k))

# a list type; a list with no element is Foldable's container, the marker
# List (Base's list functions are written for it)
def fd.ty.list(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case a <> t:
      fd.list(a)
    case Nil{}:
      fd.v("List")

def fd.ty.t2(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case a <> b <> t:
      fd.pair(a, b)
    case Nil{}:
      fd.v("Tuple2")
    case _:
      fd.todo("fold:tuple-type")

def fd.ty.t3(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case a <> b <> c <> t:
      fd.pair(a, fd.pair(b, c))
    case _:
      fd.todo("fold:tuple-type")

# Fix f, Cofree f a and CofreeF f a b (Data.Fix, Control.Comonad.Cofree,
# Control.Comonad.Trans.Cofree) are HsPrelude's (see The prelude), with the
# functor f a type function: a type written F<A> for all its arguments but
# the last is (r_ => F<A, r_>), a list's is (r_ => List<&2, r_>), and a
# type variable is itself.  Base t a (Data.Functor.Foldable's type family)
# is f a at Fix f and CofreeF f w a at Cofree f w.

def fd.rv() -> List<&2, U32>:
  S.b("r_")

# a spine with t after its last argument
def fd.args.snoc(+args: T.Bt, t: T.Bt) -> T.Bt:
  T.tba.args(List.append(&2, T.Bt, fd.spine(args), t <> Nil{}))

def fd.fn.var.if(list: Bool, n: List<&2, U32>, t: T.Bt) -> T.Bt:
  match list:
    case True{}:
      fd.list(t)
    case False{}:
      T.tba.call(T.BtVar{n}, [t])

def fd.fn.var(+n: List<&2, U32>, t: T.Bt) -> T.Bt:
  fd.fn.var.if(fd.is(n, "List"), n, t)

# the functor f (a type written for all its arguments but the last)
# applied to t
def fd.fn.at(f: T.Bt, t: T.Bt) -> T.Bt:
  match f:
    case T.BtTyApp{n, args}:
      T.BtTyApp{n, fd.args.snoc(args, t)}
    case T.BtVar{n}:
      fd.fn.var(n, t)
    case _:
      fd.todo("fold:functor")

# the functor f as a type function
def fd.fn.lam(f: T.Bt) -> T.Bt:
  match f:
    case T.BtVar{+n}:
      Bool.pick(T.Bt, fd.is(n, "List"), T.BtLam{T.BmLive{}, fd.rv(), fd.list(T.BtVar{fd.rv()})}, T.BtVar{n})
    case g:
      T.BtLam{T.BmLive{}, fd.rv(), fd.fn.at(g, T.BtVar{fd.rv()})}

# Twins. Bend's Data holds no function (a function is Type), and a layer of
# a monad's actions is one: the layer a cata at Reader or State hands its
# algebra, the argument of traverse id there. So each data type of the
# package with type variables has a twin D.fn: its last variable a Type,
# itself a Type, its constructors D.fn.C, its fields as D's but each of
# another of the package's types at the last variable that type's twin. The
# fold writes the twin wherever the last type argument is a function (or a
# twin): the type, its constructors in patterns and terms, Cofree's layer
# (HsPrelude.CofreeF.fn) and the cata (G.cata.fn, G.cata.cofree.fn). A
# twin's functions are used once, as Bend's Type is.

# whether a type, as the fold wrote it, is a function or a twin
def fd.isfn(t: T.Bt) -> Bool:
  match t:
    case T.BtPi{m, x, i, a, b}:
      True{}
    case T.BtTyApp{+n, a}:
      S.suffix(n, S.b(".fn"))
    case _:
      False{}

def fd.isfn.m(m: Maybe<&2, T.Bt>) -> Bool:
  match m:
    case Some{t}:
      fd.isfn(t)
    case None{}:
      False{}

def fd.isfn.last(+tys: List<&2, T.Bt>) -> Bool:
  fd.isfn.m(List.last(&2, T.Bt, tys))

def fd.cfn.go(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> Nil{}:
      S.b("fn") <> h <> Nil{}
    case h <> t:
      h <> fd.cfn.go(t)

# a constructor's twin: D.C as D.fn.C
def fd.cfn(+n: List<&2, U32>) -> List<&2, U32>:
  S.join(fd.cfn.go(S.split(n, 46)), 46)

# a type function (r_ => F<.., r_>) at the twin, (r_ => F.fn<.., r_>)
def fd.lam.fn(l: T.Bt) -> T.Bt:
  match l:
    case T.BtLam{m, x, T.BtTyApp{n, args}}:
      T.BtLam{m, x, T.BtTyApp{fd.cat(n, S.b(".fn")), args}}
    case _:
      fd.todo("fold:functor-twin")

# a constructor term at its twin (fn), under a partial application's lambdas
def fd.con.fn(fn: Bool, t: T.Bt) -> T.Bt:
  match fn t:
    case True{} T.BtCon{+n, a}:
      T.BtCon{fd.cfn(n), a}
    case True{} T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.con.fn(True{}, b)}
    case _ u:
      u

def fd.ty.fix(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case f <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.Fix"), T.tba.args([fd.fn.lam(f)])}
    case _:
      fd.todo("fold:fix-type")

def fd.ty.cofree(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case f <> a <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.Cofree"), T.tba.args([fd.fn.lam(f), a])}
    case _:
      fd.todo("fold:cofree-type")

def fd.ty.cofreef.at(fn: Bool, f: T.Bt, a: T.Bt, b: T.Bt) -> T.Bt:
  match fn:
    case True{}:
      T.BtTyApp{S.b("HsPrelude.CofreeF.fn"), T.tba.args([fd.lam.fn(fd.fn.lam(f)), a, b])}
    case False{}:
      T.BtTyApp{S.b("HsPrelude.CofreeF"), T.tba.args([fd.fn.lam(f), a, b])}

def fd.ty.cofreef(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case f <> a <> +b <> Nil{}:
      fd.ty.cofreef.at(fd.isfn(b), f, a, b)
    case _:
      fd.todo("fold:cofreef-type")

# h, t without the last element
def fd.init.go(t: List<&2, T.Bt>, h: T.Bt) -> List<&2, T.Bt>:
  match t:
    case Nil{}:
      Nil{}
    case h2 <> t2:
      h <> fd.init.go(t2, h2)

def fd.init(xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case h <> t:
      fd.init.go(t, h)
    case Nil{}:
      Nil{}

# a type function applied to a: its body with a for the variable, which
# fd.fn.lam put last
def fd.lam.at(l: T.Bt, a: T.Bt) -> T.Bt:
  match l:
    case T.BtLam{m, x, T.BtTyApp{n, args}}:
      T.BtTyApp{n, fd.args.snoc(T.tba.args(fd.init(fd.spine(args))), a)}
    case T.BtVar{n}:
      T.tba.call(T.BtVar{n}, [a])
    case _:
      fd.todo("fold:functor")

def fd.ty.base.at(fix: Bool, cof: Bool, rest: T.Bt, fn: Bool, l: T.Bt, a: T.Bt) -> T.Bt:
  match fix cof rest fn:
    case True{} _ _ False{}:
      fd.lam.at(l, a)
    case True{} _ _ True{}:
      fd.lam.at(fd.lam.fn(l), a)
    case False{} True{} T.BtArgs{w, _} False{}:
      T.BtTyApp{S.b("HsPrelude.CofreeF"), T.tba.args([l, w, a])}
    case False{} True{} T.BtArgs{w, _} True{}:
      T.BtTyApp{S.b("HsPrelude.CofreeF.fn"), T.tba.args([fd.lam.fn(l), w, a])}
    case _ _ _ _:
      fd.todo("type:Data.Functor.Foldable.Base")

def fd.ty.base.if(fix: Bool, cof: Bool, rest: T.Bt, l: T.Bt, +a: T.Bt) -> T.Bt:
  fd.ty.base.at(fix, cof, rest, fd.isfn(a), l, a)

def fd.ty.base.of(+n: List<&2, U32>, l: T.Bt, rest: T.Bt, a: T.Bt) -> T.Bt:
  fd.ty.base.if(fd.is(n, "HsPrelude.Fix"), fd.is(n, "HsPrelude.Cofree"), rest, l, a)

def fd.ty.base(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case T.BtTyApp{n, T.BtArgs{l, rest}} <> a <> Nil{}:
      fd.ty.base.of(n, l, rest, a)
    case _:
      fd.todo("type:Data.Functor.Foldable.Base")

# a type that is not Base's: the module's own or an earlier module's of its
# package, by its Bend name (None: neither)
def fd.tc.none(tn: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>, +args: List<&2, T.Bt>) -> T.Bt:
  match tn:
    case Some{+b}:
      T.BtTyApp{fd.bpick(fd.isfn.last(args), fd.cat(b, S.b(".fn")), b), T.tba.args(args)}
    case None{}:
      T.BtTodo{fd.cat(S.b("type:"), key)}

# State s a, and StateT s Identity a (Control.Monad.Trans.State, lazy or
# strict), is a function of the state to a result and the next state,
# S -> A & S (an &1 pair: A may be a function, as at <*>); State s alone, a
# monad argument, is the marker hs.State<S> (see Monads), Identity alone
# hs.Identity
def fd.spair(a: T.Bt, s: T.Bt) -> T.Bt:
  T.BtTyApp{S.b("Sigma"), T.tba.args([fd.v("&1"), fd.v("&1"), a, T.BtLam{T.BmLive{}, S.b("_"), s}])}

def fd.ty.st(+s: T.Bt, a: T.Bt) -> T.Bt:
  T.BtPi{T.BmLive{}, S.b("_"), False{}, s, fd.spair(a, s)}

def fd.ty.state(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case s <> a <> Nil{}:
      fd.ty.st(s, a)
    case s <> Nil{}:
      T.BtTyApp{S.b("hs.State"), T.tba.args([s])}
    case _:
      fd.todo("fold:state-type")

def fd.isid(t: T.Bt) -> Bool:
  match t:
    case T.BtTyApp{+n, T.BtANil{}}:
      fd.is(n, "hs.Identity")
    case _:
      False{}

def fd.ty.statet.if(id: Bool, args: List<&2, T.Bt>) -> T.Bt:
  match id:
    case True{}:
      fd.ty.state(args)
    case False{}:
      fd.todo("fold:statet-type")

def fd.ty.statet(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case s <> m <> t:
      fd.ty.statet.if(fd.isid(m), s <> t)
    case _:
      fd.todo("fold:statet-type")

def fd.ty.identity(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case Nil{}:
      fd.ty0("hs.Identity")
    case a <> Nil{}:
      a
    case _:
      fd.todo("fold:identity-type")

# ExceptT e m a (Control.Monad.Trans.Except) is its newtype's m (Either e a):
# over State s (StateT s Identity), a State whose result is an Either,
# S -> Either E A & S; over Identity, Either E A. ExceptT e m alone, a
# monad argument, is the marker hs.ExceptS<E, S> (Either's marker over
# Identity), ExceptT e alone (lift's transformer) hs.ExceptT<E>
def fd.either(e: T.Bt, a: T.Bt) -> T.Bt:
  T.BtTyApp{S.b("Either"), T.tba.args([fd.v("&2"), fd.v("&2"), e, a])}

# the monad under an ExceptT, as the fold wrote it
type Em is Data:
  EmState{s: T.Bt}
  EmId{}
  EmOther{}

def fd.em.one(+n: List<&2, U32>, s: T.Bt) -> Em:
  Bool.pick(Em, fd.is(n, "hs.State"), EmState{s}, EmOther{})

def fd.em.zero(+n: List<&2, U32>) -> Em:
  Bool.pick(Em, fd.is(n, "hs.Identity"), EmId{}, EmOther{})

def fd.em(m: T.Bt) -> Em:
  match m:
    case T.BtTyApp{+n, T.BtArgs{s, T.BtANil{}}}:
      fd.em.one(n, s)
    case T.BtTyApp{+n, T.BtANil{}}:
      fd.em.zero(n)
    case _:
      EmOther{}

def fd.ty.exc.full(k: Em, e: T.Bt, a: T.Bt) -> T.Bt:
  match k:
    case EmState{s}:
      fd.ty.st(s, fd.either(e, a))
    case EmId{}:
      fd.either(e, a)
    case EmOther{}:
      fd.todo("fold:exceptt-type")

def fd.ty.exc.mon(k: Em, e: T.Bt) -> T.Bt:
  match k:
    case EmState{s}:
      T.BtTyApp{S.b("hs.ExceptS"), T.tba.args([e, s])}
    case EmId{}:
      T.BtTyApp{S.b("Either"), T.tba.args([fd.v("&2"), fd.v("&2"), e])}
    case EmOther{}:
      fd.todo("fold:exceptt-type")

def fd.ty.exceptt(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case e <> m <> a <> Nil{}:
      fd.ty.exc.full(fd.em(m), e, a)
    case e <> m <> Nil{}:
      fd.ty.exc.mon(fd.em(m), e)
    case e <> Nil{}:
      T.BtTyApp{S.b("hs.ExceptT"), T.tba.args([e])}
    case _:
      fd.todo("fold:exceptt-type")

# ReaderT r m a (Control.Monad.Trans.Reader) is its newtype's r -> m a:
# over Identity (Reader r a) R -> A, over Either e R -> Either E A.
# ReaderT r m alone, a monad argument, is the marker hs.Reader<R> (over
# Identity) or hs.ReaderE<R, E> (over Either e), ReaderT r alone (lift's
# transformer) hs.ReaderT<R>
type Rm is Data:
  RmId{}
  RmEither{e: T.Bt}
  RmOther{}

def fd.rm.three(either: Bool, e: T.Bt) -> Rm:
  match either:
    case True{}:
      RmEither{e}
    case False{}:
      RmOther{}

def fd.rm(m: T.Bt) -> Rm:
  match m:
    case T.BtTyApp{+n, T.BtANil{}}:
      Bool.pick(Rm, fd.is(n, "hs.Identity"), RmId{}, RmOther{})
    case T.BtTyApp{n, T.BtArgs{a, T.BtArgs{b, T.BtArgs{e, T.BtANil{}}}}}:
      fd.rm.three(fd.is(n, "Either"), e)
    case _:
      RmOther{}

def fd.ty.rd.full(k: Rm, r: T.Bt, a: T.Bt) -> T.Bt:
  match k:
    case RmId{}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, a}
    case RmEither{e}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, fd.either(e, a)}
    case RmOther{}:
      fd.todo("fold:readert-type")

def fd.ty.rd.mon(k: Rm, r: T.Bt) -> T.Bt:
  match k:
    case RmId{}:
      T.BtTyApp{S.b("hs.Reader"), T.tba.args([r])}
    case RmEither{e}:
      T.BtTyApp{S.b("hs.ReaderE"), T.tba.args([r, e])}
    case RmOther{}:
      fd.todo("fold:readert-type")

def fd.ty.readert(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case r <> m <> a <> Nil{}:
      fd.ty.rd.full(fd.rm(m), r, a)
    case r <> m <> Nil{}:
      fd.ty.rd.mon(fd.rm(m), r)
    case r <> Nil{}:
      T.BtTyApp{S.b("hs.ReaderT"), T.tba.args([r])}
    case _:
      fd.todo("fold:readert-type")

# transformers' synonym Reader r (ReaderT r Identity), should GHC hand it
# over unexpanded
def fd.ty.reader(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case r <> t:
      fd.ty.readert(r <> fd.ty0("hs.Identity") <> t)
    case Nil{}:
      fd.todo("fold:readert-type")

# the markers hs.Reader<R> and hs.ReaderE<R, E> applied to more arguments
# (a synonym's use)
def fd.ty.rds(e: Bool, args: List<&2, T.Bt>) -> T.Bt:
  match e args:
    case False{} r <> a <> Nil{}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, a}
    case True{} r <> x <> a <> Nil{}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, fd.either(x, a)}
    case _ _:
      fd.todo("fold:readert-type")

# WriterT w m a (Control.Monad.Trans.Writer, strict or lazy) is its
# newtype's m (a, w): over Identity (Writer w a) A & W, over Either e
# Either E (A & W). WriterT w m alone, a monad argument, is the marker
# hs.Writer<W> (over Identity) or hs.WriterE<W, E> (over Either e),
# WriterT w alone (lift's transformer) hs.WriterT<W>
def fd.ty.wr.full(k: Rm, w: T.Bt, a: T.Bt) -> T.Bt:
  match k:
    case RmId{}:
      fd.pair(a, w)
    case RmEither{e}:
      fd.either(e, fd.pair(a, w))
    case RmOther{}:
      fd.todo("fold:writert-type")

def fd.ty.wr.mon(k: Rm, w: T.Bt) -> T.Bt:
  match k:
    case RmId{}:
      T.BtTyApp{S.b("hs.Writer"), T.tba.args([w])}
    case RmEither{e}:
      T.BtTyApp{S.b("hs.WriterE"), T.tba.args([w, e])}
    case RmOther{}:
      fd.todo("fold:writert-type")

def fd.ty.writert(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case w <> m <> a <> Nil{}:
      fd.ty.wr.full(fd.rm(m), w, a)
    case w <> m <> Nil{}:
      fd.ty.wr.mon(fd.rm(m), w)
    case w <> Nil{}:
      T.BtTyApp{S.b("hs.WriterT"), T.tba.args([w])}
    case _:
      fd.todo("fold:writert-type")

# transformers' synonym Writer w (WriterT w Identity)
def fd.ty.writer(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case w <> t:
      fd.ty.writert(w <> fd.ty0("hs.Identity") <> t)
    case Nil{}:
      fd.todo("fold:writert-type")

# the markers hs.Writer<W> and hs.WriterE<W, E> applied to more arguments
# (a synonym's use)
def fd.ty.wrs(e: Bool, args: List<&2, T.Bt>) -> T.Bt:
  match e args:
    case False{} w <> a <> Nil{}:
      fd.pair(a, w)
    case True{} w <> x <> a <> Nil{}:
      fd.either(x, fd.pair(a, w))
    case _ _:
      fd.todo("fold:writert-type")

# Data.Map's Map k v, Data.Set's Set k, IntMap v (Map Int v) and IntSet
# (Set Int) are HsPrelude's HsMap and HsSet (see The prelude)
def fd.ty.map(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case k <> v <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.HsMap"), T.tba.args([k, v])}
    case k <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.HsMap"), T.tba.args([k])}
    case Nil{}:
      fd.v("HsPrelude.HsMap")
    case _:
      fd.todo("fold:map-type")

def fd.ty.set(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case k <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.HsSet"), T.tba.args([k])}
    case Nil{}:
      fd.v("HsPrelude.HsSet")
    case _:
      fd.todo("fold:set-type")

def fd.ty.intmap(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case v <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.HsMap"), T.tba.args([fd.ty0("Nat"), v])}
    case _:
      fd.todo("fold:map-type")

def fd.ty.intset(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case Nil{}:
      T.BtTyApp{S.b("HsPrelude.HsSet"), T.tba.args([fd.ty0("Nat")])}
    case _:
      fd.todo("fold:set-type")

# the marker hs.ExceptS<E, S> applied to more arguments (a synonym's use)
def fd.ty.exs(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case e <> s <> a <> Nil{}:
      fd.ty.st(s, fd.either(e, a))
    case e <> s <> Nil{}:
      T.BtTyApp{S.b("hs.ExceptS"), T.tba.args([e, s])}
    case _:
      fd.todo("fold:exceptt-type")

# megaparsec's ParsecT e s Identity a (Parsec e s a) is HsPrelude's parser,
# a function of the state to a reply, HsPcSt -> HsPcRep<A> (see HsPc in
# the prelude); ParsecT e s Identity alone, a monad argument, the marker
# hs.Pc. ParseErrorBundle is HsPcBundle, SourcePos HsPcPos, Pos a Nat, and
# the Stream's Token and Tokens (at String) Char and String.
def fd.ty.pc(a: T.Bt) -> T.Bt:
  T.BtPi{T.BmLive{}, S.b("_"), False{}, fd.ty0("HsPrelude.HsPcSt"), T.BtTyApp{S.b("HsPrelude.HsPcRep"), T.tba.args([a])}}

def fd.ty.parsect.if(id: Bool, args: List<&2, T.Bt>) -> T.Bt:
  match id args:
    case True{} a <> Nil{}:
      fd.ty.pc(a)
    case True{} Nil{}:
      fd.ty0("hs.Pc")
    case _ _:
      fd.todo("fold:parsect-type")

def fd.ty.parsect(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case e <> s <> m <> t:
      fd.ty.parsect.if(fd.isid(m), t)
    case _:
      fd.todo("fold:parsect-type")

def fd.ty.parsec(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case e <> s <> t:
      fd.ty.parsect.if(True{}, t)
    case _:
      fd.todo("fold:parsect-type")

def fd.tc.base(k: Tk, args: List<&2, T.Bt>) -> T.Bt:
  match k:
    case TkNat{}:
      fd.ty0("Nat")
    case TkBool{}:
      fd.ty0("Bool")
    case TkChar{}:
      fd.ty0("Char")
    case TkF32{}:
      fd.ty0("F32")
    case TkStr{}:
      fd.list(fd.ty0("Char"))
    case TkShowS{}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, fd.list(fd.ty0("Char")), fd.list(fd.ty0("Char"))}
    case TkUnit{}:
      fd.ty0("Unit")
    case TkCmp{}:
      fd.ty0("Cmp")
    case TkList{}:
      fd.ty.list(args)
    case TkMaybe{}:
      T.BtTyApp{S.b("Maybe"), T.tba.args(fd.v("&2") <> args)}
    case TkEither{}:
      T.BtTyApp{S.b("Either"), T.tba.args(fd.v("&2") <> fd.v("&2") <> args)}
    case TkT2{}:
      fd.ty.t2(args)
    case TkT3{}:
      fd.ty.t3(args)
    case TkFix{}:
      fd.ty.fix(args)
    case TkCofree{}:
      fd.ty.cofree(args)
    case TkCofreeF{}:
      fd.ty.cofreef(args)
    case TkBase{}:
      fd.ty.base(args)
    case TkState{}:
      fd.ty.state(args)
    case TkStateT{}:
      fd.ty.statet(args)
    case TkIdentity{}:
      fd.ty.identity(args)
    case TkExceptT{}:
      fd.ty.exceptt(args)
    case TkReaderT{}:
      fd.ty.readert(args)
    case TkReader{}:
      fd.ty.reader(args)
    case TkWriterT{}:
      fd.ty.writert(args)
    case TkWriter{}:
      fd.ty.writer(args)
    case TkMap{}:
      fd.ty.map(args)
    case TkEmpty{}:
      fd.ty0("Empty")
    case TkHsInt{}:
      fd.ty0("HsPrelude.HsInt")
    case TkDigest{}:
      fd.ty0("HsPrelude.HsDigest")
    case TkRat{}:
      fd.ty0("HsPrelude.HsRational")
    case TkU32{}:
      fd.ty0("U32")
    case TkSet{}:
      fd.ty.set(args)
    case TkIntMap{}:
      fd.ty.intmap(args)
    case TkIntSet{}:
      fd.ty.intset(args)
    case TkParsecT{}:
      fd.ty.parsect(args)
    case TkParsec{}:
      fd.ty.parsec(args)
    case TkPeb{}:
      fd.ty0("HsPrelude.HsPcBundle")
    case TkSPos{}:
      fd.ty0("HsPrelude.HsPcPos")
    case TkPos{}:
      fd.ty0("Nat")
    case TkToken{}:
      fd.ty0("Char")
    case TkTokens{}:
      fd.list(fd.ty0("Char"))
    case TkNone{}:
      fd.todo("fold:type")

def fd.tk.none(k: Tk) -> Bool:
  match k:
    case TkNone{}:
      True{}
    case _:
      False{}

def fd.tc.of.if(none: Bool, k: Tk, tn: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>, args: List<&2, T.Bt>) -> T.Bt:
  match none:
    case True{}:
      fd.tc.none(tn, key, args)
    case False{}:
      fd.tc.base(k, args)

def fd.tc.of(+k: Tk, tn: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>, args: List<&2, T.Bt>) -> T.Bt:
  fd.tc.of.if(fd.tk.none(k), k, tn, key, args)

# Base's constructors ----------------------------------------------------------

type Cb is Data:
  CbCons{}
  CbNil{}
  CbTrue{}
  CbFalse{}
  CbJust{}
  CbNothing{}
  CbLeft{}
  CbRight{}
  CbLT{}
  CbEQ{}
  CbGT{}
  CbUnit{}
  CbT2{}
  CbT3{}
  CbFix{}
  CbCofree{}
  CbCofreeF{}
  CbNt{}
  CbNone{}

type CbE is Data:
  CbE{k: String, v: Cb}

def fd.cbtab() -> List<&2, CbE>:
  [CbE{"GHC.Types.:", CbCons{}}, CbE{"GHC.Types.[]", CbNil{}}, CbE{"Data.Sequence.Internal.EmptyL", CbNil{}}, CbE{"Data.Sequence.Internal.:<", CbCons{}}, CbE{"GHC.Types.True", CbTrue{}}, CbE{"GHC.Types.False", CbFalse{}}, CbE{"GHC.Internal.Maybe.Just", CbJust{}}, CbE{"GHC.Internal.Maybe.Nothing", CbNothing{}}, CbE{"GHC.Internal.Data.Either.Left", CbLeft{}}, CbE{"GHC.Internal.Data.Either.Right", CbRight{}}, CbE{"GHC.Types.LT", CbLT{}}, CbE{"GHC.Types.EQ", CbEQ{}}, CbE{"GHC.Types.GT", CbGT{}}, CbE{"GHC.Tuple.()", CbUnit{}}, CbE{"GHC.Tuple.(,)", CbT2{}}, CbE{"GHC.Tuple.(,,)", CbT3{}}, CbE{"Data.Fix.Fix", CbFix{}}, CbE{"Control.Comonad.Cofree.:<", CbCofree{}}, CbE{"Control.Comonad.Trans.Cofree.:<", CbCofreeF{}}, CbE{"Control.Monad.Trans.Writer.Strict.WriterT", CbNt{}}, CbE{"Control.Monad.Trans.Writer.Lazy.WriterT", CbNt{}}]

def fd.cb.find(xs: List<&2, CbE>, +k: List<&2, U32>) -> Cb:
  match xs:
    case Nil{}:
      CbNone{}
    case CbE{s, v} <> t:
      Bool.pick(Cb, S.eq(S.b(s), k), v, fd.cb.find(t, k))

def fd.cb.n(c: Cb) -> Nat:
  match c:
    case CbCons{}:
      2n
    case CbJust{}:
      1n
    case CbLeft{}:
      1n
    case CbRight{}:
      1n
    case CbT2{}:
      2n
    case CbT3{}:
      3n
    case CbFix{}:
      1n
    case CbCofree{}:
      2n
    case CbCofreeF{}:
      2n
    case CbNt{}:
      1n
    case _:
      0n

# a constructor of Base's with its arguments (patterns or terms)
def fd.cb.mk(c: Cb, xs: List<&2, T.Bt>) -> T.Bt:
  match c xs:
    case CbCons{} h <> t <> _:
      T.BtCon{S.b("Con"), T.tba.args([h, t])}
    case CbNil{} _:
      fd.con0("Nil")
    case CbTrue{} _:
      fd.con0("True")
    case CbFalse{} _:
      fd.con0("False")
    case CbJust{} a <> _:
      T.BtCon{S.b("Some"), T.tba.args([a])}
    case CbNothing{} _:
      fd.con0("None")
    case CbLeft{} a <> _:
      T.BtCon{S.b("Inl"), T.tba.args([a])}
    case CbRight{} a <> _:
      T.BtCon{S.b("Inr"), T.tba.args([a])}
    case CbLT{} _:
      fd.con0("LT")
    case CbEQ{} _:
      fd.con0("EQ")
    case CbGT{} _:
      fd.con0("GT")
    case CbUnit{} _:
      fd.con0("Unit")
    case CbT2{} a <> b <> _:
      T.BtCon{S.b("Tuple"), T.tba.args([a, b])}
    case CbT3{} a <> b <> c <> _:
      T.BtCon{S.b("Tuple"), T.tba.args([a, T.BtCon{S.b("Tuple"), T.tba.args([b, c])}])}
    case CbFix{} a <> _:
      T.BtCon{S.b("HsPrelude.Fix.Fix"), T.tba.args([a])}
    case CbCofree{} a <> b <> _:
      T.BtCon{S.b("HsPrelude.Cofree.Cofree"), T.tba.args([a, b])}
    case CbCofreeF{} a <> b <> _:
      T.BtCon{S.b("HsPrelude.CofreeF.CofreeF"), T.tba.args([a, b])}
    case CbNt{} a <> _:
      a
    case _ _:
      fd.todo("fold:constructor")

# The module's own names ----------------------------------------------------

# a constructor of the module: its name, its type's, its arity, and its
# field names (none when it is not a record)
type Ctr is Data:
  Ctr{c: List<&2, U32>, t: List<&2, U32>, n: Nat, fs: List<&2, List<&2, U32>>}

# a def of the module (its Haskell name) and its arity
type Df is Data:
  Df{n: List<&2, U32>, a: Nat}

def fd.ctr.find(xs: List<&2, Ctr>, +c: List<&2, U32>) -> Maybe<&2, Ctr>:
  match xs:
    case Nil{}:
      None{}
    case Ctr{+k, t, n, fs} <> rest:
      Bool.pick(Maybe<&2, Ctr>, S.eq(k, c), Some{Ctr{k, t, n, fs}}, fd.ctr.find(rest, c))

def fd.df.find(xs: List<&2, Df>, +n: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Df{k, a} <> rest:
      Bool.pick(Maybe<&2, Nat>, S.eq(k, n), Some{a}, fd.df.find(rest, n))

# a field's role
type Fr is Data:
  FrCopy{}
  FrRec{}
  FrIn{k: List<&2, U32>}
  FrMaybe{r: Fr}
  FrPair{a: Fr, b: Fr}
  FrList{r: Fr}
  FrNo{}

# a constructor of a functor: its Bend name, its fields' roles
type Fc is Data:
  Fc{c: List<&2, U32>, rs: List<&2, Fr>}

# a functor: its key M.G, its Bend name, the type variables before the
# last, its constructors
type Fz is Data:
  Fz{k: List<&2, U32>, b: List<&2, U32>, tvs: List<&2, List<&2, U32>>, cs: List<&2, Fc>}

# What the modules of a package before this one have in (package mode).
# Each is known by its key M.NAME and written with the alias of M's file,
# M with each . as _: a def (its Bend name and arity), a constructor (its
# Bend name, arity and fields), a type (its Bend name).
type Ix is Data:
  IxDef{k: List<&2, U32>, b: List<&2, U32>, a: Nat}
  IxCon{k: List<&2, U32>, b: List<&2, U32>, n: Nat, fs: List<&2, List<&2, U32>>}
  IxTy{k: List<&2, U32>, b: List<&2, U32>}
  IxFun{k: List<&2, U32>, b: List<&2, U32>, cs: List<&2, Fc>}

# a synonym of an earlier module: its key and its (synonym ...), folded
# again in each module that uses it (its types are that module's imports)
type Sy is Data:
  Sy{k: List<&2, U32>, x: X.Sx}

# a def's template flags (see Templates), by its Bend name
type Tf is Data:
  Tf{n: List<&2, U32>, fl: List<&2, Bool>}

# A package so far: its modules, the aliases of those that wrote a file,
# what they have in, their synonyms, and their defs' template flags.  A
# module alone has fd.px0().
type Px is Data:
  Px{home: List<&2, List<&2, U32>>, files: List<&2, List<&2, U32>>, ix: List<&2, Ix>, sy: List<&2, Sy>, tfs: List<&2, Tf>, dt: List<&2, T.BItem>}

def fd.px0() -> Px:
  Px{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def fd.px.home(p: Px) -> List<&2, List<&2, U32>>:
  match p:
    case Px{h, f, i, s, t, z}:
      h

def fd.px.files(p: Px) -> List<&2, List<&2, U32>>:
  match p:
    case Px{h, f, i, s, t, z}:
      f

def fd.px.ix(p: Px) -> List<&2, Ix>:
  match p:
    case Px{h, f, i, s, t, z}:
      i

def fd.px.sy(p: Px) -> List<&2, Sy>:
  match p:
    case Px{h, f, i, s, t, z}:
      s

def fd.px.tfs(p: Px) -> List<&2, Tf>:
  match p:
    case Px{h, f, i, s, t, z}:
      t

# the data types of the modules before, written as this module names them
# (Alias.T, Alias.T.C): the fuel's defaults take theirs
def fd.px.dt(p: Px) -> List<&2, T.BItem>:
  match p:
    case Px{h, f, i, s, t, z}:
      z

def fd.ix.key(i: Ix) -> List<&2, U32>:
  match i:
    case IxDef{k, b, a}:
      k
    case IxCon{k, b, n, fs}:
      k
    case IxTy{k, b}:
      k
    case IxFun{k, b, cs}:
      fd.cat(k, S.b("/functor"))

def fd.ix.hit(+xs: List<&2, Ix>, +k: List<&2, U32>) -> Bool:
  match xs:
    case h <> t:
      S.eq(fd.ix.key(h), k)
    case Nil{}:
      False{}

def fd.ix.go(xs: List<&2, Ix>, +k: List<&2, U32>, hit: Bool) -> Maybe<&2, Ix>:
  match xs hit:
    case h <> t True{}:
      Some{h}
    case h <> +t False{}:
      fd.ix.go(t, k, fd.ix.hit(t, k))
    case _ _:
      None{}

# what an earlier module of the package has in under the key k
def fd.ix.find(+xs: List<&2, Ix>, +k: List<&2, U32>) -> Maybe<&2, Ix>:
  fd.ix.go(xs, k, fd.ix.hit(xs, k))

# a type and its constructor may share a key (data T = T ..): a value's
# lookup (ty False) skips the types, a type's (ty True) takes only them
def fd.ix.isty(h: Ix) -> Bool:
  match h:
    case IxTy{k, b}:
      True{}
    case _:
      False{}

def fd.ix.hitv(+xs: List<&2, Ix>, +k: List<&2, U32>, +ty: Bool) -> Bool:
  match xs:
    case +h <> t:
      Bool.and(S.eq(fd.ix.key(h), k), Bool.not(Bool.xor(fd.ix.isty(h), ty)))
    case Nil{}:
      False{}

def fd.ix.gov(xs: List<&2, Ix>, +k: List<&2, U32>, +ty: Bool, hit: Bool) -> Maybe<&2, Ix>:
  match xs hit:
    case h <> t True{}:
      Some{h}
    case h <> +t False{}:
      fd.ix.gov(t, k, ty, fd.ix.hitv(t, k, ty))
    case _ _:
      None{}

def fd.ix.findv(+xs: List<&2, Ix>, +k: List<&2, U32>, +ty: Bool) -> Maybe<&2, Ix>:
  fd.ix.gov(xs, k, ty, fd.ix.hitv(xs, k, ty))

def fd.ix.keys(xs: List<&2, Ix>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case h <> t:
      fd.ix.keys(t, fd.ix.key(h) <> acc)
    case Nil{}:
      acc

def fd.sy.keys(xs: List<&2, Sy>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Sy{k, x} <> t:
      fd.sy.keys(t, k <> acc)
    case Nil{}:
      acc

# the survey's view of the package: its modules, and every key it has in
def fd.px.imp(+p: Px) -> V.Imp:
  V.Imp{fd.px.home(p), fd.ix.keys(fd.px.ix(p), fd.sy.keys(fd.px.sy(p), Nil{}))}

# What the fold knows where it is: the module's name, constructors and
# defs, the type of the right-hand side it is in (None in an argument),
# the type arguments a recursive call passes, the locals in scope, and the
# module's type synonyms.

# a type synonym of the module: its Haskell name, its type variables, and
# its right-hand side, folded
type Syn is Data:
  Syn{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, body: T.Bt}

# a local's type, folded (see Lifting)
type Lt is Data:
  Lt{x: List<&2, U32>, t: T.Bt}

type Env is Data:
  Env{m: List<&2, U32>, cons: List<&2, Ctr>, defs: List<&2, Df>, res: Maybe<&2, T.Bt>, self: List<&2, T.Bt>, ls: List<&2, List<&2, U32>>, syn: List<&2, Syn>, px: Px, lt: List<&2, Lt>}

def fd.env.m(e: Env) -> List<&2, U32>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      m

def fd.env.cons(e: Env) -> List<&2, Ctr>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      c

def fd.env.defs(e: Env) -> List<&2, Df>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      d

def fd.env.res(e: Env) -> Maybe<&2, T.Bt>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      r

def fd.env.self(e: Env) -> List<&2, T.Bt>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      s

def fd.env.ls(e: Env) -> List<&2, List<&2, U32>>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      l

def fd.env.syn(e: Env) -> List<&2, Syn>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      y

def fd.env.px(e: Env) -> Px:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      p

# the package's modules before this one (none for a module alone)
def fd.env.home(e: Env) -> List<&2, List<&2, U32>>:
  fd.px.home(fd.env.px(e))

def fd.env.ix(e: Env) -> List<&2, Ix>:
  fd.px.ix(fd.env.px(e))

def fd.withsyn(e: Env, ys: List<&2, Syn>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, r, s, l, ys, p, q}

def fd.withres(e: Env, t: T.Bt) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, Some{t}, s, l, y, p, q}

def fd.notail(e: Env) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, None{}, s, l, y, p, q}

def fd.addls(e: Env, xs: List<&2, List<&2, U32>>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, r, s, List.append(&2, List<&2, U32>, xs, l), y, p, q}

def fd.withself(e: Env, ts: List<&2, T.Bt>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, r, ts, l, y, p, q}

def fd.env.lt(e: Env) -> List<&2, Lt>:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      q

# locals in scope with their types, in front of those already there
def fd.addlts(e: Env, xs: List<&2, Lt>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, r, s, l, y, p, List.append(&2, Lt, xs, q)}

# a local's type: the innermost local of that name
def fd.lt.find(xs: List<&2, Lt>, +x: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match xs:
    case Nil{}:
      None{}
    case Lt{+y, t} <> r:
      Bool.pick(Maybe<&2, T.Bt>, S.eq(y, x), Some{t}, fd.lt.find(r, x))

# Calls ---------------------------------------------------------------------

# the lambdas a call k arguments short takes: x_i => .. => mk(args ++ [x_i, ..])
def fd.eta(k: Nat, +i: Nat, mk: List<&2, T.Bt> -> T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match k:
    case 0n:
      mk(args)
    case 1n+p:
      +x = fd.cat(S.b("x_"), fd.nshow(i))
      T.BtLam{T.BmLive{}, x, fd.eta(p, 1n+i, mk, List.append(&2, T.Bt, args, T.BtVar{x} <> Nil{}))}

def fd.sat.of(c: Cmp, +n: Nat, +len: Nat, +all: List<&2, T.Bt>, mk: List<&2, T.Bt> -> T.Bt) -> T.Bt:
  match c:
    case LT{}:
      fd.eta(Nat.sub(n, len), 1n, mk, all)
    case EQ{}:
      mk(all)
    case GT{}:
      T.BtApp{mk(List.take(&2, T.Bt, all, n)), T.tba.args(List.drop(&2, T.Bt, all, n))}

# a call of something that takes n arguments: lambdas for the missing
# ones, an application for the extra ones
def fd.sat(+n: Nat, +all: List<&2, T.Bt>, mk: List<&2, T.Bt> -> T.Bt) -> T.Bt:
  +len = List.length(&2, T.Bt, all)
  fd.sat.of(Nat.cmp(len, n), n, len, all, mk)

# whether no free variable of a term is a local (a template's argument
# must be closed)
def fd.closed.go(fs: List<&2, List<&2, U32>>, +ls: List<&2, List<&2, U32>>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.not(S.mem(h, ls)), fd.closed.go(t, ls))

# (whether it is closed is decided once the module's templates are known:
# see Templates)
def fd.tpl(+ls: List<&2, List<&2, U32>>, +f: T.Bt) -> T.Bt:
  T.BtTplArg{f}

# Base's functions ------------------------------------------------------------

# Which one a Haskell function of base is; the comparisons and the
# arithmetic carry the name of Base's def (Nat.is_lt, ...).
type Bf is Data:
  BfCmp{op: String}
  BfNum{op: String}
  BfAnd{}
  BfOr{}
  BfNot{}
  BfTrue{}
  BfAppend{}
  BfLength{}
  BfNull{}
  BfReverse{}
  BfConcat{}
  BfTake{}
  BfDrop{}
  BfReplicate{}
  BfMap{}
  BfFilter{}
  BfAny{}
  BfAll{}
  BfFoldr{}
  BfFoldl{}
  BfElem{}
  BfSum{}
  BfProduct{}
  BfAndL{}
  BfOrL{}
  BfConcatMap{}
  BfShow{}
  BfId{}
  BfConst{}
  BfSucc{}
  BfUnFix{}
  BfProject{}
  BfEmbed{}
  BfCata{}
  BfBind{}
  BfThen{}
  BfPure{}
  BfFmap{}
  BfMaybe{}
  BfFromMaybe{}
  BfEither{}
  BfSemi{}
  BfAp{}
  BfGet{}
  BfPut{}
  BfModify{}
  BfGets{}
  BfEval{}
  BfExec{}
  BfRun{}
  BfThrow{}
  BfRunExc{}
  BfWhen{}
  BfUnless{}
  BfVoid{}
  BfBindR{}
  BfForM_{}
  BfMapM_{}
  BfForM{}
  BfMapM{}
  BfSeq{}
  BfFoldM{}
  BfFilterM{}
  BfZipWithM_{}
  BfDm{d: String, r: String, p: String, nt: Nat, n: Nat}
  BfAbsurd{}
  BfNeg{op: String}
  BfConv{}
  BfIdAt{}
  BfSubtract{}
  BfLift2{}
  BfZ{op: String}
  BfRange{}
  BfOne{f: String}
  BfParity{op: String}
  BfDmF{d: String, r: String, p: String, nt: Nat, n: Nat}
  BfBi{op: String}
  BfFlip{}
  BfTrace{}
  BfMempty{}
  BfMconcat{}
  BfShowsPrec{}
  BfShows{}
  BfAlt{}
  BfEmpty{}
  BfLeft{}
  BfConstL{}
  BfFail{}
  BfPc{f: String, d: Nat, n: Nat}
  BfBound{hi: Bool}
  BfAsk{}
  BfLocal{}
  BfLocalT{}
  BfAsks{}
  BfLift{}
  BfWriter{}
  BfNone{}

type BfE is Data:
  BfE{k: String, v: Bf}

# Data.Map's, Data.IntMap's, Data.Set's and Data.IntSet's functions the fold
# writes (see fd.dm): a name, HsPrelude's def, the roles of GHC's type
# arguments at Map (Set) and at IntMap (IntSet), the def's templates, how
# many of the arguments lead as templates, the arity
type DmS is Data:
  DmS{n: String, d: String, rm: String, ri: String, p: String, nt: Nat, k: Nat}

def fd.dm.specs.map1() -> List<&2, DmS>:
  [DmS{"empty", "HsMap.empty", "KV", "V", "KV", 0n, 0n}, DmS{"singleton", "HsMap.singleton", "KV", "V", "KV", 0n, 2n}, DmS{"insert", "HsMap.insert", "KV", "V", "KVc", 0n, 3n}, DmS{"insertWith", "HsMap.insertWith", "KV", "V", "KVc", 1n, 4n}, DmS{"lookup", "HsMap.lookup", "KV", "V", "KVc", 0n, 2n}, DmS{"member", "HsMap.member", "KV", "V", "KVc", 0n, 2n}, DmS{"notMember", "HsMap.notMember", "KV", "V", "KVc", 0n, 2n}, DmS{"findWithDefault", "HsMap.findWithDefault", "KV", "V", "KVc", 0n, 3n}, DmS{"delete", "HsMap.delete", "KV", "V", "KVc", 0n, 2n}]

def fd.dm.specs.map2() -> List<&2, DmS>:
  [DmS{"adjust", "HsMap.adjust", "KV", "V", "KVc", 1n, 3n}, DmS{"toList", "HsMap.toList", "KV", "V", "KV", 0n, 1n}, DmS{"toAscList", "HsMap.toList", "KV", "V", "KV", 0n, 1n}, DmS{"assocs", "HsMap.toList", "KV", "V", "KV", 0n, 1n}, DmS{"fromList", "HsMap.fromList", "KV", "V", "KVc", 0n, 1n}, DmS{"fromAscList", "HsMap.fromList", "KV", "V", "KVc", 0n, 1n}, DmS{"fromDistinctAscList", "HsMap.fromList", "KV", "V", "KVc", 0n, 1n}, DmS{"fromListWith", "HsMap.fromListWith", "KV", "V", "KVc", 1n, 2n}, DmS{"elems", "HsMap.elems", "KV", "V", "KV", 0n, 1n}]

def fd.dm.specs.map3() -> List<&2, DmS>:
  [DmS{"keys", "HsMap.keys", "KV", "V", "KV", 0n, 1n}, DmS{"keysSet", "HsMap.keysSet", "KV", "V", "KV", 0n, 1n}, DmS{"size", "HsMap.isize", "KV", "V", "KV", 0n, 1n}, DmS{"null", "HsMap.null", "KV", "V", "KV", 0n, 1n}, DmS{"union", "HsMap.union", "KV", "V", "KVc", 0n, 2n}, DmS{"unionWith", "HsMap.unionWith", "KV", "V", "KVc", 1n, 3n}, DmS{"difference", "HsMap.difference", "KVW", "VW", "KVWc", 0n, 2n}, DmS{"map", "HsMap.map", "VWK", "VW", "KVW", 1n, 2n}, DmS{"mapWithKey", "HsMap.mapWithKey", "KVW", "VW", "KVW", 1n, 2n}]

def fd.dm.specs.map4() -> List<&2, DmS>:
  [DmS{"filter", "HsMap.filter", "VK", "V", "KV", 1n, 2n}, DmS{"filterWithKey", "HsMap.filterWithKey", "KV", "V", "KV", 1n, 2n}, DmS{"foldr", "HsMap.foldr", "VBK", "VB", "KVB", 1n, 3n}, DmS{"foldrWithKey", "HsMap.foldrWithKey", "KVB", "VB", "KVB", 1n, 3n}]

def fd.dm.specs.set1() -> List<&2, DmS>:
  [DmS{"empty", "HsSet.empty", "K", "", "K", 0n, 0n}, DmS{"singleton", "HsSet.singleton", "K", "", "K", 0n, 1n}, DmS{"insert", "HsSet.insert", "K", "", "Kc", 0n, 2n}, DmS{"member", "HsSet.member", "K", "", "Kc", 0n, 2n}, DmS{"notMember", "HsSet.notMember", "K", "", "Kc", 0n, 2n}, DmS{"delete", "HsSet.delete", "K", "", "Kc", 0n, 2n}, DmS{"toList", "HsSet.toList", "K", "", "K", 0n, 1n}, DmS{"toAscList", "HsSet.toList", "K", "", "K", 0n, 1n}, DmS{"elems", "HsSet.toList", "K", "", "K", 0n, 1n}]

def fd.dm.specs.set2() -> List<&2, DmS>:
  [DmS{"fromList", "HsSet.fromList", "K", "", "Kc", 0n, 1n}, DmS{"union", "HsSet.union", "K", "", "Kc", 0n, 2n}, DmS{"difference", "HsSet.difference", "K", "", "Kc", 0n, 2n}, DmS{"\\\\", "HsSet.difference", "K", "", "Kc", 0n, 2n}, DmS{"filter", "HsSet.filter", "K", "", "K", 1n, 2n}, DmS{"size", "HsSet.isize", "K", "", "K", 0n, 1n}, DmS{"null", "HsSet.null", "K", "", "K", 0n, 1n}, DmS{"unions", "HsSet.unions", "XK", "X", "Kc", 0n, 1n}]

# (map5 and set3: prelude/HsMapMore.bend's; unionsWith's Foldable a list)
def fd.dm.specs.map5() -> List<&2, DmS>:
  [DmS{"intersectionWith", "HsMap.intersectionWith", "KVWX", "VWX", "KVWXc", 1n, 3n}, DmS{"restrictKeys", "HsMap.restrictKeys", "KV", "V", "KVc", 0n, 2n}, DmS{"withoutKeys", "HsMap.withoutKeys", "KV", "V", "KVc", 0n, 2n}, DmS{"fromSet", "HsMap.fromSet", "KV", "V", "KV", 1n, 2n}, DmS{"unionWithKey", "HsMap.unionWithKey", "KV", "V", "KVc", 1n, 3n}, DmS{"unionsWith", "HsMap.unionsWith", "XKV", "XV", "KVc", 1n, 2n}, DmS{"split", "HsMap.split", "KV", "V", "KVc", 0n, 2n}]

# (Map's !: partial, prelude/HsPartial.bend)
def fd.dm.specs.map6() -> List<&2, DmS>:
  [DmS{"!", "HsMap.at", "KV", "V", "KVc", 0n, 2n}]

def fd.dm.specs.set3() -> List<&2, DmS>:
  [DmS{"intersection", "HsSet.intersection", "K", "", "Kc", 0n, 2n}]

def fd.dm.specs.maps() -> List<&2, DmS>:
  List.concat(&2, DmS, [fd.dm.specs.map1(), fd.dm.specs.map2(), fd.dm.specs.map3(), fd.dm.specs.map4(), fd.dm.specs.map5(), fd.dm.specs.map6()])

def fd.dm.specs.sets() -> List<&2, DmS>:
  List.concat(&2, DmS, [fd.dm.specs.set1(), fd.dm.specs.set2(), fd.dm.specs.set3()])

def fd.dm.tab.map(xs: List<&2, DmS>) -> List<&2, BfE>:
  match xs:
    case Nil{}:
      Nil{}
    case DmS{+n, +d, +rm, +ri, +p, +nt, +k} <> t:
      BfE{"Data.Map.Internal." ++ n, BfDm{d, rm, p, nt, k}} <> BfE{"Data.Map.Strict.Internal." ++ n, BfDm{d, rm, p, nt, k}} <> BfE{"Data.IntMap.Internal." ++ n, BfDm{d, ri, p, nt, k}} <> BfE{"Data.IntMap.Strict.Internal." ++ n, BfDm{d, ri, p, nt, k}} <> fd.dm.tab.map(t)

def fd.dm.tab.set(xs: List<&2, DmS>) -> List<&2, BfE>:
  match xs:
    case Nil{}:
      Nil{}
    case DmS{+n, +d, +rm, +ri, +p, +nt, +k} <> t:
      BfE{"Data.Set.Internal." ++ n, BfDm{d, rm, p, nt, k}} <> BfE{"Data.IntSet.Internal." ++ n, BfDm{d, ri, p, nt, k}} <> fd.dm.tab.set(t)


def fd.bftab0() -> List<&2, BfE>:
  [BfE{"GHC.Classes.==", BfCmp{"is_eq"}}, BfE{"GHC.Classes./=", BfCmp{"is_ne"}}, BfE{"GHC.Classes.<", BfCmp{"is_lt"}}, BfE{"GHC.Classes.<=", BfCmp{"is_le"}}, BfE{"GHC.Classes.>", BfCmp{"is_gt"}}, BfE{"GHC.Classes.>=", BfCmp{"is_ge"}}, BfE{"GHC.Classes.compare", BfCmp{"cmp"}}, BfE{"GHC.Classes.max", BfCmp{"max"}}, BfE{"GHC.Classes.min", BfCmp{"min"}}, BfE{"GHC.Classes.&&", BfAnd{}}, BfE{"GHC.Classes.||", BfOr{}}, BfE{"GHC.Classes.not", BfNot{}}, BfE{"GHC.Internal.Base.otherwise", BfTrue{}}, BfE{"GHC.Internal.Num.+", BfNum{"add"}}, BfE{"GHC.Internal.Num.*", BfNum{"mul"}}, BfE{"GHC.Internal.Real.div", BfNum{"div"}}, BfE{"GHC.Internal.Real.mod", BfNum{"mod"}}, BfE{"GHC.Internal.Real.quot", BfNum{"quot"}}, BfE{"GHC.Internal.Real.rem", BfNum{"rem"}}, BfE{"GHC.Internal.Real.^", BfNum{"pow"}}, BfE{"GHC.Internal.Real./", BfNum{"div"}}, BfE{"GHC.Internal.Real.%", BfNum{"ratio"}}, BfE{"GHC.Internal.Real.gcd", BfNum{"gcd"}}, BfE{"GHC.Internal.Real.lcm", BfNum{"lcm"}}, BfE{"GHC.Internal.Base.++", BfAppend{}}, BfE{"GHC.Internal.Data.Foldable.length", BfLength{}}, BfE{"GHC.Internal.Data.Foldable.null", BfNull{}}, BfE{"GHC.Internal.List.reverse", BfReverse{}}, BfE{"GHC.Internal.Data.Foldable.concat", BfConcat{}}, BfE{"GHC.Internal.List.take", BfTake{}}, BfE{"GHC.Internal.List.drop", BfDrop{}}, BfE{"GHC.Internal.List.replicate", BfReplicate{}}, BfE{"GHC.Internal.Base.map", BfMap{}}, BfE{"GHC.Internal.List.filter", BfFilter{}}, BfE{"GHC.Internal.Data.Foldable.any", BfAny{}}, BfE{"GHC.Internal.Data.Foldable.all", BfAll{}}, BfE{"GHC.Internal.Data.Foldable.foldr", BfFoldr{}}, BfE{"GHC.Internal.Data.Foldable.foldl", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.foldl'", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.elem", BfElem{}}, BfE{"GHC.Internal.Data.Foldable.sum", BfSum{}}, BfE{"GHC.Internal.Data.Foldable.product", BfProduct{}}, BfE{"GHC.Internal.Data.Foldable.and", BfAndL{}}, BfE{"GHC.Internal.Data.Foldable.or", BfOrL{}}, BfE{"GHC.Internal.Data.Foldable.concatMap", BfConcatMap{}}, BfE{"GHC.Internal.Show.show", BfShow{}}, BfE{"GHC.Internal.Base.id", BfId{}}, BfE{"GHC.Internal.Base.const", BfConst{}}, BfE{"GHC.Internal.Enum.succ", BfSucc{}}, BfE{"Data.Fix.unFix", BfUnFix{}}, BfE{"Data.Functor.Foldable.project", BfProject{}}, BfE{"Data.Functor.Foldable.embed", BfEmbed{}}, BfE{"Data.Functor.Foldable.cata", BfCata{}}, BfE{"GHC.Internal.Base.>>=", BfBind{}}, BfE{"GHC.Internal.Base.>>", BfThen{}}, BfE{"GHC.Internal.Base.return", BfPure{}}, BfE{"GHC.Internal.Base.pure", BfPure{}}, BfE{"GHC.Internal.Base.fmap", BfFmap{}}, BfE{"GHC.Internal.Data.Functor.<$>", BfFmap{}}, BfE{"GHC.Internal.Data.Maybe.maybe", BfMaybe{}}, BfE{"GHC.Internal.Data.Maybe.fromMaybe", BfFromMaybe{}}, BfE{"GHC.Internal.Data.Either.either", BfEither{}}, BfE{"GHC.Internal.Base.<>", BfSemi{}}, BfE{"GHC.Internal.Base.<*>", BfAp{}}, BfE{"Control.Monad.State.Class.get", BfGet{}}, BfE{"Control.Monad.State.Class.put", BfPut{}}, BfE{"Control.Monad.State.Class.modify", BfModify{}}, BfE{"Control.Monad.State.Class.modify'", BfModify{}}, BfE{"Control.Monad.State.Class.gets", BfGets{}}, BfE{"Control.Monad.Trans.State.Lazy.evalState", BfEval{}}, BfE{"Control.Monad.Trans.State.Strict.evalState", BfEval{}}, BfE{"Control.Monad.Trans.State.Lazy.execState", BfExec{}}, BfE{"Control.Monad.Trans.State.Strict.execState", BfExec{}}, BfE{"Control.Monad.Trans.State.Lazy.runState", BfRun{}}, BfE{"Control.Monad.Trans.State.Strict.runState", BfRun{}}, BfE{"Control.Monad.Error.Class.throwError", BfThrow{}}, BfE{"Control.Monad.Trans.Except.runExceptT", BfRunExc{}}, BfE{"GHC.Internal.Base.when", BfWhen{}}, BfE{"GHC.Internal.Control.Monad.unless", BfUnless{}}, BfE{"GHC.Internal.Data.Functor.void", BfVoid{}}, BfE{"GHC.Internal.Base.=<<", BfBindR{}}, BfE{"GHC.Internal.Base.*>", BfThen{}}, BfE{"GHC.Internal.Data.Foldable.forM_", BfForM_{}}, BfE{"GHC.Internal.Data.Foldable.mapM_", BfMapM_{}}, BfE{"GHC.Internal.Data.Traversable.forM", BfForM{}}, BfE{"GHC.Internal.Data.Traversable.mapM", BfMapM{}}, BfE{"GHC.Internal.Data.Traversable.traverse", BfMapM{}}, BfE{"GHC.Internal.Data.Traversable.sequence", BfSeq{}}, BfE{"GHC.Internal.Data.Traversable.sequenceA", BfSeq{}}, BfE{"GHC.Internal.Control.Monad.foldM", BfFoldM{}}, BfE{"GHC.Internal.Base.absurd", BfAbsurd{}}]

# Num's and Enum's functions beyond the first table
def fd.bftab1() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Num.-", BfNum{"sub"}}, BfE{"GHC.Internal.Num.negate", BfNeg{"negate"}}, BfE{"GHC.Internal.Num.abs", BfNeg{"abs"}}, BfE{"GHC.Internal.Num.signum", BfNeg{"signum"}}, BfE{"GHC.Internal.Enum.pred", BfNeg{"pred"}}, BfE{"GHC.Internal.Real.fromIntegral", BfConv{}}, BfE{"GHC.Internal.Real.toInteger", BfIdAt{}}, BfE{"GHC.Internal.Enum.toEnum", BfIdAt{}}, BfE{"GHC.Internal.Enum.fromEnum", BfIdAt{}}, BfE{"GHC.Internal.Num.subtract", BfSubtract{}}, BfE{"GHC.Internal.Base.liftA2", BfLift2{}}, BfE{"HsPrelude.Z.length", BfZ{"length"}}, BfE{"HsPrelude.Z.take", BfZ{"take"}}, BfE{"HsPrelude.Z.drop", BfZ{"drop"}}, BfE{"HsPrelude.Z.replicate", BfZ{"replicate"}}, BfE{"HsPrelude.Z.ord", BfZ{"ord"}}, BfE{"HsPrelude.Z.chr", BfZ{"chr"}}, BfE{"GHC.Internal.Enum.enumFromTo", BfRange{}}, BfE{"Crypto.Hash.hash", BfOne{"HsPrelude.HsDigest.hash"}}, BfE{"Data.ByteString.pack", BfOne{""}}, BfE{"Data.ByteString.unpack", BfOne{""}}, BfE{"Data.ByteString.Lazy.pack", BfOne{""}}, BfE{"Data.ByteString.Lazy.unpack", BfOne{""}}, BfE{"Data.ByteString.Lazy.Internal.toStrict", BfOne{""}}, BfE{"Data.ByteString.Lazy.Internal.fromStrict", BfOne{""}}, BfE{"Data.ByteArray.Methods.unpack", BfOne{"HsPrelude.HsDigest.bytes"}}, BfE{"GHC.Internal.Real.numerator", BfOne{"HsPrelude.HsRational.numerator"}}, BfE{"GHC.Internal.Real.denominator", BfOne{"HsPrelude.HsRational.denominator"}}, BfE{"Codec.Binary.UTF8.String.encode", BfOne{"HsPrelude.HsUtf8.encode"}}]

# Data.List's, Data.Maybe's, Data.Either's, Data.Tuple's and Data.Bifunctor's
# functions (HsPrelude's HsList, see fd.dm), mempty, flip, trace, liftM2
def fd.bftab2.a() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.Tuple.fst", BfDm{"HsList.fst", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Tuple.snd", BfDm{"HsList.snd", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Tuple.uncurry", BfDm{"HsList.uncurry", "ABC", "ABC", 1n, 2n}}, BfE{"GHC.Internal.Data.Tuple.swap", BfDm{"HsList.swap", "AB", "AB", 0n, 1n}}, BfE{"Data.Tuple.swap", BfDm{"HsList.swap", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.List.zip", BfDm{"HsList.zip", "AB", "AB", 0n, 2n}}, BfE{"GHC.Internal.List.zip3", BfDm{"HsList.zip3", "ABC", "ABC", 0n, 3n}}, BfE{"GHC.Internal.List.zipWith", BfDm{"HsList.zipWith", "ABC", "ABC", 1n, 3n}}, BfE{"GHC.Internal.List.zipWith3", BfDm{"HsList.zipWith3", "ABCD", "ABCD", 1n, 4n}}, BfE{"GHC.Internal.List.unzip", BfDm{"HsList.unzip", "AB", "AB", 0n, 1n}}]

def fd.bftab2.b() -> List<&2, BfE>:
  [BfE{"GHC.Internal.List.lookup", BfDm{"HsList.lookup", "KV", "KVe", 0n, 2n}}, BfE{"GHC.Internal.List.takeWhile", BfDm{"HsList.takeWhile", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.List.dropWhile", BfDm{"HsList.dropWhile", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.List.span", BfDm{"HsList.span", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.List.break", BfDm{"HsList.break", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.partition", BfDm{"HsList.partition", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.nub", BfDm{"HsList.nub", "K", "Ke", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.nubBy", BfDm{"HsList.nubBy", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.isPrefixOf", BfDm{"HsList.isPrefixOf", "K", "Ke", 0n, 2n}}, BfE{"GHC.Internal.Data.OldList.isSuffixOf", BfDm{"HsList.isSuffixOf", "K", "Ke", 0n, 2n}}]

def fd.bftab2.c() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.OldList.isInfixOf", BfDm{"HsList.isInfixOf", "K", "Ke", 0n, 2n}}, BfE{"GHC.Internal.Data.OldList.stripPrefix", BfDm{"HsList.stripPrefix", "K", "Ke", 0n, 2n}}, BfE{"GHC.Internal.List.isPrefixOf", BfDm{"HsList.isPrefixOf", "K", "Ke", 0n, 2n}}, BfE{"GHC.Internal.Data.OldList.intersperse", BfDm{"HsList.intersperse", "A", "A", 0n, 2n}}, BfE{"GHC.Internal.Data.OldList.intercalate", BfDm{"HsList.intercalate", "A", "A", 0n, 2n}}, BfE{"GHC.Internal.Data.OldList.lines", BfDm{"HsList.lines", "", "", 0n, 1n}}, BfE{"Data.OldList.lines", BfDm{"HsList.lines", "", "", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.unlines", BfDm{"HsList.unlines", "", "", 0n, 1n}}, BfE{"Data.OldList.unlines", BfDm{"HsList.unlines", "", "", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.words", BfDm{"HsList.words", "", "", 0n, 1n}}]

def fd.bftab2.d() -> List<&2, BfE>:
  [BfE{"Data.OldList.words", BfDm{"HsList.words", "", "", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.unwords", BfDm{"HsList.unwords", "", "", 0n, 1n}}, BfE{"Data.OldList.unwords", BfDm{"HsList.unwords", "", "", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.sortOn", BfDm{"HsList.sortOn", "KA", "KAc", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.sortBy", BfDm{"HsList.sortBy", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.sort", BfDm{"HsList.sort", "K", "Kc", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.groupBy", BfDm{"HsList.groupBy", "A", "A", 1n, 2n}}, BfE{"GHC.Internal.Data.OldList.group", BfDm{"HsList.group", "K", "Ke", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.tails", BfDm{"HsList.tails", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.OldList.inits", BfDm{"HsList.inits", "A", "A", 0n, 1n}}]

def fd.bftab2.e() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.Maybe.mapMaybe", BfDm{"HsList.mapMaybe", "AB", "AB", 1n, 2n}}, BfE{"GHC.Internal.Data.Maybe.catMaybes", BfDm{"HsList.catMaybes", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Maybe.isJust", BfDm{"HsList.isJust", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Maybe.isNothing", BfDm{"HsList.isNothing", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Maybe.listToMaybe", BfDm{"HsList.listToMaybe", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Maybe.maybeToList", BfDm{"HsList.maybeToList", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Either.lefts", BfDm{"HsList.lefts", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Either.rights", BfDm{"HsList.rights", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Either.partitionEithers", BfDm{"HsList.partitionEithers", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Either.isLeft", BfDm{"HsList.isLeft", "AB", "AB", 0n, 1n}}]

def fd.bftab2.f() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.Either.isRight", BfDm{"HsList.isRight", "AB", "AB", 0n, 1n}}, BfE{"GHC.Internal.Data.Either.fromLeft", BfDm{"HsList.fromLeft", "AB", "AB", 0n, 2n}}, BfE{"GHC.Internal.Data.Either.fromRight", BfDm{"HsList.fromRight", "AB", "AB", 0n, 2n}}, BfE{"GHC.Internal.Data.Foldable.find", BfDmF{"HsList.find", "TK", "K", 1n, 2n}}, BfE{"GHC.Internal.Data.Foldable.notElem", BfDmF{"HsList.notElem", "TK", "Ke", 0n, 2n}}, BfE{"GHC.Internal.Data.Foldable.toList", BfDmF{"HsList.toList", "TK", "K", 0n, 1n}}, BfE{"HsPrelude.Z.zipFrom", BfDm{"HsList.zipFrom", "KA", "KAs", 0n, 2n}}, BfE{"HsPrelude.Z.zipR", BfDm{"HsList.zipR", "AK", "AKs", 0n, 2n}}, BfE{"HsPrelude.Z.zipWithFrom", BfDm{"HsList.zipWithFrom", "KBC", "KBCs", 1n, 3n}}, BfE{"HsPrelude.Z.zipWithR", BfDm{"HsList.zipWithR", "AKC", "AKCs", 1n, 3n}}]

def fd.bftab2.g() -> List<&2, BfE>:
  [BfE{"Data.Bifunctor.first", BfBi{"first"}}, BfE{"Data.Bifunctor.second", BfBi{"second"}}, BfE{"Data.Bifunctor.bimap", BfBi{"bimap"}}, BfE{"GHC.Internal.Base.flip", BfFlip{}}, BfE{"GHC.Internal.Debug.Trace.trace", BfTrace{}}, BfE{"GHC.Internal.Base.mempty", BfMempty{}}, BfE{"GHC.Internal.Base.mconcat", BfMconcat{}}, BfE{"GHC.Internal.Base.mappend", BfSemi{}}, BfE{"GHC.Internal.Base.liftM2", BfLift2{}}, BfE{"Control.Monad.Reader.Class.ask", BfAsk{}}, BfE{"Control.Monad.Reader.Class.local", BfLocal{}}, BfE{"Control.Monad.Trans.Reader.local", BfLocalT{}}, BfE{"Control.Monad.Reader.Class.asks", BfAsks{}}, BfE{"Control.Monad.Reader.Class.reader", BfAsks{}}, BfE{"Control.Monad.Trans.Class.lift", BfLift{}}, BfE{"Control.Monad.Trans.Reader.runReaderT", BfId{}}, BfE{"Control.Monad.Trans.Reader.runReader", BfId{}}, BfE{"Control.Monad.Trans.Writer.Strict.runWriterT", BfId{}}, BfE{"Control.Monad.Trans.Writer.Lazy.runWriterT", BfId{}}, BfE{"Control.Monad.Trans.Writer.Strict.runWriter", BfId{}}, BfE{"Control.Monad.Trans.Writer.Lazy.runWriter", BfId{}}, BfE{"Control.Monad.Trans.Writer.Strict.writer", BfWriter{}}, BfE{"Control.Monad.Trans.Writer.Lazy.writer", BfWriter{}}]

def fd.bftab2.seq() -> List<&2, BfE>:
  [BfE{"Data.Sequence.Internal.empty", BfDm{"HsList.nil", "A", "A", 0n, 0n}}, BfE{"Data.Sequence.Internal.|>", BfDm{"HsList.snoc", "A", "A", 0n, 2n}}, BfE{"Data.Sequence.Internal.<|", BfDm{"HsList.cons", "A", "A", 0n, 2n}}, BfE{"Data.Sequence.Internal.viewl", BfDm{"HsList.toList", "A", "A", 0n, 1n}}, BfE{"Data.Sequence.Internal.fromList", BfDm{"HsList.toList", "A", "A", 0n, 1n}}]

# GHC.Show's functions (HsPrelude's HsShow), showsPrec and shows at base's
# types, the specialiser's showVia and showListVia
def fd.bftab2.show() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Show.showString", BfDm{"HsShow.string", "", "", 0n, 2n}}, BfE{"GHC.Internal.Show.showChar", BfDm{"HsShow.char", "", "", 0n, 2n}}, BfE{"GHC.Internal.Show.showParen", BfDm{"HsShow.paren", "", "", 0n, 3n}}, BfE{"GHC.Internal.Show.showSpace", BfDm{"HsShow.space", "", "", 0n, 1n}}, BfE{"GHC.Internal.Show.showCommaSpace", BfDm{"HsShow.commaSpace", "", "", 0n, 1n}}, BfE{"GHC.Internal.Show.showList__", BfDm{"HsShow.list", "A", "A", 1n, 3n}}, BfE{"HsPrelude.Z.showVia", BfDm{"HsShow.via", "A", "A", 1n, 2n}}, BfE{"HsPrelude.Z.showListVia", BfDm{"HsShow.listVia", "A", "A", 1n, 3n}}, BfE{"GHC.Internal.Show.showsPrec", BfShowsPrec{}}, BfE{"GHC.Internal.Show.shows", BfShows{}}]

# base's partial functions (prelude/HsPartial.bend), each an Either the
# partial pass (fd.pt) binds: error's and undefined's first type argument
# their representation
def fd.bftab2.pt() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Err.error", BfDm{"HsList.error", "rA", "A", 0n, 1n}}, BfE{"GHC.Internal.Err.errorWithoutStackTrace", BfDm{"HsList.error", "rA", "A", 0n, 1n}}, BfE{"GHC.Internal.Err.undefined", BfDm{"HsList.undefined", "rA", "A", 0n, 0n}}, BfE{"GHC.Internal.List.head", BfDm{"HsList.head", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.List.tail", BfDm{"HsList.tail", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.List.last", BfDm{"HsList.last", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.List.init", BfDm{"HsList.init", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.List.!!", BfDm{"HsList.index", "A", "A", 0n, 2n}}, BfE{"GHC.Internal.Data.Maybe.fromJust", BfDm{"HsList.fromJust", "A", "A", 0n, 1n}}, BfE{"GHC.Internal.Data.Foldable.maximum", BfDmF{"HsList.maximum", "TK", "Kc", 0n, 1n}}, BfE{"GHC.Internal.Data.Foldable.minimum", BfDmF{"HsList.minimum", "TK", "Kc", 0n, 1n}}, BfE{"GHC.Internal.Data.Foldable.maximumBy", BfDmF{"HsList.maximumBy", "TK", "K", 1n, 2n}}, BfE{"GHC.Internal.Data.Foldable.minimumBy", BfDmF{"HsList.minimumBy", "TK", "K", 1n, 2n}}, BfE{"GHC.Internal.Data.Foldable.foldr1", BfDmF{"HsList.foldr1", "TK", "K", 1n, 2n}}, BfE{"GHC.Internal.Data.Foldable.foldl1", BfDmF{"HsList.foldl1", "TK", "K", 1n, 2n}}]

# base functions of an Ord (prelude/HsOrd.bend)
def fd.bftab2.ord() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.Ord.comparing", BfDm{"HsList.comparing", "KA", "KAc", 1n, 3n}}, BfE{"GHC.Internal.Real.even", BfParity{"even"}}, BfE{"GHC.Internal.Real.odd", BfParity{"odd"}}]

# Control.Monad's list functions at a monad (see fd.mapm.at, fd.mlist.at)
def fd.bftab2.mlist() -> List<&2, BfE>:
  [BfE{"GHC.Internal.Data.Foldable.traverse_", BfMapM_{}}, BfE{"GHC.Internal.Data.Foldable.for_", BfForM_{}}, BfE{"GHC.Internal.Control.Monad.filterM", BfFilterM{}}, BfE{"GHC.Internal.Control.Monad.zipWithM_", BfZipWithM_{}}]

def fd.bftab2() -> List<&2, BfE>:
  List.concat(&2, BfE, [fd.bftab2.pt(), fd.bftab2.ord(), fd.bftab2.mlist(), fd.bftab2.show(), fd.bftab2.seq(), fd.bftab2.a(), fd.bftab2.b(), fd.bftab2.c(), fd.bftab2.d(), fd.bftab2.e(), fd.bftab2.f(), fd.bftab2.g()])

# megaparsec's and parser-combinators' functions that run a parser once,
# HsPrelude's HsPc (prelude/HsPc.bend): its def, the leading type arguments
# dropped (e, s and m, or m), the arguments taken (the model's,
# prelude/Cata/Parsec.hs, run one again)
def fd.bftab.pc() -> List<&2, BfE>:
  +c = {"Text.Megaparsec.Class." : String}
  +l = {"Text.Megaparsec.Char.Lexer." : String}
  [BfE{"GHC.Internal.Base.<|>", BfAlt{}}, BfE{"GHC.Internal.Base.empty", BfEmpty{}}, BfE{"GHC.Internal.Base.<*", BfLeft{}}, BfE{"GHC.Internal.Base.<$", BfConstL{}}, BfE{"GHC.Internal.Control.Monad.Fail.fail", BfFail{}}, BfE{c ++ "try", BfPc{"HsPc.try", 3n, 1n}}, BfE{c ++ "eof", BfPc{"HsPc.eof", 3n, 0n}}, BfE{c ++ "notFollowedBy", BfPc{"HsPc.notFollowedBy", 3n, 1n}}, BfE{c ++ "lookAhead", BfPc{"HsPc.lookAhead", 3n, 1n}}, BfE{c ++ "hidden", BfPc{"HsPc.hidden", 3n, 1n}}, BfE{c ++ "label", BfPc{"HsPc.label", 3n, 2n}}, BfE{"Text.Megaparsec.<?>", BfPc{"HsPc.labelf", 3n, 2n}}, BfE{"Text.Megaparsec.satisfy", BfPc{"HsPc.satisfy", 3n, 1n}}, BfE{"Text.Megaparsec.anySingle", BfPc{"HsPc.anySingle", 3n, 0n}}, BfE{"Text.Megaparsec.single", BfPc{"HsPc.char", 3n, 1n}}, BfE{"Text.Megaparsec.getOffset", BfPc{"HsPc.getOffset", 3n, 0n}}, BfE{"Text.Megaparsec.getSourcePos", BfPc{"HsPc.getSourcePos", 3n, 0n}}, BfE{"Text.Megaparsec.runParser", BfPc{"HsPc.runParser", 2n, 3n}}, BfE{"Text.Megaparsec.Error.errorBundlePretty", BfPc{"HsPc.errorBundlePretty", 2n, 1n}}, BfE{"Text.Megaparsec.Pos.unPos", BfPc{"HsPc.unPos", 0n, 1n}}, BfE{"Text.Megaparsec.Pos.sourceLine", BfPc{"HsPc.pos.line", 0n, 1n}}, BfE{"Text.Megaparsec.Pos.sourceColumn", BfPc{"HsPc.pos.col", 0n, 1n}}, BfE{"Text.Megaparsec.Pos.sourceName", BfPc{"HsPc.pos.name", 0n, 1n}}, BfE{"Text.Megaparsec.Char.char", BfPc{"HsPc.char", 3n, 1n}}, BfE{"Text.Megaparsec.Common.string", BfPc{"HsPc.string", 3n, 1n}}, BfE{"Text.Megaparsec.Char.space1", BfPc{"HsPc.space1", 3n, 0n}}, BfE{"Text.Megaparsec.Char.space", BfPc{"HsPc.space", 3n, 0n}}, BfE{l ++ "skipLineComment", BfPc{"HsPc.skipLineComment", 3n, 1n}}, BfE{l ++ "indentLevel", BfPc{"HsPc.indentLevel", 3n, 0n}}, BfE{l ++ "incorrectIndent", BfPc{"HsPc.incorrectIndent", 3n, 3n}}, BfE{l ++ "decimal", BfPc{"HsPc.decimal", 4n, 0n}}, BfE{l ++ "charLiteral", BfPc{"HsPc.charLiteral", 3n, 0n}}, BfE{"Text.Megaparsec.Lexer.lexeme", BfPc{"HsPc.lexeme", 3n, 2n}}, BfE{"Text.Megaparsec.Lexer.symbol", BfPc{"HsPc.symbol", 3n, 2n}}, BfE{"Control.Applicative.Combinators.between", BfPc{"HsPc.between", 1n, 3n}}, BfE{"Control.Applicative.optional", BfPc{"HsPc.optional", 1n, 1n}}, BfE{"Control.Applicative.Combinators.option", BfPc{"HsPc.option", 1n, 2n}}, BfE{"Control.Monad.Combinators.option", BfPc{"HsPc.option", 1n, 2n}}, BfE{"GHC.Internal.Unicode.isAlpha", BfPc{"HsChar.isAlpha", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isLetter", BfPc{"HsChar.isAlpha", 0n, 1n}}, BfE{"Data.Char.isLetter", BfPc{"HsChar.isAlpha", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isAlphaNum", BfPc{"HsChar.isAlphaNum", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isUpper", BfPc{"HsChar.isUpper", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isLower", BfPc{"HsChar.isLower", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isSpace", BfPc{"HsChar.isSpace", 0n, 1n}}, BfE{"GHC.Internal.Unicode.isDigit", BfPc{"HsChar.isDigit", 0n, 1n}}, BfE{"GHC.Internal.Enum.maxBound", BfBound{True{}}}, BfE{"GHC.Internal.Enum.minBound", BfBound{False{}}}, BfE{"GHC.Internal.Num.fromInteger", BfIdAt{}}]

def fd.bftab() -> List<&2, BfE>:
  List.concat(&2, BfE, [fd.bftab0(), fd.bftab1(), fd.bftab2(), fd.bftab.pc(), fd.dm.tab.map(fd.dm.specs.maps()), fd.dm.tab.set(fd.dm.specs.sets()), [BfE{"Data.Set.Internal.map", BfDm{"HsSet.map", "LK", "KLd", 1n, 2n}}]])

def fd.bf.find(xs: List<&2, BfE>, +k: List<&2, U32>) -> Bf:
  match xs:
    case Nil{}:
      BfNone{}
    case BfE{s, v} <> t:
      Bool.pick(Bf, S.eq(S.b(s), k), v, fd.bf.find(t, k))

def fd.z.n(+op: List<&2, U32>) -> Nat:
  Bool.pick(Nat, Bool.or(fd.is(op, "length"), Bool.or(fd.is(op, "ord"), fd.is(op, "chr"))), 1n, 2n)

# the number of arguments each takes
def fd.bf.n(f: Bf) -> Nat:
  match f:
    case BfTrue{}:
      0n
    case BfNot{}:
      1n
    case BfLength{}:
      1n
    case BfNull{}:
      1n
    case BfReverse{}:
      1n
    case BfConcat{}:
      1n
    case BfSum{}:
      1n
    case BfProduct{}:
      1n
    case BfAndL{}:
      1n
    case BfOrL{}:
      1n
    case BfShow{}:
      1n
    case BfId{}:
      1n
    case BfSucc{}:
      1n
    case BfUnFix{}:
      1n
    case BfProject{}:
      1n
    case BfEmbed{}:
      1n
    case BfPure{}:
      1n
    case BfGet{}:
      0n
    case BfPut{}:
      1n
    case BfModify{}:
      1n
    case BfGets{}:
      1n
    case BfThrow{}:
      1n
    case BfRunExc{}:
      1n
    case BfVoid{}:
      1n
    case BfFoldM{}:
      3n
    case BfFilterM{}:
      2n
    case BfZipWithM_{}:
      3n
    case BfDm{d, r, p, nt, n}:
      n
    case BfAbsurd{}:
      1n
    case BfNeg{op}:
      1n
    case BfConv{}:
      1n
    case BfIdAt{}:
      1n
    case BfLift2{}:
      3n
    case BfOne{f}:
      1n
    case BfParity{op}:
      1n
    case BfDmF{d, r, p, nt, n}:
      n
    case BfBi{op}:
      Bool.pick(Nat, fd.is(S.b(op), "bimap"), 3n, 2n)
    case BfFlip{}:
      3n
    case BfTrace{}:
      2n
    case BfMempty{}:
      0n
    case BfMconcat{}:
      1n
    case BfShowsPrec{}:
      3n
    case BfShows{}:
      2n
    case BfZ{op}:
      fd.z.n(S.b(op))
    case BfMaybe{}:
      3n
    case BfEither{}:
      3n
    case BfFoldr{}:
      3n
    case BfFoldl{}:
      3n
    case BfEmpty{}:
      0n
    case BfFail{}:
      1n
    case BfPc{f, d, n}:
      n
    case BfBound{hi}:
      0n
    case BfAsk{}:
      0n
    case BfAsks{}:
      1n
    case BfLift{}:
      1n
    case BfWriter{}:
      1n
    case BfSeq{}:
      1n
    case _:
      2n

# what a type argument is, for the functions that differ by type
type Tq is Data:
  TqNat{}
  TqInt{}
  TqDigest{}
  TqRat{}
  TqU32{}
  TqChar{}
  TqBool{}
  TqF32{}
  TqOther{}

def fd.tq.of(+n: List<&2, U32>) -> Tq:
  Bool.pick(Tq, fd.is(n, "U32"), TqU32{}, Bool.pick(Tq, fd.is(n, "HsPrelude.HsDigest"), TqDigest{}, Bool.pick(Tq, fd.is(n, "HsPrelude.HsInt"), TqInt{}, Bool.pick(Tq, fd.is(n, "HsPrelude.HsRational"), TqRat{}, Bool.pick(Tq, fd.is(n, "Nat"), TqNat{}, Bool.pick(Tq, fd.is(n, "Char"), TqChar{}, Bool.pick(Tq, fd.is(n, "Bool"), TqBool{}, Bool.pick(Tq, fd.is(n, "F32"), TqF32{}, TqOther{}))))))))

def fd.tq(t: T.Bt) -> Tq:
  match t:
    case T.BtTyApp{n, T.BtANil{}}:
      fd.tq.of(n)
    case _:
      TqOther{}

# Foldable's functions at a list (the container argument is the marker List)
def fd.foldable(c: T.Bt, t: T.Bt) -> T.Bt:
  match c:
    case T.BtVar{+n}:
      Bool.pick(T.Bt, Bool.or(fd.is(n, "List"), fd.is(n, "HsPrelude.HsSet")), t, fd.todo("fold:foldable-not-list"))
    case T.BtTyApp{+n, T.BtArgs{k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), t, fd.todo("fold:foldable-not-list"))
    case _:
      fd.todo("fold:foldable-not-list")

# a Foldable's argument as a list: the list, a Set's elements, a Map's
# values (in the order of the keys, as Data.Foldable has them)
def fd.fl(c: T.Bt, +t: T.Bt, +x: T.Bt) -> T.Bt:
  match c:
    case T.BtVar{+n}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsSet"), fd.callS("HsPrelude.HsSet.toList", [fd.tpl0(t), x]), x)
    case T.BtTyApp{+n, T.BtArgs{k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), fd.callS("HsPrelude.HsMap.elems", [fd.tpl0(k), fd.tpl0(t), x]), x)
    case _:
      x

def fd.cmp.char(+op: List<&2, U32>, +a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(op, "is_eq"), fd.callS("Char.is_eq", [a, b]), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.not", [fd.callS("Char.is_eq", [a, b])]), Bool.pick(T.Bt, Bool.or(fd.is(op, "max"), fd.is(op, "min")), fd.todo("fold:char-max"), T.tba.call(T.BtVar{fd.cat(S.b("U32."), op)}, [fd.callS("Char.to_u32", [a]), fd.callS("Char.to_u32", [b])]))))

def fd.cmp.bool(+op: List<&2, U32>, +a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(op, "is_eq"), fd.callS("Bool.not", [fd.callS("Bool.xor", [a, b])]), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.xor", [a, b]), fd.todo("fold:bool-order")))

# Equality ---------------------------------------------------------------------
#
# Haskell's == at a type Base has no == for: at a list, Maybe, Either, a
# pair, Unit and Ordering the prelude's hs.eq.* (templates given == at the
# parts), at a type of the module T.eq, the def a derived Eq instance gives
# (the same constructor and == at each field, as GHC derives it).  A type
# of the module whose Eq instance is written by hand has no T.eq yet, and
# what uses == at it is out (fold:eq-instance).  A type variable's == is
# the def's dictionary eq_A when it takes one, else out (fold:eq-at-tyvar).

# a type's arguments as == sees them: quantities out, a Sigma's second
# component its body
def fd.eq.targs(ts: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match ts:
    case Nil{}:
      Nil{}
    case T.BtVar{+x} <> t:
      +rest = fd.eq.targs(t)
      Bool.pick(List<&2, T.Bt>, S.prefix(x, S.b("&")), rest, T.BtVar{x} <> rest)
    case T.BtLam{m, x, b} <> t:
      b <> fd.eq.targs(t)
    case h <> t:
      h <> fd.eq.targs(t)

# the dictionary of the type variable v: == at v
def fd.eq.dict(+v: List<&2, U32>) -> List<&2, U32>:
  fd.cat(S.b("eq_"), v)

# the def == is at a type of this name, given == at its arguments
def fd.eq.name(+n: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, fd.is(n, "List"), S.b("hs.eq.list"), Bool.pick(List<&2, U32>, fd.is(n, "Maybe"), S.b("hs.eq.maybe"), Bool.pick(List<&2, U32>, fd.is(n, "Either"), S.b("hs.eq.either"), Bool.pick(List<&2, U32>, fd.is(n, "Sigma"), S.b("hs.eq.pair"), Bool.pick(List<&2, U32>, fd.is(n, "Unit"), S.b("hs.eq.unit"), Bool.pick(List<&2, U32>, fd.is(n, "Cmp"), S.b("hs.eq.cmp"), fd.cat(n, S.b(".eq"))))))))

# whether Base has n.is_eq
def fd.eq.prim(+n: List<&2, U32>) -> Bool:
  Bool.or(Bool.or(fd.is(n, "HsPrelude.HsDigest"), fd.is(n, "U32")), Bool.or(fd.is(n, "HsPrelude.HsInt"), Bool.or(fd.is(n, "Nat"), Bool.or(fd.is(n, "Char"), fd.is(n, "F32")))))

# whether == at a type of this name is out: HsPrelude's types and the
# types Bend has no == at
def fd.eq.bad(+n: List<&2, U32>) -> Bool:
  Bool.or(Bool.and(S.prefix(n, S.b("HsPrelude.")), Bool.not(Bool.or(fd.is(n, "HsPrelude.HsMap"), fd.is(n, "HsPrelude.HsSet")))), Bool.or(fd.is(n, "String"), Bool.or(fd.is(n, "IO"), Bool.or(fd.is(n, "Type"), fd.is(n, "Data")))))

# what fd.eqk makes of a type: a == b at it, == at it as a function, or
# (at an argument spine) == at each argument as == sees them
type Eqk is Data:
  EkCall{a: T.Bt, b: T.Bt}
  EkFn{}
  EkFns{}

# == at a type variable: the def's dictionary, or out
def fd.eq.var(+v: List<&2, U32>, +vs: List<&2, List<&2, U32>>) -> T.Bt:
  Bool.pick(T.Bt, S.mem(v, vs), T.BtVar{fd.eq.dict(v)}, fd.todo("fold:eq-at-tyvar"))

# a == b at a type named n, its arguments ts, == at them fs
def fd.eqcall.app(+n: List<&2, U32>, +ts: List<&2, T.Bt>, +fs: List<&2, T.Bt>, +a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(n, "Empty"), fd.con0("True"), Bool.pick(T.Bt, fd.eq.prim(n), T.tba.call(T.BtVar{fd.cat(n, S.b(".is_eq"))}, [a, b]), Bool.pick(T.Bt, fd.is(n, "Bool"), fd.callS("Bool.not", [fd.callS("Bool.xor", [a, b])]), Bool.pick(T.Bt, fd.eq.bad(n), fd.todo("fold:eq-at-type"), T.tba.call(T.BtVar{fd.eq.name(n)}, List.append(&2, T.Bt, fd.tpls(ts), List.append(&2, T.Bt, fd.tpls(fs), [a, b])))))))

# == at a type named n without arguments, as a function: a def's name (so
# a recursive T.eq passes its own template arguments on), at Bool a lambda
def fd.eq.fn0(+n: List<&2, U32>) -> T.Bt:
  Bool.pick(T.Bt, fd.is(n, "Empty"), T.BtLam{T.BmLive{}, S.b("p_"), T.BtLam{T.BmLive{}, S.b("q_"), fd.con0("True")}}, Bool.pick(T.Bt, fd.eq.prim(n), T.BtVar{fd.cat(n, S.b(".is_eq"))}, Bool.pick(T.Bt, fd.is(n, "Bool"), T.BtLam{T.BmLive{}, S.b("p_"), T.BtLam{T.BmLive{}, S.b("q_"), fd.callS("Bool.not", [fd.callS("Bool.xor", [fd.v("p_"), fd.v("q_")])])}}, Bool.pick(T.Bt, fd.eq.bad(n), fd.todo("fold:eq-at-type"), T.BtVar{fd.eq.name(n)}))))

# an argument that is a variable: a quantity (&2) is no type and goes
def fd.eq.fns.var(+x: List<&2, U32>, +vs: List<&2, List<&2, U32>>, +rest: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, S.prefix(x, S.b("&")), rest, T.BtArgs{fd.eq.var(x, vs), rest})

# one recursion over the type (Bend takes no mutual recursion here)
def fd.eqk(t: T.Bt, k: Eqk, +vs: List<&2, List<&2, U32>>) -> T.Bt:
  match t k:
    case T.BtTyApp{+n, +args} EkCall{+a, +b}:
      fd.eqcall.app(n, fd.eq.targs(fd.spine(args)), fd.spine(fd.eqk(args, EkFns{}, vs)), a, b)
    case T.BtVar{+v} EkCall{+a, +b}:
      Bool.pick(T.Bt, S.mem(v, vs), T.tba.call(T.BtVar{fd.eq.dict(v)}, [a, b]), fd.todo("fold:eq-at-tyvar"))
    case T.BtVar{+v} EkFn{}:
      fd.eq.var(v, vs)
    case T.BtTyApp{+n, T.BtANil{}} EkFn{}:
      fd.eq.fn0(n)
    case T.BtTyApp{+n, +args} EkFn{}:
      T.BtLam{T.BmLive{}, S.b("p_"), T.BtLam{T.BmLive{}, S.b("q_"), fd.eqcall.app(n, fd.eq.targs(fd.spine(args)), fd.spine(fd.eqk(args, EkFns{}, vs)), fd.v("p_"), fd.v("q_"))}}
    case T.BtANil{} EkFns{}:
      T.BtANil{}
    case T.BtArgs{T.BtLam{m, x, b}, rest} EkFns{}:
      T.BtArgs{fd.eqk(b, EkFn{}, vs), fd.eqk(rest, EkFns{}, vs)}
    case T.BtArgs{T.BtVar{+x}, rest} EkFns{}:
      fd.eq.fns.var(x, vs, fd.eqk(rest, EkFns{}, vs))
    case T.BtArgs{h, rest} EkFns{}:
      T.BtArgs{fd.eqk(h, EkFn{}, vs), fd.eqk(rest, EkFns{}, vs)}
    case _ _:
      fd.todo("fold:eq-at-type")

# a == b at the type t; vs: the type variables whose == the def takes
def fd.eqcall(t: T.Bt, +vs: List<&2, List<&2, U32>>, a: T.Bt, b: T.Bt) -> T.Bt:
  fd.eqk(t, EkCall{a, b}, vs)

# == at t as a function, for a template argument
def fd.eqfn(t: T.Bt, +vs: List<&2, List<&2, U32>>) -> T.Bt:
  fd.eqk(t, EkFn{}, vs)

# compare at a type, as a function (a template argument: Data.Map's and
# Data.Set's key): at Int, Char, Bool and () Base's or HsPrelude's, at a
# list, a pair and Maybe HsPrelude's HsCmp given compare at the parts (a
# closed lambda); at any other type out (fold:ord-at-type)
type Ck is Data:
  CkFn{}
  CkFns{}

def fd.cmp.fn0(+n: List<&2, U32>) -> T.Bt:
  Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsDigest"), fd.v("HsPrelude.HsDigest.cmp"), Bool.pick(T.Bt, fd.is(n, "U32"), fd.v("U32.cmp"), Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsInt"), fd.v("HsPrelude.HsInt.cmp"), Bool.pick(T.Bt, fd.is(n, "Nat"), fd.v("Nat.cmp"), Bool.pick(T.Bt, fd.is(n, "Char"), fd.v("HsPrelude.HsCmp.char"), Bool.pick(T.Bt, fd.is(n, "Bool"), fd.v("HsPrelude.HsCmp.bool"), Bool.pick(T.Bt, fd.is(n, "Unit"), fd.v("HsPrelude.HsCmp.unit"), fd.todo("fold:ord-at-type"))))))))

def fd.cmp.name(+n: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, fd.is(n, "List"), S.b("HsPrelude.HsCmp.list"), Bool.pick(List<&2, U32>, fd.is(n, "Sigma"), S.b("HsPrelude.HsCmp.pair"), S.b("HsPrelude.HsCmp.maybe")))

def fd.cmp.app(+n: List<&2, U32>, +ts: List<&2, T.Bt>, +fs: List<&2, T.Bt>) -> T.Bt:
  Bool.pick(T.Bt, Bool.or(fd.is(n, "List"), Bool.or(fd.is(n, "Sigma"), fd.is(n, "Maybe"))), T.BtLam{T.BmLive{}, S.b("p_"), T.BtLam{T.BmLive{}, S.b("q_"), T.tba.call(T.BtVar{fd.cmp.name(n)}, List.append(&2, T.Bt, fd.tpls(ts), List.append(&2, T.Bt, fd.tpls(fs), [fd.v("p_"), fd.v("q_")])))}}, fd.todo("fold:ord-at-type"))

# an argument that is a variable: a quantity (&2) is no type and goes
def fd.cmp.fns.var(+x: List<&2, U32>, +rest: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, S.prefix(x, S.b("&")), rest, T.BtArgs{fd.todo("fold:ord-at-tyvar"), rest})

def fd.cmpk(t: T.Bt, k: Ck) -> T.Bt:
  match t k:
    case T.BtTyApp{+n, T.BtANil{}} CkFn{}:
      fd.cmp.fn0(n)
    case T.BtTyApp{+n, +args} CkFn{}:
      fd.cmp.app(n, fd.eq.targs(fd.spine(args)), fd.spine(fd.cmpk(args, CkFns{})))
    case T.BtANil{} CkFns{}:
      T.BtANil{}
    case T.BtArgs{T.BtLam{m, x, b}, rest} CkFns{}:
      T.BtArgs{fd.cmpk(b, CkFn{}), fd.cmpk(rest, CkFns{})}
    case T.BtArgs{T.BtVar{+x}, rest} CkFns{}:
      fd.cmp.fns.var(x, fd.cmpk(rest, CkFns{}))
    case T.BtArgs{h, rest} CkFns{}:
      T.BtArgs{fd.cmpk(h, CkFn{}), fd.cmpk(rest, CkFns{})}
    case _ _:
      fd.todo("fold:ord-at-type")

def fd.cmpfn(t: T.Bt) -> T.Bt:
  fd.cmpk(t, CkFn{})

# the type of a dictionary: A -> A -> Bool
def fd.eq.dty(+a: T.Bt) -> T.Bt:
  T.BtPi{T.BmLive{}, S.b("_"), False{}, a, T.BtPi{T.BmLive{}, S.b("_"), False{}, a, fd.ty0("Bool")}}

def fd.eq.dps(vs: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match vs:
    case +v <> t:
      T.BParam{T.BmTpl{}, fd.eq.dict(v), fd.eq.dty(T.BtVar{v})} <> fd.eq.dps(t)
    case Nil{}:
      Nil{}

# T.eq's template parameters: ~A: Data for each type parameter, then
# ~eq_A: A -> A -> Bool for each
def fd.eq.tps(+vs: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  List.append(&2, T.BParam, fd.tvtpls(vs), fd.eq.dps(vs))

def fd.eq.pnames(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case T.BParam{m, x, ty} <> t:
      x <> fd.eq.pnames(t)
    case Nil{}:
      Nil{}

def fd.eq.vars(vs: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match vs:
    case v <> t:
      T.BtVar{v} <> fd.eq.vars(t)
    case Nil{}:
      Nil{}

# the field variables p0, p1, ... of a constructor's pattern
def fd.eq.pv(+p: List<&2, U32>, i: Nat) -> List<&2, U32>:
  fd.cat(p, fd.nshow(i))

def fd.eq.pvs(fs: List<&2, T.BField>, +p: List<&2, U32>, +i: Nat) -> List<&2, T.Bt>:
  match fs:
    case f <> t:
      T.BtPv{T.BmLive{}, fd.eq.pv(p, i)} <> fd.eq.pvs(t, p, 1n+i)
    case Nil{}:
      Nil{}

# == at each field, and-ed
def fd.eq.fields(fs: List<&2, T.BField>, +vs: List<&2, List<&2, U32>>, +i: Nat) -> T.Bt:
  match fs:
    case Nil{}:
      fd.con0("True")
    case T.BField{x, ty} <> +t:
      +e = fd.eqcall(ty, vs, T.BtVar{fd.eq.pv(S.b("a"), i)}, T.BtVar{fd.eq.pv(S.b("b"), i)})
      Bool.pick(T.Bt, List.is_empty(&2, T.BField, t), e, fd.callS("Bool.and", [e, fd.eq.fields(t, vs, 1n+i)]))

def fd.eq.cases(cs: List<&2, T.BCtor>, +vs: List<&2, List<&2, U32>>, +many: Bool) -> T.Bt:
  match cs:
    case T.BCtor{+c, +fs} <> t:
      T.BtCase{T.tba.args([T.BtCon{c, T.tba.args(fd.eq.pvs(fs, S.b("a"), 0n))}, T.BtCon{c, T.tba.args(fd.eq.pvs(fs, S.b("b"), 0n))}]), T.BtExpr{fd.eq.fields(fs, vs, 0n)}, fd.eq.cases(t, vs, many)}
    case Nil{}:
      Bool.pick(T.Bt, many, T.BtCase{T.tba.args([T.BtWild{}, T.BtWild{}]), T.BtExpr{fd.con0("False")}, T.BtCEnd{}}, T.BtCEnd{})

def fd.eq.iname(+it: T.BItem) -> List<&2, U32>:
  match it:
    case T.BiType{n, ps, k, cs, d}:
      fd.cat(n, S.b(".eq"))
    case _:
      S.b("?.eq")

# T.eq, from the type's item: a match on both arguments
def fd.eq.def(it: T.BItem) -> T.BItem:
  match it:
    case T.BiType{+n, ps, k, +cs, d}:
      +vs = fd.eq.pnames(ps)
      +ty = {T.BtTyApp{n, T.tba.args(fd.eq.vars(vs))} : T.Bt}
      T.BiDef{fd.cat(n, S.b(".eq")), List.append(&2, T.BParam, fd.eq.tps(vs), [T.BParam{T.BmLive{}, S.b("a"), ty}, T.BParam{T.BmLive{}, S.b("b"), ty}]), fd.ty0("Bool"), T.BtMatch{T.tba.args([fd.v("a"), fd.v("b")]), fd.eq.cases(cs, vs, Nat.is_gt(List.length(&2, T.BCtor, cs), 1n))}, [fd.cat3(S.b("generated: Eq's == at "), n, S.b(", as GHC derives it"))]}
    case T.BiDef{n, ps, r, b, d}:
      T.BiDef{n, ps, r, b, d}
    case T.BiComment{d}:
      T.BiComment{d}

# a type under its foralls and contexts
def fd.eq.strip(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+h}, X.SxCons{+a, X.SxCons{+b, X.SxNil{}}}}:
      Bool.pick(X.Sx, Bool.or(fd.is(h, "tforall"), fd.is(h, "tctx")), fd.eq.strip(b), X.SxCons{X.SxAtom{h}, X.SxCons{a, X.SxCons{b, X.SxNil{}}}})
    case u:
      u

# the first type of a binder's type, under foralls and contexts
def fd.eq.arg1(t: X.Sx) -> X.Sx:
  V.sv.at(fd.eq.strip(t), 1n)

# (top (abs TVS EVS ((export (l "$c==" N) TYPE)) EVB BINDS SPAN)) whose
# binds GHC generated: the type ==  is at
def fd.eq.drv.of(+x: X.Sx) -> List<&2, List<&2, U32>>:
  +b = V.sv.at(x, 1n)
  +e = V.sv.at(V.sv.at(b, 3n), 0n)
  +ok = Bool.and(V.sv.is(V.sv.hd(x), "top"), Bool.and(V.sv.is(V.sv.hd(b), "abs"), Bool.and(V.sv.is(V.sv.str(V.sv.at(e, 1n), 1n), "$c=="), V.sv.has(b, S.b("generated")))))
  fd.bpicks(ok, [V.sv.str(fd.eq.arg1(V.sv.at(e, 2n)), 2n)], Nil{})

def fd.eq.drv(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      List.append(&2, List<&2, U32>, fd.eq.drv.of(h), fd.eq.drv(t))
    case Nil{}:
      Nil{}

# (instance "GHC.Classes" "Eq" ((tc MOD T ...)) DFUN SPAN): T
def fd.eq.ins.of(+x: X.Sx) -> List<&2, List<&2, U32>>:
  +ok = Bool.and(V.sv.is(V.sv.hd(x), "instance"), Bool.and(V.sv.is(V.sv.str(x, 1n), "GHC.Classes"), V.sv.is(V.sv.str(x, 2n), "Eq")))
  fd.bpicks(ok, [V.sv.str(V.sv.at(V.sv.at(x, 3n), 0n), 2n)], Nil{})

def fd.eq.ins(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      List.append(&2, List<&2, U32>, fd.eq.ins.of(h), fd.eq.ins(t))
    case Nil{}:
      Nil{}

# compare a b at a list, a pair or Maybe: HsPrelude's HsCmp given compare
# at the parts, as fd.cmp.app's function (Data.Map's keys) applied
def fd.cmp.call(t: T.Bt, a: T.Bt, b: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, +args}:
      Bool.pick(T.Bt, Bool.or(fd.is(n, "List"), Bool.or(fd.is(n, "Sigma"), fd.is(n, "Maybe"))), T.tba.call(T.BtVar{fd.cmp.name(n)}, List.append(&2, T.Bt, fd.tpls(fd.eq.targs(fd.spine(args))), List.append(&2, T.Bt, fd.tpls(fd.spine(fd.cmpk(args, CkFns{}))), [a, b]))), fd.todo("fold:ord-at-type"))
    case _:
      fd.todo("fold:ord-at-type")

# == and /= at a type of the module, a list, Maybe, ... (see Equality);
# compare and <, <=, >, >= at a list, a pair or Maybe through their
# compare (fd.cmp.call; max and min out); an order elsewhere is out
def fd.cmp.other(+op: List<&2, U32>, +t: T.Bt, +a: T.Bt, +b: T.Bt) -> T.Bt:
  +c = fd.cmp.call(t, a, b)
  +ord = Bool.pick(T.Bt, fd.is(op, "cmp"), c, Bool.pick(T.Bt, Bool.or(fd.is(op, "max"), fd.is(op, "min")), fd.todo("fold:ord-at-type"), T.tba.call(T.BtVar{fd.cat(S.b("Cmp."), op)}, [c])))
  Bool.pick(T.Bt, fd.is(op, "is_eq"), fd.eqcall(t, Nil{}, a, b), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.not", [fd.eqcall(t, Nil{}, a, b)]), ord))

# compare and the comparisons at a digest (its bytes' order)
def fd.cmp.dig(+op: List<&2, U32>, a: T.Bt, b: T.Bt) -> T.Bt:
  +c = fd.callS("HsPrelude.HsDigest.cmp", [a, b])
  Bool.pick(T.Bt, fd.is(op, "cmp"), c, Bool.pick(T.Bt, Bool.or(fd.is(op, "max"), fd.is(op, "min")), fd.todo("fold:ord-at-type"), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.not", [fd.callS("Cmp.is_eq", [c])]), T.tba.call(T.BtVar{fd.cat(S.b("Cmp."), op)}, [c]))))

def fd.cmp(q: Tq, t: T.Bt, op: String, a: T.Bt, b: T.Bt) -> T.Bt:
  match q:
    case TqU32{}:
      fd.callS("U32." ++ op, [a, b])
    case TqDigest{}:
      fd.cmp.dig(S.b(op), a, b)
    case TqInt{}:
      fd.callS("HsPrelude.HsInt." ++ op, [a, b])
    case TqRat{}:
      fd.callS("HsPrelude.HsRational." ++ op, [a, b])
    case TqF32{}:
      fd.callS("F32." ++ op, [a, b])
    case TqNat{}:
      fd.callS("Nat." ++ op, [a, b])
    case TqChar{}:
      fd.cmp.char(S.b(op), a, b)
    case TqBool{}:
      fd.cmp.bool(S.b(op), a, b)
    case TqOther{}:
      fd.cmp.other(S.b(op), t, a, b)

# Nat's and F32's names for quot and rem, and Nat has no subtraction
def fd.num.nat(+op: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, fd.is(op, "quot"), S.b("div"), Bool.pick(List<&2, U32>, fd.is(op, "rem"), S.b("mod"), op))

def fd.num.natf(+pre: String, +op: List<&2, U32>, a: T.Bt, b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(op, "sub"), fd.todo("fold:int-sub"), T.tba.call(T.BtVar{fd.cat(S.b(pre), fd.num.nat(op))}, [a, b]))

def fd.num(q: Tq, op: String, a: T.Bt, b: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.num.natf("Nat.", S.b(op), a, b)
    case TqInt{}:
      fd.callS("HsPrelude.HsInt." ++ op, [a, b])
    case TqRat{}:
      fd.callS("HsPrelude.HsRational." ++ op, [a, b])
    case TqF32{}:
      T.tba.call(T.BtVar{fd.cat(S.b("F32."), fd.num.nat(S.b(op)))}, [a, b])
    case _:
      fd.todo("fold:num-at-type")

def fd.elem(q: Tq, +t: T.Bt, x: T.Bt, xs: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.v("HsPrelude.HsInt.is_eq")), xs, x])
    case TqNat{}:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.v("Nat.is_eq")), xs, x])
    case TqChar{}:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.v("Char.is_eq")), xs, x])
    case _:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.eqfn(t, Nil{})), xs, x])

# a * b at Nat, as a template
def fd.nmul() -> T.Bt:
  T.BtLam{T.BmLive{}, S.b("p"), T.BtLam{T.BmLive{}, S.b("q"), fd.callS("Nat.mul", [fd.v("p"), fd.v("q")])}}

# sum and product (prod) at Nat and at HsPrelude's HsInt (Int, Integer)
def fd.sum(q: Tq, +prod: Bool, +t: T.Bt, xs: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.callS("List.foldl", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Nat")), fd.tpl0(fd.ty0("Nat")), fd.tpl0(Bool.pick(T.Bt, prod, fd.nmul(), fd.v("Nat.add"))), xs, T.BtNat{Bool.pick(List<&2, U32>, prod, S.b("1"), S.b("0"))}])
    case TqInt{}:
      fd.callS("List.foldl", [fd.tpl0(fd.v("&2")), fd.tpl0(t), fd.tpl0(t), fd.tpl0(fd.v(Bool.pick(String, prod, "HsPrelude.HsInt.mul", "HsPrelude.HsInt.add"))), xs, T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([T.BtNat{Bool.pick(List<&2, U32>, prod, S.b("1"), S.b("0"))}])}])
    case _:
      fd.todo("fold:sum-at-type")

def fd.show(q: Tq, x: T.Bt) -> T.Bt:
  match q:
    case TqDigest{}:
      fd.callS("HsPrelude.HsDigest.hexs", [x])
    case TqInt{}:
      fd.callS("HsPrelude.HsInt.show", [x])
    case TqRat{}:
      fd.callS("HsPrelude.HsRational.show", [x])
    case TqNat{}:
      fd.callS("String.to_list", [fd.callS("Nat.show", [x])])
    case _:
      fd.todo("fold:show-at-type")

# showsPrec d x r at base's types (GHC.Show's instances): HsPrelude's
# HsShow at Int, Char, Bool, (), String, lists, Maybe, pairs, maps and sets
# (prelude/HsShowMore.bend; the precedence an
# HsInt: a package through the specialiser); else out (fold:show-at-type)
def fd.sp.zero() -> T.Bt:
  T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([T.BtNat{S.b("0")}])}

def fd.sp.ischar(t: T.Bt) -> Bool:
  match t:
    case T.BtTyApp{n, a}:
      fd.is(n, "Char")
    case _:
      False{}

def fd.sp.prim(q: Tq, +n: List<&2, U32>, +d: T.Bt, +x: T.Bt, +r: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("HsPrelude.HsShow.int", [d, x, r])
    case TqRat{}:
      fd.callS("HsPrelude.HsRational.shows", [d, x, r])
    case TqNat{}:
      fd.callS("HsPrelude.HsShow.nat", [d, x, r])
    case TqChar{}:
      fd.callS("HsPrelude.HsShow.charq", [x, r])
    case TqBool{}:
      fd.callS("HsPrelude.HsShow.bool", [x, r])
    case TqDigest{}:
      fd.callS("HsPrelude.HsShow.string", [fd.callS("HsPrelude.HsDigest.hexs", [x]), r])
    case _:
      Bool.pick(T.Bt, fd.is(n, "Unit"), fd.callS("HsPrelude.HsShow.unit", [x, r]), fd.todo("fold:show-at-type"))

def fd.sp(t: T.Bt, +d: T.Bt, +x: T.Bt, +r: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtANil{}}:
      fd.sp.prim(fd.tq.of(n), n, d, x, r)
    case T.BtTyApp{+n, T.BtArgs{+q, T.BtArgs{+a, T.BtANil{}}}}:
      +ch = Bool.and(fd.is(n, "List"), fd.sp.ischar(a))
      Bool.pick(T.Bt, ch, fd.callS("HsPrelude.HsShow.str", [x, r]), Bool.pick(T.Bt, fd.is(n, "List"), fd.callS("HsPrelude.HsShow.list", [fd.tpl0(a), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(a, fd.sp.zero(), fd.v("sy_"), fd.v("ss_"))}}), x, r]), Bool.pick(T.Bt, fd.is(n, "Maybe"), fd.callS("HsPrelude.HsShow.maybe", [fd.tpl0(a), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(a, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), d, x, r]), Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), fd.callS("HsPrelude.HsShow.map", [fd.tpl0(q), fd.tpl0(a), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(q, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(a, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), d, x, r]), fd.todo("fold:show-at-type")))))
    case T.BtTyApp{+n, T.BtArgs{+k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsSet"), fd.callS("HsPrelude.HsShow.set", [fd.tpl0(k), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(k, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), d, x, r]), fd.todo("fold:show-at-type"))
    case T.BtTyApp{+n, T.BtArgs{_, T.BtArgs{_, T.BtArgs{+a, T.BtArgs{T.BtLam{_, _, +b}, T.BtANil{}}}}}}:
      Bool.pick(T.Bt, fd.is(n, "Sigma"), fd.callS("HsPrelude.HsShow.pair", [fd.tpl0(a), fd.tpl0(b), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(a, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), fd.tpl0(T.BtLam{T.BmLive{}, S.b("sd_"), T.BtLam{T.BmLive{}, S.b("sy_"), T.BtLam{T.BmLive{}, S.b("ss_"), fd.sp(b, fd.v("sd_"), fd.v("sy_"), fd.v("ss_"))}}}), x, r]), fd.todo("fold:show-at-type"))
    case _:
      fd.todo("fold:show-at-type")

# show x at a type fd.show has no rule for: showsPrec 0 x ""
def fd.show.at(q: Tq, t: T.Bt, x: T.Bt) -> T.Bt:
  match q:
    case TqDigest{}:
      fd.show(TqDigest{}, x)
    case TqInt{}:
      fd.show(TqInt{}, x)
    case TqRat{}:
      fd.show(TqRat{}, x)
    case TqNat{}:
      fd.show(TqNat{}, x)
    case _:
      fd.sp(t, fd.sp.zero(), x, fd.con0("Nil"))

def fd.succ(q: Tq, x: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("HsPrelude.HsInt.succ", [x])
    case TqNat{}:
      T.BtSucc{x}
    case _:
      fd.todo("fold:succ-at-type")

# Monads and functors at Maybe, Either e and lists: a do block is GHC's
# >>= and >> (FORMAT: expanded), each a closure Base's Maybe.bind or the
# prelude's hs.either.bind calls
type Mk is Data:
  MkMaybe{}
  MkEither{e: T.Bt}
  MkList{}
  MkState{s: T.Bt}
  MkExS{e: T.Bt, s: T.Bt}
  MkIdentity{}
  MkPc{}
  MkRd{r: T.Bt}
  MkRde{r: T.Bt, e: T.Bt}
  MkWr{w: T.Bt}
  MkWre{w: T.Bt, e: T.Bt}
  MkOther{}

def fd.mk.one(+n: List<&2, U32>, +a: T.Bt) -> Mk:
  Bool.pick(Mk, fd.is(n, "Maybe"), MkMaybe{}, Bool.pick(Mk, fd.is(n, "hs.State"), MkState{a}, Bool.pick(Mk, fd.is(n, "hs.Reader"), MkRd{a}, Bool.pick(Mk, fd.is(n, "hs.Writer"), MkWr{a}, MkOther{}))))

def fd.mk.two(+n: List<&2, U32>, +e: T.Bt, +s: T.Bt) -> Mk:
  Bool.pick(Mk, fd.is(n, "hs.ExceptS"), MkExS{e, s}, Bool.pick(Mk, fd.is(n, "hs.ReaderE"), MkRde{e, s}, Bool.pick(Mk, fd.is(n, "hs.WriterE"), MkWre{e, s}, MkOther{})))

def fd.mk.three(either: Bool, e: T.Bt) -> Mk:
  match either:
    case True{}:
      MkEither{e}
    case False{}:
      MkOther{}

def fd.mk.var(list: Bool) -> Mk:
  match list:
    case True{}:
      MkList{}
    case False{}:
      MkOther{}

# what the monad (or functor) argument m, as the fold wrote it, is
def fd.mk(m: T.Bt) -> Mk:
  match m:
    case T.BtTyApp{+n, T.BtANil{}}:
      Bool.pick(Mk, fd.is(n, "hs.Identity"), MkIdentity{}, Bool.pick(Mk, fd.is(n, "hs.Pc"), MkPc{}, MkOther{}))
    case T.BtTyApp{+n, T.BtArgs{a, T.BtANil{}}}:
      fd.mk.one(n, a)
    case T.BtTyApp{+n, T.BtArgs{e, T.BtArgs{s, T.BtANil{}}}}:
      fd.mk.two(n, e, s)
    case T.BtTyApp{n, T.BtArgs{a, T.BtArgs{b, T.BtArgs{e, T.BtANil{}}}}}:
      fd.mk.three(fd.is(n, "Either"), e)
    case T.BtVar{n}:
      fd.mk.var(fd.is(n, "List"))
    case _:
      MkOther{}

# mempty at a list, a Map, a Set, Ordering (EQ) and ()
def fd.mempty(t: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{+q, T.BtArgs{+a, T.BtANil{}}}}:
      Bool.pick(T.Bt, fd.is(n, "List"), fd.con0("Nil"), Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), fd.callS("HsPrelude.HsMap.empty", [fd.tpl0(q), fd.tpl0(a)]), fd.todo("fold:monoid-at-type")))
    case T.BtTyApp{+n, T.BtArgs{+k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsSet"), fd.callS("HsPrelude.HsSet.empty", [fd.tpl0(k)]), fd.todo("fold:monoid-at-type"))
    case T.BtTyApp{+n, T.BtANil{}}:
      Bool.pick(T.Bt, fd.is(n, "Cmp"), fd.con0("EQ"), Bool.pick(T.Bt, fd.is(n, "Unit"), fd.con0("Unit"), fd.todo("fold:monoid-at-type")))
    case _:
      fd.todo("fold:monoid-at-type")

# mconcat at a list of lists (concat) or of Sets (unions)
def fd.mconcat(t: T.Bt, xs: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{+q, T.BtArgs{+a, T.BtANil{}}}}:
      Bool.pick(T.Bt, fd.is(n, "List"), fd.callS("List.concat", [fd.v("&2"), a, xs]), fd.todo("fold:monoid-at-type"))
    case T.BtTyApp{+n, T.BtArgs{+k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsSet"), fd.callS("HsPrelude.HsSet.unions", [fd.tpl0(k), fd.tpl0(fd.cmpfn(k)), xs]), fd.todo("fold:monoid-at-type"))
    case _:
      fd.todo("fold:monoid-at-type")

# <> at a list
# (and at a Map or a Set: union, left-biased)
def fd.semi(t: T.Bt, +x: T.Bt, +y: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{+q, T.BtArgs{+a, T.BtANil{}}}}:
      Bool.pick(T.Bt, fd.is(n, "List"), fd.callS("List.append", [fd.v("&2"), a, x, y]), Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), fd.callS("HsPrelude.HsMap.union", [fd.tpl0(q), fd.tpl0(a), fd.tpl0(fd.cmpfn(q)), x, y]), fd.todo("fold:semigroup-at-type")))
    case T.BtTyApp{+n, T.BtArgs{+k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsSet"), fd.callS("HsPrelude.HsSet.union", [fd.tpl0(k), fd.tpl0(fd.cmpfn(k)), x, y]), fd.todo("fold:semigroup-at-type"))
    case _:
      fd.todo("fold:semigroup-at-type")

# w's mempty and <> (a function of two), the arguments a Writer's
# >>=, pure and fmap take after W (and E)
def fd.wmon(+w: T.Bt) -> List<&2, T.Bt>:
  [fd.mempty(w), T.BtLam{T.BmLive{}, S.b("wx_"), T.BtLam{T.BmLive{}, S.b("wy_"), fd.semi(w, fd.v("wx_"), fd.v("wy_"))}}]

def fd.bind(k: Mk, a: T.Bt, b: T.Bt, x: T.Bt, f: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      fd.callS("Maybe.bind", [fd.v("&2"), a, b, x, f])
    case MkEither{e}:
      fd.callS("hs.either.bind", [e, a, b, x, f])
    case MkState{s}:
      fd.callS("hs.state.bind", [s, a, b, x, f])
    case MkExS{e, s}:
      fd.callS("hs.exs.bind", [e, s, a, b, x, f])
    case MkIdentity{}:
      T.tba.call(f, [x])
    case MkPc{}:
      fd.callS("HsPrelude.HsPc.bind", [a, b, x, f])
    case MkRd{r}:
      fd.callS("hs.rd.bind", [r, a, b, x, f])
    case MkRde{r, e}:
      fd.callS("hs.rde.bind", [r, e, a, b, x, f])
    case MkWr{+w}:
      fd.callS("hs.wr.bind", List.append(&2, T.Bt, w <> fd.wmon(w), [a, b, x, f]))
    case MkWre{+w, e}:
      fd.callS("hs.wre.bind", List.append(&2, T.Bt, w <> e <> fd.wmon(w), [a, b, x, f]))
    case _:
      fd.todo("fold:monad-at-type")

def fd.pure(k: Mk, a: T.Bt, x: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      T.BtCon{S.b("Some"), T.tba.args([x])}
    case MkEither{e}:
      T.BtCon{S.b("Inr"), T.tba.args([x])}
    case MkList{}:
      T.BtCon{S.b("Con"), T.tba.args([x, fd.con0("Nil")])}
    case MkState{s}:
      fd.callS("hs.state.pure", [s, a, x])
    case MkExS{e, s}:
      fd.callS("hs.exs.pure", [e, s, a, x])
    case MkIdentity{}:
      x
    case MkPc{}:
      fd.callS("HsPrelude.HsPc.pure", [a, x])
    case MkRd{r}:
      fd.callS("hs.rd.pure", [r, a, x])
    case MkRde{r, e}:
      fd.callS("hs.rde.pure", [r, e, a, x])
    case MkWr{+w}:
      fd.callS("hs.wr.pure", List.append(&2, T.Bt, w <> fd.wmon(w), [a, x]))
    case MkWre{+w, e}:
      fd.callS("hs.wre.pure", List.append(&2, T.Bt, w <> e <> fd.wmon(w), [a, x]))
    case _:
      fd.todo("fold:monad-at-type")

def fd.untpl(g: T.Bt) -> T.Bt:
  match g:
    case T.BtTplArg{h}:
      h
    case h:
      h

def fd.fmap(k: Mk, a: T.Bt, b: T.Bt, g: T.Bt, x: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      fd.callS("Maybe.map", [fd.v("&2"), a, b, fd.untpl(g), x])
    case MkEither{e}:
      fd.callS("hs.either.map", [e, a, b, fd.untpl(g), x])
    case MkState{s}:
      fd.callS("hs.state.map", [s, a, b, fd.untpl(g), x])
    case MkExS{e, s}:
      fd.callS("hs.exs.map", [e, s, a, b, fd.untpl(g), x])
    case MkIdentity{}:
      T.tba.call(fd.untpl(g), [x])
    case MkList{}:
      fd.callS("hs.map", [fd.tpl0(a), fd.tpl0(b), g, x])
    case MkPc{}:
      fd.callS("HsPrelude.HsPc.map", [a, b, fd.untpl(g), x])
    case MkRd{r}:
      fd.callS("hs.rd.map", [r, a, b, fd.untpl(g), x])
    case MkRde{r, e}:
      fd.callS("hs.rde.map", [r, e, a, b, fd.untpl(g), x])
    case MkWr{+w}:
      fd.callS("hs.wr.map", List.append(&2, T.Bt, w <> fd.wmon(w), [a, b, fd.untpl(g), x]))
    case MkWre{+w, e}:
      fd.callS("hs.wre.map", List.append(&2, T.Bt, w <> e <> fd.wmon(w), [a, b, fd.untpl(g), x]))
    case _:
      fd.todo("fold:fmap-at-type")

# A folded fmap, >>= or pure of the monad k, so that <*> after one is a
# >>=: g <$> y <*> x is y >>= \v -> fmap (g v) x, (y >>= \v -> e) <*> x is
# y >>= \v -> (e <*> x), and pure g <*> x is fmap g x. A chain f <$> a <*>
# b <*> c then holds no Maybe or Either of a function (a function is
# Type, and their parts are Data).
type Apv is Data:
  ApFmap{a0: T.Bt, g: T.Bt, y: T.Bt}
  ApBind{a0: T.Bt, y: T.Bt, v: List<&2, U32>, body: T.Bt}
  ApPure{g: T.Bt}
  ApOther{f: T.Bt}

def fd.ap.argl(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> fd.ap.argl(t)
    case _:
      Nil{}

def fd.ap.drop(n: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match n xs:
    case Succ{p} _ <> t:
      fd.ap.drop(p, t)
    case _ ys:
      ys

# k's fmap, >>= and pure (at State and ExceptT, calls), and how many of
# their arguments come before the element types
def fd.ap.pre(k: Mk) -> Nat:
  match k:
    case MkExS{e, s}:
      2n
    case MkRde{r, e}:
      2n
    case MkWr{w}:
      3n
    case MkWre{w, e}:
      4n
    case MkPc{}:
      0n
    case _:
      1n

def fd.ap.name(k: Mk, +w: Nat) -> String:
  match k:
    case MkMaybe{}:
      Bool.pick(String, Nat.is_eq(w, 0n), "Maybe.map", Bool.pick(String, Nat.is_eq(w, 1n), "Maybe.bind", ""))
    case MkEither{e}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.either.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.either.bind", ""))
    case MkState{s}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.state.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.state.bind", "hs.state.pure"))
    case MkExS{e, s}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.exs.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.exs.bind", "hs.exs.pure"))
    case MkPc{}:
      Bool.pick(String, Nat.is_eq(w, 0n), "HsPrelude.HsPc.map", Bool.pick(String, Nat.is_eq(w, 1n), "HsPrelude.HsPc.bind", "HsPrelude.HsPc.pure"))
    case MkRd{r}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.rd.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.rd.bind", "hs.rd.pure"))
    case MkRde{r, e}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.rde.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.rde.bind", "hs.rde.pure"))
    case MkWr{v}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.wr.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.wr.bind", "hs.wr.pure"))
    case MkWre{v, e}:
      Bool.pick(String, Nat.is_eq(w, 0n), "hs.wre.map", Bool.pick(String, Nat.is_eq(w, 1n), "hs.wre.bind", "hs.wre.pure"))
    case _:
      ""

def fd.ap.view.call(ism: Bool, isb: Bool, isp: Bool, xs: List<&2, T.Bt>, f: T.Bt) -> Apv:
  match ism isb isp xs:
    case True{} _ _ a0 <> ab <> g <> y <> Nil{}:
      ApFmap{a0, g, y}
    case False{} True{} _ a0 <> mb <> y <> T.BtLam{m, v, body} <> Nil{}:
      ApBind{a0, y, v, body}
    case False{} False{} True{} a <> g <> Nil{}:
      ApPure{g}
    case _ _ _ _:
      ApOther{f}

def fd.ap.view(+k: Mk, +f: T.Bt) -> Apv:
  match f:
    case T.BtApp{T.BtVar{+n}, args}:
      fd.ap.view.call(fd.is(n, fd.ap.name(k, 0n)), fd.is(n, fd.ap.name(k, 1n)), fd.is(n, fd.ap.name(k, 2n)), fd.ap.drop(fd.ap.pre(k), fd.ap.argl(args)), f)
    case T.BtCon{+c, T.BtArgs{g, T.BtANil{}}}:
      Bool.pick(Apv, Bool.or(fd.is(c, "Some"), fd.is(c, "Inr")), ApPure{g}, ApOther{f})
    case _:
      ApOther{f}

def fd.ap.var(n: Nat) -> List<&2, U32>:
  List.append(&2, U32, S.b("apx_"), fd.nshow(n))

# f <*> x at k (not Identity, not State), chains of at most n
def fd.ap.go(n: Nat, v: Apv, +k: Mk, +a: T.Bt, +b: T.Bt, x: T.Bt) -> T.Bt:
  match n v:
    case Succ{+p} ApFmap{a0, g, y}:
      fd.bind(k, a0, b, y, T.BtLam{T.BmLive{}, fd.ap.var(p), fd.fmap(k, a, b, fd.tpl0(T.tba.call(fd.untpl(g), [T.BtVar{fd.ap.var(p)}])), x)})
    case Succ{p} ApBind{a0, y, w, body}:
      fd.bind(k, a0, b, y, T.BtLam{T.BmLive{}, w, fd.ap.go(p, fd.ap.view(k, body), k, a, b, x)})
    case Succ{p} ApPure{g}:
      fd.fmap(k, a, b, fd.tpl0(g), x)
    case _ ApOther{f}:
      fd.bind(k, T.BtPi{T.BmLive{}, S.b("_"), False{}, a, b}, b, f, T.BtLam{T.BmLive{}, S.b("ap_"), fd.fmap(k, a, b, fd.tpl0(fd.v("ap_")), x)})
    case Zero{} _:
      fd.todo("fold:applicative-chain")

# <*>, and MonadState's methods (mtl), at State s
# (<*> at Maybe, Either e and ExceptT e (State s): see Apv)
def fd.ap(k: Mk, +a: T.Bt, +b: T.Bt, f: T.Bt, x: T.Bt) -> T.Bt:
  match k:
    case MkIdentity{}:
      T.tba.call(fd.untpl(f), [x])
    case MkState{s}:
      fd.callS("hs.state.ap", [s, a, b, fd.untpl(f), x])
    case +k2:
      fd.ap.go(16n, fd.ap.view(k2, f), k2, a, b, x)

def fd.st.get(k: Mk, s: T.Bt) -> T.Bt:
  match k:
    case MkState{t}:
      fd.callS("hs.state.get", [s])
    case MkExS{e, t}:
      fd.callS("hs.exs.get", [e, s])
    case _:
      fd.todo("fold:monadstate-at-type")

# put, modify, gets (op) at State or ExceptT over State (mtl lifts
# MonadState through ExceptT)
def fd.st.call(k: Mk, op: String, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkState{t}:
      fd.callS("hs.state." ++ op, xs)
    case MkExS{e, t}:
      fd.callS("hs.exs." ++ op, e <> xs)
    case _:
      fd.todo("fold:monadstate-at-type")

# the type m a at the monad k (a when's or an unless's branches)
def fd.mty(k: Mk, a: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      T.BtTyApp{S.b("Maybe"), T.tba.args([fd.v("&2"), a])}
    case MkEither{e}:
      fd.either(e, a)
    case MkList{}:
      fd.list(a)
    case MkState{s}:
      fd.ty.st(s, a)
    case MkExS{e, s}:
      fd.ty.st(s, fd.either(e, a))
    case MkIdentity{}:
      a
    case MkPc{}:
      fd.ty.pc(a)
    case MkRd{r}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, a}
    case MkRde{r, e}:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, r, fd.either(e, a)}
    case MkWr{w}:
      fd.pair(a, w)
    case MkWre{w, e}:
      fd.either(e, fd.pair(a, w))
    case MkOther{}:
      fd.todo("fold:monad-at-type")

# when c m and unless c m: an if whose other branch is pure ()
def fd.when.if(yes: Bool, r: T.Bt, c: T.Bt, m: T.Bt, p: T.Bt) -> T.Bt:
  match yes:
    case True{}:
      fd.callS("Bool.if", [r, c, T.BtLam{T.BmLive{}, S.b("_"), m}, T.BtLam{T.BmLive{}, S.b("_"), p}])
    case False{}:
      fd.callS("Bool.if", [r, c, T.BtLam{T.BmLive{}, S.b("_"), p}, T.BtLam{T.BmLive{}, S.b("_"), m}])

def fd.when(+k: Mk, yes: Bool, c: T.Bt, m: T.Bt) -> T.Bt:
  fd.when.if(yes, fd.mty(k, fd.ty0("Unit")), c, m, fd.pure(k, fd.ty0("Unit"), fd.con0("Unit")))

# liftA2 f x y: at Identity f x y, else x >>= \\la_ -> fmap (f la_) y
def fd.lift2(+k: Mk, a: T.Bt, +b: T.Bt, +c: T.Bt, f: T.Bt, x: T.Bt, y: T.Bt) -> T.Bt:
  match k:
    case MkIdentity{}:
      T.tba.call(T.tba.call(f, [x]), [y])
    case _:
      fd.bind(k, a, c, x, T.BtLam{T.BmLive{}, S.b("la_"), fd.fmap(k, b, c, fd.tpl0(T.tba.call(f, [fd.v("la_")])), y)})

# MonadError's throwError at ExceptT over State, or at Either
def fd.throw(k: Mk, a: T.Bt, x: T.Bt) -> T.Bt:
  match k:
    case MkExS{e, s}:
      fd.callS("hs.exs.throw", [e, s, a, x])
    case MkEither{e}:
      T.BtCon{S.b("Inl"), T.tba.args([x])}
    case MkRde{r, e}:
      fd.callS("hs.rde.throw", [r, e, a, x])
    case MkWre{w, e}:
      T.BtCon{S.b("Inl"), T.tba.args([x])}
    case _:
      fd.todo("fold:monaderror-at-type")

# MonadReader's ask, local, asks and reader (mtl, and transformers' local)
# at ReaderT over Identity or over Either (op's arguments after r and e)
def fd.rd.call(k: Mk, op: String, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkRd{r}:
      fd.callS("hs.rd." ++ op, r <> xs)
    case MkRde{r, e}:
      fd.callS("hs.rde." ++ op, r <> e <> xs)
    case _:
      fd.todo("fold:monadreader-at-type")

def fd.lift.wr(+w: T.Bt, +m: T.Bt, +a: T.Bt, x: T.Bt) -> T.Bt:
  fd.fmap(fd.mk(m), a, fd.pair(a, w), fd.tpl0(T.BtLam{T.BmLive{}, S.b("wl_"), T.BtCon{S.b("Tuple"), T.tba.args([fd.v("wl_"), fd.mempty(w)])}}), x)

def fd.lift.if(rd: Bool, wr: Bool, r: T.Bt, m: T.Bt, a: T.Bt, x: T.Bt) -> T.Bt:
  match rd wr:
    case True{} _:
      fd.callS("hs.rd.pure", [r, fd.mty(fd.mk(m), a), x])
    case False{} True{}:
      fd.lift.wr(r, m, a, x)
    case False{} False{}:
      fd.todo("fold:lift-at-type")

# MonadTrans's lift at ReaderT r (t) of the monad m: a Reader that ignores
# its environment, the term at m a (pure at Reader r of m a)
# (at WriterT w of m: fmap at m of a pair with mempty at w, the term
# logging nothing)
def fd.lift(t: T.Bt, m: T.Bt, a: T.Bt, x: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{r, T.BtANil{}}}:
      fd.lift.if(fd.is(n, "hs.ReaderT"), fd.is(n, "hs.WriterT"), r, m, a, x)
    case _:
      fd.todo("fold:lift-at-type")

# runExceptT over State is the term itself (ExceptT's newtype)
def fd.runexc(k: Em, x: T.Bt) -> T.Bt:
  match k:
    case EmState{s}:
      x
    case _:
      fd.todo("fold:runexceptt-at-type")

# mapM_/forM_, mapM/forM/traverse and foldM at a list, at State or ExceptT
# over State: the prelude's, f a template
def fd.mapm.at(k: Mk, f: String, a: T.Bt, b: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkState{s}:
      fd.callS("hs.state." ++ f, List.append(&2, T.Bt, [fd.tpl0(s), fd.tpl0(a), fd.tpl0(b)], xs))
    case MkExS{e, s}:
      fd.callS("hs.exs." ++ f, List.append(&2, T.Bt, [fd.tpl0(e), fd.tpl0(s), fd.tpl0(a), fd.tpl0(b)], xs))
    case MkEither{e}:
      fd.callS("HsPrelude.HsList.either." ++ f, List.append(&2, T.Bt, [fd.tpl0(e), fd.tpl0(a), fd.tpl0(b)], xs))
    case MkMaybe{}:
      fd.callS("HsPrelude.HsList.maybe." ++ f, List.append(&2, T.Bt, [fd.tpl0(a), fd.tpl0(b)], xs))
    case _:
      fd.todo("fold:monad-at-type")

# sequence and sequenceA (t (m a) -> m (t a)) at a list, at State, ExceptT
# over State, Either and Maybe: mapM id, the prelude's
def fd.seq.at(k: Mk, a: T.Bt, l: T.Bt) -> T.Bt:
  match k:
    case MkState{s}:
      fd.callS("hs.state.seq", [fd.tpl0(s), fd.tpl0(a), l])
    case MkExS{e, s}:
      fd.callS("hs.exs.seq", [fd.tpl0(e), fd.tpl0(s), fd.tpl0(a), l])
    case MkEither{e}:
      fd.callS("HsPrelude.HsList.either.seq", [fd.tpl0(e), fd.tpl0(a), l])
    case MkMaybe{}:
      fd.callS("HsPrelude.HsList.maybe.seq", [fd.tpl0(a), l])
    case _:
      fd.todo("fold:monad-at-type")

# a sequence's container: a list only (its Traversable at Map is not here)
def fd.seq.list(c: T.Bt, t: T.Bt) -> T.Bt:
  match c:
    case T.BtVar{+n}:
      Bool.pick(T.Bt, fd.is(n, "List"), t, fd.todo("fold:traversable-not-list"))
    case _:
      fd.todo("fold:traversable-not-list")

# Integral's even and odd at Int (prelude/HsOrd.bend)
def fd.parity(q: Tq, op: String, x: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("HsPrelude.HsInt." ++ op, [x])
    case _:
      fd.todo("fold:parity-at-type")

# filterM (tys: the element) and zipWithM_ (the two elements and the
# answer) at a list, at State, ExceptT over State (each module's prelude),
# Either and Maybe (prelude/HsMonad.bend)
def fd.tpl0s(ts: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      fd.tpl0(t) <> fd.tpl0s(r)

def fd.mlist.at(k: Mk, f: String, tys: List<&2, T.Bt>, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkState{s}:
      fd.callS("hs.state." ++ f, List.append(&2, T.Bt, fd.tpl0(s) <> fd.tpl0s(tys), xs))
    case MkExS{e, s}:
      fd.callS("hs.exs." ++ f, List.append(&2, T.Bt, fd.tpl0(e) <> fd.tpl0(s) <> fd.tpl0s(tys), xs))
    case MkEither{e}:
      fd.callS("HsPrelude.HsList.either." ++ f, List.append(&2, T.Bt, fd.tpl0(e) <> fd.tpl0s(tys), xs))
    case MkMaybe{}:
      fd.callS("HsPrelude.HsList.maybe." ++ f, List.append(&2, T.Bt, fd.tpl0s(tys), xs))
    case _:
      fd.todo("fold:monad-at-type")

# negate, abs, signum at HsInt (abs at Nat is the number)
def fd.neg(q: Tq, op: String, x: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("HsPrelude.HsInt." ++ op, [x])
    case TqRat{}:
      fd.callS("HsPrelude.HsRational." ++ op, [x])
    case TqNat{}:
      Bool.pick(T.Bt, fd.is(S.b(op), "abs"), x, fd.todo("fold:int-sub"))
    case _:
      fd.todo("fold:num-at-type")

# fromIntegral and toInteger between the same kinds of number
def fd.conv(a: Tq, b: Tq, x: T.Bt) -> T.Bt:
  match a b:
    case TqInt{} TqInt{}:
      x
    case TqNat{} TqNat{}:
      x
    case TqNat{} TqInt{}:
      T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([x])}
    case TqU32{} TqInt{}:
      T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([fd.callS("U32.to_nat", [x])])}
    case TqU32{} TqNat{}:
      fd.callS("U32.to_nat", [x])
    case TqU32{} TqU32{}:
      x
    case TqInt{} TqRat{}:
      fd.callS("HsPrelude.HsRational.of", [x])
    case TqRat{} TqRat{}:
      x
    case _ _:
      fd.todo("fold:conversion")

# toEnum and fromEnum at HsInt (Int's Enum: the number itself)
def fd.idat(q: Tq, x: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      x
    case TqRat{}:
      fd.callS("HsPrelude.HsRational.of", [x])
    case _:
      fd.todo("fold:enum-at-type")

# base's functions at Int when Int is HsInt (Spec's HsPrelude.Z.*): a
# count is a Nat to Base, negative ones as 0 (take, drop and replicate
# below zero are the empty case, as Haskell's); a length an HsInt
def fd.hsint.of(x: T.Bt) -> T.Bt:
  T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([x])}

def fd.hsint.nat(x: T.Bt) -> T.Bt:
  fd.callS("HsPrelude.HsInt.count", [x])

def fd.z(+op: List<&2, U32>, tys: List<&2, T.Bt>, xs: List<&2, T.Bt>) -> T.Bt:
  match tys xs:
    case +c <> +t <> _ +a <> _:
      Bool.pick(T.Bt, fd.is(op, "length"), fd.foldable(c, fd.hsint.of(fd.callS("List.length", [fd.v("&2"), t, fd.fl(c, t, a)]))), fd.todo("fold:z"))
    case +t <> _ +n <> +a <> _:
      Bool.pick(T.Bt, fd.is(op, "take"), fd.callS("List.take", [fd.v("&2"), t, a, fd.hsint.nat(n)]), Bool.pick(T.Bt, fd.is(op, "drop"), fd.callS("List.drop", [fd.v("&2"), t, a, fd.hsint.nat(n)]), Bool.pick(T.Bt, fd.is(op, "replicate"), fd.callS("List.replicate", [t, fd.hsint.nat(n), a]), fd.todo("fold:z"))))
    case Nil{} +x <> _:
      Bool.pick(T.Bt, fd.is(op, "ord"), fd.hsint.of(fd.callS("U32.to_nat", [fd.callS("Char.to_u32", [x])])), Bool.pick(T.Bt, fd.is(op, "chr"), fd.callS("Char.from_u32", [fd.callS("U32.from_nat", [fd.hsint.nat(x)])]), fd.todo("fold:z")))
    case _ _:
      fd.todo("fold:z")

# a function of one argument: HsPrelude's f, or the argument itself (f empty)
def fd.one(+f: List<&2, U32>, +x: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, S.eq(f, Nil{}), x, T.tba.call(T.BtVar{f}, [x]))

# [a .. b] at HsInt
def fd.range(q: Tq, a: T.Bt, b: T.Bt) -> T.Bt:
  match q:
    case TqInt{}:
      fd.callS("HsPrelude.HsInt.range", [a, b])
    case _:
      fd.todo("fold:range-at-type")

# Data.Map's, Data.IntMap's, Data.Set's and Data.IntSet's functions: a call
# of HsPrelude's def d, its templates p (K, V, W, B, L: the type GHC gave
# that role in r, its type arguments; K at an IntMap or IntSet Int; c, d:
# compare at K, at L), then the arguments, the first nt of them templates
def fd.dm.find(r: List<&2, U32>, tys: List<&2, T.Bt>, +c: U32) -> Maybe<&2, T.Bt>:
  match r tys:
    case +h <> rt t <> tt:
      Bool.pick(Maybe<&2, T.Bt>, U32.is_eq(h, c), Some{t}, fd.dm.find(rt, tt, c))
    case _ _:
      None{}

def fd.dm.role.of(m: Maybe<&2, T.Bt>, +c: U32) -> T.Bt:
  match m:
    case Some{t}:
      t
    case None{}:
      Bool.pick(T.Bt, U32.is_eq(c, 75), fd.ty0("Nat"), fd.todo("fold:map-type-argument"))

def fd.dm.role(+r: List<&2, U32>, +tys: List<&2, T.Bt>, +c: U32) -> T.Bt:
  fd.dm.role.of(fd.dm.find(r, tys, c), c)

def fd.dm.tp.cd(+r: List<&2, U32>, +tys: List<&2, T.Bt>, +c: U32) -> T.Bt:
  Bool.pick(T.Bt, U32.is_eq(c, 99), fd.tpl0(fd.cmpfn(fd.dm.role(r, tys, 75))), Bool.pick(T.Bt, U32.is_eq(c, 100), fd.tpl0(fd.cmpfn(fd.dm.role(r, tys, 76))), fd.tpl0(fd.dm.role(r, tys, c))))

def fd.dm.tp(+r: List<&2, U32>, +tys: List<&2, T.Bt>, +c: U32) -> T.Bt:
  Bool.pick(T.Bt, U32.is_eq(c, 101), fd.tpl0(fd.eqfn(fd.dm.role(r, tys, 75), Nil{})), Bool.pick(T.Bt, U32.is_eq(c, 115), fd.tpl0(T.BtLam{T.BmLive{}, S.b("s_"), fd.succ(fd.tq(fd.dm.role(r, tys, 75)), fd.v("s_"))}), fd.dm.tp.cd(r, tys, c)))

def fd.dm.tps(+r: List<&2, U32>, +tys: List<&2, T.Bt>, p: List<&2, U32>) -> List<&2, T.Bt>:
  match p:
    case Nil{}:
      Nil{}
    case +c <> t:
      fd.dm.tp(r, tys, c) <> fd.dm.tps(r, tys, t)

def fd.dm.vs(+ls: List<&2, List<&2, U32>>, nt: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match nt xs:
    case Succ{k} x <> t:
      fd.tpl(ls, x) <> fd.dm.vs(ls, k, t)
    case _ ys:
      ys

def fd.dm(d: String, +r: List<&2, U32>, p: List<&2, U32>, nt: Nat, +tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  fd.callS("HsPrelude." ++ d, List.append(&2, T.Bt, fd.dm.tps(r, tys, p), fd.dm.vs(ls, nt, xs)))

# the last argument (a Foldable's container) as a list
def fd.dmf.cons(+c: T.Bt, +a: T.Bt, xs: List<&2, T.Bt>, x: T.Bt) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      [fd.fl(c, a, x)]
    case y <> t:
      x <> fd.dmf.cons(c, a, t, y)

def fd.dmf.last(+c: T.Bt, +a: T.Bt, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      fd.dmf.cons(c, a, t, x)

# a Foldable's function (role T its container, K the element): HsPrelude's
# list def d of the container as a list (see fd.dm)
def fd.dmf(d: String, +r: List<&2, U32>, p: List<&2, U32>, nt: Nat, +tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  +c = fd.dm.role(r, tys, 84)
  +a = fd.dm.role(r, tys, 75)
  fd.foldable(c, fd.dm(d, r, p, nt, tys, fd.dmf.last(c, a, xs), ls))

# whether a type (or a type constructor) is named n
def fd.bi.is(t: T.Bt, s: String) -> Bool:
  match t:
    case T.BtVar{n}:
      fd.is(n, s)
    case T.BtTyApp{n, a}:
      fd.is(n, s)
    case _:
      False{}

def fd.dm.b(d: List<&2, U32>, +r: List<&2, U32>, p: List<&2, U32>, nt: Nat, +tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  T.tba.call(T.BtVar{fd.cat(S.b("HsPrelude."), d)}, List.append(&2, T.Bt, fd.dm.tps(r, tys, p), fd.dm.vs(ls, nt, xs)))

# Data.Bifunctor's first, second and bimap (op) at Either and at pairs:
# HsPrelude's HsList.op.either and HsList.op.pair (GHC's type arguments the
# class's p, then the method's in order)
def fd.bi(+op: List<&2, U32>, +tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  +p = Maybe.default(&2, T.Bt, List.head(&2, T.Bt, tys), fd.ty0("Unit"))
  +ei = fd.bi.is(p, "Either")
  +pr = fd.bi.is(p, "Tuple2")
  +bm = fd.is(op, "bimap")
  +d = fd.cat3(S.b("HsList."), op, Bool.pick(List<&2, U32>, ei, S.b(".either"), S.b(".pair")))
  Bool.pick(T.Bt, Bool.or(ei, pr), fd.dm.b(d, Bool.pick(List<&2, U32>, bm, S.b("PABCD"), S.b("PABC")), Bool.pick(List<&2, U32>, bm, S.b("ABCD"), S.b("ABC")), 0n, tys, xs, ls), fd.todo("fold:bifunctor-at-type"))

# fmap at a Map k (its values), else at the functor m
def fd.fmap.at(m: T.Bt, +a: T.Bt, +b: T.Bt, +g: T.Bt, +x: T.Bt) -> T.Bt:
  match m:
    case T.BtTyApp{+n, T.BtArgs{+k, T.BtANil{}}}:
      Bool.pick(T.Bt, fd.is(n, "HsPrelude.HsMap"), fd.callS("HsPrelude.HsMap.map", [fd.tpl0(k), fd.tpl0(a), fd.tpl0(b), g, x]), fd.fmap(fd.mk(T.BtTyApp{n, T.BtArgs{k, T.BtANil{}}}), a, b, g, x))
    case m2:
      fd.fmap(fd.mk(m2), a, b, g, x)

# Recursive's project and cata and Corecursive's embed
# (Data.Functor.Foldable) at Fix f and Cofree f w: cata is the functor's
# G.cata or G.cata.cofree (see Recursion schemes)
def fd.project.if(fix: Bool, cof: Bool, l: T.Bt, rest: T.Bt, x: T.Bt) -> T.Bt:
  match fix cof rest:
    case True{} _ _:
      fd.callS("HsPrelude.Fix.unFix", [l, x])
    case False{} True{} T.BtArgs{w, _}:
      fd.callS("HsPrelude.Cofree.project", [l, w, x])
    case _ _ _:
      fd.todo("fold:project-at-type")

def fd.project(t: T.Bt, x: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{l, rest}}:
      fd.project.if(fd.is(n, "HsPrelude.Fix"), fd.is(n, "HsPrelude.Cofree"), l, rest, x)
    case _:
      fd.todo("fold:project-at-type")

def fd.embed.if(fix: Bool, cof: Bool, l: T.Bt, rest: T.Bt, x: T.Bt) -> T.Bt:
  match fix cof rest:
    case True{} _ _:
      T.BtCon{S.b("HsPrelude.Fix.Fix"), T.tba.args([x])}
    case False{} True{} T.BtArgs{w, _}:
      fd.callS("HsPrelude.Cofree.embed", [l, w, x])
    case _ _ _:
      fd.todo("fold:embed-at-type")

def fd.embed(t: T.Bt, x: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{+n, T.BtArgs{l, rest}}:
      fd.embed.if(fd.is(n, "HsPrelude.Fix"), fd.is(n, "HsPrelude.Cofree"), l, rest, x)
    case _:
      fd.todo("fold:embed-at-type")

# G.cata(~A.., ~R, ~alg, x) at Fix<(r_ => G<A.., r_>)>, and
# G.cata.cofree(~A.., ~W, ~R, ~alg, x) at Cofree<(r_ => G<A.., r_>), W>
def fd.cata.call(+n: List<&2, U32>, +s: String, args: T.Bt, more: List<&2, T.Bt>) -> T.Bt:
  T.tba.call(T.BtVar{fd.cat(n, S.b(s))}, List.append(&2, T.Bt, fd.tpls(fd.init(fd.spine(args))), more))

def fd.cata.if(fix: Bool, cof: Bool, own: Bool, +n: List<&2, U32>, args: T.Bt, rest: T.Bt, +r: T.Bt, g: T.Bt, x: T.Bt) -> T.Bt:
  match fix cof own rest:
    case True{} _ True{} _:
      fd.cata.call(n, Bool.pick(String, fd.isfn(r), ".cata.fn", ".cata"), args, [fd.tpl0(r), g, x])
    case False{} True{} True{} T.BtArgs{w, _}:
      fd.cata.call(n, Bool.pick(String, fd.isfn(r), ".cata.cofree.fn", ".cata.cofree"), args, [fd.tpl0(w), fd.tpl0(r), g, x])
    case _ _ _ _:
      fd.todo("fold:cata-at-type")

def fd.cata.of(+h: List<&2, U32>, l: T.Bt, rest: T.Bt, r: T.Bt, g: T.Bt, x: T.Bt) -> T.Bt:
  match l:
    case T.BtLam{m, v, T.BtTyApp{+n, args}}:
      fd.cata.if(fd.is(h, "HsPrelude.Fix"), fd.is(h, "HsPrelude.Cofree"), Bool.not(Bool.or(fd.is(n, "List"), Bool.or(fd.is(n, "Maybe"), fd.is(n, "Either")))), n, args, rest, r, g, x)
    case _:
      fd.todo("fold:cata-at-type")

def fd.cata(t: T.Bt, r: T.Bt, g: T.Bt, x: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{h, T.BtArgs{l, rest}}:
      fd.cata.of(h, l, rest, r, g, x)
    case _:
      fd.todo("fold:cata-at-type")

# maxBound and minBound at Int: 2^48 - 1 and -(2^48 - 1). An HsInt is a
# sign and a Nat, and Bend's runtime holds a Nat up to its largest
# immediate, 2^48 - 1 (a Nat past it stops the run), so that is the Int's
# range: one Haskell 2010 allows (at least -2^29 .. 2^29 - 1), not GHC's
# 2^63 - 1, which would stop the run at once. A Nat literal is at most
# 2^32 - 1: 2^48 - 1 is (2^32 - 1) 2^16 + 2^16 - 1.
def fd.bound.big() -> T.Bt:
  fd.callS("Nat.add", [fd.callS("Nat.mul", [T.BtNat{S.b("4294967295")}, T.BtNat{S.b("65536")}]), T.BtNat{S.b("65535")}])

def fd.bound(q: Tq, hi: Bool) -> T.Bt:
  match q hi:
    case TqInt{} True{}:
      T.BtCon{S.b("HsPrelude.HsInt.Pos"), T.tba.args([fd.bound.big()])}
    case TqInt{} False{}:
      T.BtCon{S.b("HsPrelude.HsInt.Neg"), T.tba.args([fd.bound.big()])}
    case _ _:
      fd.todo("fold:bounded-at-type")

# <|>, empty, <*, <$ and fail at a parser (HsPc's)
def fd.pc.op(k: Mk, +f: String, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkPc{}:
      fd.callS("HsPrelude.HsPc." ++ f, xs)
    case _:
      fd.todo("fold:alternative-at-type")

# <|> and empty at Maybe (the first Just; the second a thunk, Haskell's
# <|> lazy in it), else at a parser
def fd.alt(k: Mk, a: T.Bt, x: T.Bt, y: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      fd.callS("hs.maybe.alt", [a, x, T.BtLam{T.BmLive{}, S.b("_"), y}])
    case +k2:
      fd.pc.op(k2, "alt", [a, x, y])

def fd.empty(k: Mk, a: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      fd.con0("None")
    case +k2:
      fd.pc.op(k2, "empty", [a])

def fd.pc.drop(n: Nat, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match n xs:
    case 1n+k h <> t:
      fd.pc.drop(k, t)
    case _ ys:
      ys

# a saturated call of one of base's functions, as Base writes it
def fd.bf.mk(f: Bf, tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  match f tys xs:
    case BfCmp{op} +t <> _ a <> b <> _:
      fd.cmp(fd.tq(t), t, op, a, b)
    case BfNum{op} t <> _ a <> b <> _:
      fd.num(fd.tq(t), op, a, b)
    case BfAnd{} _ a <> b <> _:
      fd.callS("Bool.and", [a, b])
    case BfOr{} _ a <> b <> _:
      fd.callS("Bool.or", [a, b])
    case BfNot{} _ a <> _:
      fd.callS("Bool.not", [a])
    case BfTrue{} _ _:
      fd.con0("True")
    case BfAppend{} t <> _ a <> b <> _:
      fd.callS("List.append", [fd.v("&2"), t, a, b])
    case BfLength{} +c <> +t <> _ a <> _:
      fd.foldable(c, fd.callS("List.length", [fd.v("&2"), t, fd.fl(c, t, a)]))
    case BfNull{} +c <> +t <> _ a <> _:
      fd.foldable(c, fd.callS("List.is_empty", [fd.v("&2"), t, fd.fl(c, t, a)]))
    case BfReverse{} t <> _ a <> _:
      fd.callS("List.reverse", [fd.v("&2"), t, a])
    case BfConcat{} c <> t <> _ a <> _:
      fd.foldable(c, fd.callS("List.concat", [fd.v("&2"), t, a]))
    case BfTake{} t <> _ n <> a <> _:
      fd.callS("List.take", [fd.v("&2"), t, a, n])
    case BfDrop{} t <> _ n <> a <> _:
      fd.callS("List.drop", [fd.v("&2"), t, a, n])
    case BfReplicate{} t <> _ n <> a <> _:
      fd.callS("List.replicate", [t, n, a])
    case BfMap{} a <> b <> _ g <> l <> _:
      fd.callS("hs.map", [fd.tpl0(a), fd.tpl0(b), fd.tpl(ls, g), l])
    case BfFilter{} t <> _ g <> l <> _:
      fd.callS("List.filter", [fd.tpl0(t), fd.tpl(ls, g), l])
    case BfAny{} +c <> +t <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.any", [fd.tpl0(fd.v("&2")), fd.tpl0(t), fd.tpl(ls, g), fd.fl(c, t, l)]))
    case BfAll{} +c <> +t <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.all", [fd.tpl0(fd.v("&2")), fd.tpl0(t), fd.tpl(ls, g), fd.fl(c, t, l)]))
    case BfFoldr{} +c <> +a <> b <> _ g <> z <> l <> _:
      fd.foldable(c, fd.callS("HsPrelude.HsList.foldr", [fd.tpl0(a), fd.tpl0(b), fd.tpl(ls, g), fd.fl(c, a, l), z]))
    case BfFoldl{} +c <> b <> +a <> _ g <> z <> l <> _:
      fd.foldable(c, fd.callS("HsPrelude.HsList.foldl", [fd.tpl0(a), fd.tpl0(b), fd.tpl(ls, g), fd.fl(c, a, l), z]))
    case BfElem{} +c <> +t <> _ x <> l <> _:
      fd.foldable(c, fd.elem(fd.tq(t), t, x, fd.fl(c, t, l)))
    case BfSum{} +c <> +t <> _ l <> _:
      fd.foldable(c, fd.sum(fd.tq(t), False{}, t, fd.fl(c, t, l)))
    case BfProduct{} +c <> +t <> _ l <> _:
      fd.foldable(c, fd.sum(fd.tq(t), True{}, t, fd.fl(c, t, l)))
    case BfAndL{} c <> _ l <> _:
      fd.foldable(c, fd.callS("List.all", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Bool")), fd.tpl0(T.BtLam{T.BmLive{}, S.b("b"), fd.v("b")}), l]))
    case BfOrL{} c <> _ l <> _:
      fd.foldable(c, fd.callS("List.any", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Bool")), fd.tpl0(T.BtLam{T.BmLive{}, S.b("b"), fd.v("b")}), l]))
    case BfConcatMap{} +c <> +a <> +b <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.concat", [fd.v("&2"), b, fd.callS("hs.map", [fd.tpl0(a), fd.tpl0(fd.list(b)), fd.tpl(ls, g), fd.fl(c, a, l)])]))
    case BfShow{} +t <> _ x <> _:
      fd.show.at(fd.tq(t), t, x)
    case BfId{} _ x <> _:
      x
    case BfConst{} _ a <> b <> _:
      a
    case BfSucc{} +t <> _ x <> _:
      fd.succ(fd.tq(t), x)
    case BfUnFix{} f <> _ x <> _:
      fd.callS("HsPrelude.Fix.unFix", [fd.fn.lam(f), x])
    case BfProject{} t <> _ x <> _:
      fd.project(t, x)
    case BfEmbed{} t <> _ x <> _:
      fd.embed(t, x)
    case BfCata{} t <> r <> _ g <> x <> _:
      fd.cata(t, r, fd.tpl(ls, g), x)
    case BfBind{} m <> a <> b <> _ x <> f <> _:
      fd.bind(fd.mk(m), a, b, x, f)
    case BfThen{} m <> a <> b <> _ x <> y <> _:
      fd.bind(fd.mk(m), a, b, x, T.BtLam{T.BmLive{}, S.b("_"), y})
    case BfPure{} m <> a <> _ x <> _:
      fd.pure(fd.mk(m), a, x)
    case BfFmap{} m <> a <> b <> _ g <> x <> _:
      fd.fmap.at(m, a, b, fd.tpl(ls, g), x)
    case BfMaybe{} b <> a <> _ d <> g <> m <> _:
      fd.callS("hs.maybe", [a, b, d, g, m])
    case BfFromMaybe{} a <> _ d <> m <> _:
      fd.callS("Maybe.default", [fd.v("&2"), a, m, d])
    case BfEither{} a <> c <> b <> _ f <> g <> e <> _:
      fd.callS("hs.either", [a, b, c, f, g, e])
    case BfSemi{} t <> _ x <> y <> _:
      fd.semi(t, x, y)
    case BfAp{} m <> a <> b <> _ f <> x <> _:
      fd.ap(fd.mk(m), a, b, f, x)
    case BfGet{} s <> m <> _ _:
      fd.st.get(fd.mk(m), s)
    case BfPut{} s <> m <> _ x <> _:
      fd.st.call(fd.mk(m), "put", [s, x])
    case BfModify{} s <> m <> _ g <> _:
      fd.st.call(fd.mk(m), "modify", [s, fd.untpl(g)])
    case BfGets{} s <> m <> a <> _ g <> _:
      fd.st.call(fd.mk(m), "gets", [s, a, fd.untpl(g)])
    case BfEval{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.eval", [s, a, m, x])
    case BfExec{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.exec", [s, a, m, x])
    case BfRun{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.run", [s, a, m, x])
    case BfThrow{} e <> m <> a <> _ x <> _:
      fd.throw(fd.mk(m), a, x)
    case BfRunExc{} e <> m <> a <> _ x <> _:
      fd.runexc(fd.em(m), x)
    case BfWhen{} m <> _ c <> x <> _:
      fd.when(fd.mk(m), True{}, c, x)
    case BfUnless{} m <> _ c <> x <> _:
      fd.when(fd.mk(m), False{}, c, x)
    case BfVoid{} m <> a <> _ x <> _:
      fd.fmap(fd.mk(m), a, fd.ty0("Unit"), fd.tpl0(T.BtLam{T.BmLive{}, S.b("_"), fd.con0("Unit")}), x)
    case BfBindR{} m <> a <> b <> _ f <> x <> _:
      fd.bind(fd.mk(m), a, b, x, f)
    case BfForM_{} +c <> m <> +a <> b <> _ l <> f <> _:
      fd.foldable(c, fd.mapm.at(fd.mk(m), "mapm_", a, b, [fd.tpl(ls, f), fd.fl(c, a, l)]))
    case BfMapM_{} +c <> m <> +a <> b <> _ f <> l <> _:
      fd.foldable(c, fd.mapm.at(fd.mk(m), "mapm_", a, b, [fd.tpl(ls, f), fd.fl(c, a, l)]))
    case BfFilterM{} m <> a <> _ p <> l <> _:
      fd.mlist.at(fd.mk(m), "filterm", [a], [fd.tpl(ls, p), l])
    case BfZipWithM_{} m <> a <> b <> c <> _ f <> x <> y <> _:
      fd.mlist.at(fd.mk(m), "zipwithm_", [a, b, c], [fd.tpl(ls, f), x, y])
    case BfForM{} c <> m <> a <> b <> _ l <> f <> _:
      fd.foldable(c, fd.mapm.at(fd.mk(m), "mapm", a, b, [fd.tpl(ls, f), l]))
    case BfMapM{} c <> m <> a <> b <> _ f <> l <> _:
      fd.foldable(c, fd.mapm.at(fd.mk(m), "mapm", a, b, [fd.tpl(ls, f), l]))
    case BfSeq{} c <> m <> a <> _ l <> _:
      fd.seq.list(c, fd.seq.at(fd.mk(m), a, l))
    case BfFoldM{} c <> m <> b <> a <> _ f <> z <> l <> _:
      fd.foldable(c, fd.mapm.at(fd.mk(m), "foldm", a, b, [fd.tpl(ls, f), l, z]))
    case BfDm{d, r, p, nt, n} tys xs:
      fd.dm(d, S.b(r), S.b(p), nt, tys, xs, ls)
    case BfAbsurd{} a <> _ x <> _:
      fd.callS("Empty.absurd", [a, x])
    case BfNeg{op} t <> _ x <> _:
      fd.neg(fd.tq(t), op, x)
    case BfConv{} a <> b <> _ x <> _:
      fd.conv(fd.tq(a), fd.tq(b), x)
    case BfIdAt{} t <> _ x <> _:
      fd.idat(fd.tq(t), x)
    case BfSubtract{} t <> _ a <> b <> _:
      fd.num(fd.tq(t), "sub", b, a)
    case BfLift2{} m <> a <> b <> c <> _ f <> x <> y <> _:
      fd.lift2(fd.mk(m), a, b, c, fd.untpl(f), x, y)
    case BfZ{op} tys xs:
      fd.z(S.b(op), tys, xs)
    case BfRange{} t <> _ a <> b <> _:
      fd.range(fd.tq(t), a, b)
    case BfOne{f} _ x <> _:
      fd.one(S.b(f), x)
    case BfParity{op} t <> _ x <> _:
      fd.parity(fd.tq(t), op, x)
    case BfDmF{d, r, p, nt, n} tys xs:
      fd.dmf(d, S.b(r), S.b(p), nt, tys, xs, ls)
    case BfBi{op} tys xs:
      fd.bi(S.b(op), tys, xs, ls)
    case BfFlip{} _ f <> x <> y <> _:
      T.tba.call(T.tba.call(f, [y]), [x])
    case BfTrace{} _ a <> b <> _:
      b
    case BfMempty{} t <> _ _:
      fd.mempty(t)
    case BfMconcat{} t <> _ xs <> _:
      fd.mconcat(t, xs)
    case BfShowsPrec{} t <> _ d <> x <> r <> _:
      fd.sp(t, d, x, r)
    case BfShows{} t <> _ x <> r <> _:
      fd.sp(t, fd.sp.zero(), x, r)
    case BfAlt{} m <> a <> _ x <> y <> _:
      fd.alt(fd.mk(m), a, x, y)
    case BfEmpty{} m <> a <> _ _:
      fd.empty(fd.mk(m), a)
    case BfLeft{} m <> a <> b <> _ x <> y <> _:
      fd.pc.op(fd.mk(m), "left", [a, b, x, y])
    case BfConstL{} m <> a <> b <> _ x <> y <> _:
      fd.pc.op(fd.mk(m), "const", [a, b, x, y])
    case BfFail{} m <> a <> _ x <> _:
      fd.pc.op(fd.mk(m), "fail", [a, x])
    case BfPc{f, d, n} tys xs:
      fd.callS("HsPrelude." ++ f, List.append(&2, T.Bt, fd.pc.drop(d, tys), xs))
    case BfAsk{} r <> m <> _ _:
      fd.rd.call(fd.mk(m), "ask", Nil{})
    case BfLocal{} r <> m <> a <> _ f <> x <> _:
      fd.rd.call(fd.mk(m), "local", [a, fd.untpl(f), x])
    case BfLocalT{} +r <> m <> a <> _ f <> x <> _:
      fd.rd.call(fd.mk(fd.ty.readert([r, m])), "local", [a, fd.untpl(f), x])
    case BfAsks{} r <> m <> a <> _ f <> _:
      fd.rd.call(fd.mk(m), "asks", [a, fd.untpl(f)])
    case BfLift{} t <> m <> a <> _ x <> _:
      fd.lift(t, m, a, x)
    case BfWriter{} m <> a <> w <> _ x <> _:
      fd.pure(fd.mk(m), fd.pair(a, w), x)
    case BfBound{hi} t <> _ _:
      fd.bound(fd.tq(t), hi)
    case _ _ _:
      fd.todo("fold:base-call")

# Expressions ------------------------------------------------------------------

# the head of an application: a finished term, a local, the binding's own
# recursive call, a global, or one of base's combinators the fold
# reassociates ($ and leftSection, ., rightSection)
type Hd is Data:
  HdT{t: T.Bt}
  HdL{x: List<&2, U32>}
  HdSelf{n: List<&2, U32>}
  HdG{m: List<&2, U32>, n: List<&2, U32>, k: List<&2, U32>}
  HdDollar{}
  HdDot{}
  HdRsec{}

# an expression: an application spine (a head, its type arguments, its
# arguments as an EArgs spine), not yet written
type E is Data:
  ESp{h: Hd, tys: List<&2, T.Bt>, args: E}
  EArgs{a: E, rest: E}
  ENil{}

def fd.hd.of(+key: List<&2, U32>, m: List<&2, U32>, n: List<&2, U32>, k: List<&2, U32>) -> Hd:
  Bool.pick(Hd, Bool.or(fd.is(key, "GHC.Internal.Base.$"), fd.is(key, "GHC.Prim.leftSection")), HdDollar{}, Bool.pick(Hd, fd.is(key, "GHC.Internal.Base.."), HdDot{}, Bool.pick(Hd, fd.is(key, "GHC.Prim.rightSection"), HdRsec{}, HdG{m, n, k})))

def fd.hd(+m: List<&2, U32>, +n: List<&2, U32>, k: List<&2, U32>) -> Hd:
  fd.hd.of(fd.cat3(m, S.b("."), n), m, n, k)

def fd.e0(h: Hd) -> E:
  ESp{h, Nil{}, ENil{}}

def fd.et(t: T.Bt) -> E:
  ESp{HdT{t}, Nil{}, ENil{}}

# a spine with one more argument at its end
def fd.snoc(args: E, a: E) -> E:
  match args:
    case EArgs{h, rest}:
      EArgs{h, fd.snoc(rest, a)}
    case _:
      EArgs{a, ENil{}}

def fd.ext(f: E, a: E) -> E:
  match f:
    case ESp{h, tys, args}:
      ESp{h, tys, fd.snoc(args, a)}
    case _:
      fd.et(fd.todo("fold:application"))

# f applied to a: `$` and `.` and the right section reassociated, so
# f $ x, (f . g) x and (`op` y) x are the calls f(x), f(g(x)), op(x, y)
def fd.eapp(f: E, a: E) -> E:
  match f:
    case ESp{HdDollar{}, tys, EArgs{g, ENil{}}}:
      fd.ext(g, a)
    case ESp{HdDot{}, tys, EArgs{g, EArgs{h, ENil{}}}}:
      fd.ext(g, fd.ext(h, a))
    case ESp{HdRsec{}, tys, EArgs{op, EArgs{y, ENil{}}}}:
      fd.ext(fd.ext(op, a), y)
    case g:
      fd.ext(g, a)

def fd.etyapp(f: E, t: T.Bt) -> E:
  match f:
    case ESp{h, tys, args}:
      ESp{h, List.append(&2, T.Bt, tys, t <> Nil{}), args}
    case g:
      g

# a constructor of the module
def fd.ucon(m: Maybe<&2, Ctr>, +all: List<&2, T.Bt>) -> T.Bt:
  match m:
    case Some{Ctr{+c, +t, +n, fs}}:
      fd.sat(n, all, xs => T.BtCon{fd.cname(t, c), T.tba.args(xs)})
    case None{}:
      fd.todo("fold:unknown-constructor")

# a def of the module: its type arguments, then its arguments
def fd.own(a: Maybe<&2, Nat>, +name: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>) -> T.Bt:
  match a:
    case None{}:
      T.tba.call(T.BtVar{name}, List.append(&2, T.Bt, tys, all))
    case Some{+k}:
      fd.sat(k, all, xs => T.tba.call(T.BtVar{name}, List.append(&2, T.Bt, tys, xs)))

# a field's selector: the module's def of that name (see Selectors), one
# argument after the type's
def fd.own.sel(sel: Bool, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>) -> T.Bt:
  match sel:
    case True{}:
      fd.own(Some{1n}, fd.vname(n), tys, all)
    case False{}:
      T.BtTodo{fd.cat(S.b("fold:"), k)}

def fd.own.g(var: Bool, con: Bool, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match var con:
    case True{} _:
      fd.own(fd.df.find(fd.env.defs(env), n), fd.vname(n), tys, all)
    case False{} True{}:
      fd.ucon(fd.ctr.find(fd.env.cons(env), n), all)
    case False{} False{}:
      fd.own.sel(fd.is(k, "sel"), n, k, tys, all)

def fd.bcon(c: Cb, +key: List<&2, U32>, +all: List<&2, T.Bt>) -> T.Bt:
  match c:
    case CbNone{}:
      T.BtTodo{fd.cat(S.b("base:"), key)}
    case +c1:
      fd.sat(fd.cb.n(c1), all, xs => fd.cb.mk(c1, xs))

def fd.bfun(f: Bf, +key: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  match f:
    case BfNone{}:
      T.BtTodo{fd.cat(S.b("base:"), key)}
    case +f1:
      fd.sat(fd.bf.n(f1), all, xs => fd.bf.mk(f1, tys, xs, ls))

# Coercible's coerce (GHC.Prim.coerce): at function types the argument
# coerced back and the answer forth (flip: from b to a), at a newtype its
# constructor (from its field's type) or its selector (to it), at one type
# the term itself; else out (fold:coerce-at-type). A newtype's derived
# instance (GeneralizedNewtypeDeriving) is coerce of its field type's.
type Nt is Data:
  Nt{c: List<&2, U32>, s: List<&2, U32>}

def fd.nt.mk(+c: List<&2, U32>, +pre: List<&2, U32>, fs: List<&2, List<&2, U32>>) -> Maybe<&2, Nt>:
  match fs:
    case f <> Nil{}:
      Some{Nt{c, fd.cat(pre, f)}}
    case _:
      Some{Nt{c, Nil{}}}

def fd.nt.own(cs: List<&2, Ctr>, +n: List<&2, U32>) -> Maybe<&2, Nt>:
  match cs:
    case Ctr{+c, +t, +k, fs} <> rest:
      Bool.pick(Maybe<&2, Nt>, Bool.and(S.eq(t, n), Nat.is_eq(k, 1n)), fd.nt.mk(fd.cat3(n, S.b("."), c), Nil{}, fs), fd.nt.own(rest, n))
    case Nil{}:
      None{}

def fd.nt.ix1(h: Ix, +b: List<&2, U32>, +pre: List<&2, U32>) -> Maybe<&2, Nt>:
  match h:
    case IxCon{k, +cb, +a, fs}:
      Bool.pick(Maybe<&2, Nt>, Bool.and(S.eq(cb, b), Nat.is_eq(a, 1n)), fd.nt.mk(cb, pre, fs), None{})
    case _:
      None{}

def fd.nt.imp(xs: List<&2, Ix>, +b: List<&2, U32>, +pre: List<&2, U32>) -> Maybe<&2, Nt>:
  match xs:
    case h <> t:
      Maybe.or(&2, Nt, fd.nt.ix1(h, b, pre), fd.nt.imp(t, b, pre))
    case Nil{}:
      None{}

# a newtype's constructor and selector, its Bend name n (of the module, or
# M.T of an earlier one, its constructor M.T.T)
def fd.nt(+n: List<&2, U32>, +env: Env) -> Maybe<&2, Nt>:
  +l = Maybe.default(&2, List<&2, U32>, List.last(&2, List<&2, U32>, S.split(n, 46)), n)
  +pre = List.take(&2, U32, n, Nat.sub(List.length(&2, U32, n), List.length(&2, U32, l)))
  Maybe.or(&2, Nt, fd.nt.own(fd.env.cons(env), n), fd.nt.imp(fd.env.ix(env), fd.cat3(n, S.b("."), l), pre))

def fd.co.name(t: T.Bt) -> List<&2, U32>:
  match t:
    case T.BtTyApp{n, a}:
      n
    case _:
      Nil{}

def fd.co.txt(t: T.Bt) -> List<&2, U32>:
  P.tpr.t(t, P.TpLoose{}, 0n, Nil{})

def fd.co.unwrap(m: Maybe<&2, Nt>, +x: T.Bt) -> T.Bt:
  match m:
    case Some{Nt{c, +s}}:
      Bool.pick(T.Bt, S.eq(s, Nil{}), fd.todo("fold:coerce-at-type"), T.tba.call(T.BtVar{s}, [x]))
    case None{}:
      fd.todo("fold:coerce-at-type")

def fd.co.wrap(m: Maybe<&2, Nt>, +s: T.Bt, +x: T.Bt, +env: Env) -> T.Bt:
  match m:
    case Some{Nt{c, sel}}:
      T.BtCon{c, T.tba.args([x])}
    case None{}:
      fd.co.unwrap(fd.nt(fd.co.name(s), env), x)

def fd.co.base(same: Bool, +s: T.Bt, +t: T.Bt, +x: T.Bt, +env: Env) -> T.Bt:
  match same:
    case True{}:
      x
    case False{}:
      fd.co.wrap(fd.nt(fd.co.name(t), env), s, x, env)

def fd.co(a: T.Bt, +b: T.Bt, +flip: Bool, +x: T.Bt, +d: Nat, +env: Env) -> T.Bt:
  match a b:
    case T.BtPi{m1, x1, e1, +a1, +a2} T.BtPi{m2, x2, e2, +b1, +b2}:
      +v = fd.cat(S.b("co_"), S.b(Nat.show(d)))
      T.BtLam{T.BmLive{}, v, fd.co(a2, b2, flip, T.tba.call(x, [fd.co(a1, b1, Bool.not(flip), T.BtVar{v}, Nat.add(d, 1n), env)]), Nat.add(d, 1n), env)}
    case +s +t:
      +src = Bool.pick(T.Bt, flip, t, s)
      +dst = Bool.pick(T.Bt, flip, s, t)
      fd.co.base(S.eq(fd.co.txt(src), fd.co.txt(dst)), src, dst, x, env)

def fd.coerce.one(+a: T.Bt, +b: T.Bt, xs: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match xs:
    case x <> t:
      fd.co(a, b, False{}, x, 0n, env)
    case Nil{}:
      fd.todo("fold:coerce")

def fd.coerce.g(tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match tys:
    case r <> +a <> +b <> _:
      fd.sat(1n, all, xs => fd.coerce.one(a, b, xs, env))
    case _:
      fd.todo("fold:coerce")

def fd.bglobal(con: Bool, +key: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match con:
    case True{}:
      fd.bcon(fd.cb.find(fd.cbtab(), key), key, all)
    case False{}:
      Bool.pick(T.Bt, fd.is(key, "GHC.Prim.coerce"), fd.coerce.g(tys, all, env), fd.bfun(fd.bf.find(fd.bftab(), key), key, tys, all, fd.env.ls(env)))

# a def, selector or constructor of an earlier module of the package
def fd.imp.g(found: Maybe<&2, Ix>, +key: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>) -> T.Bt:
  match found:
    case Some{IxDef{k, +b, +a}}:
      fd.own(Some{a}, b, tys, all)
    case Some{IxCon{k, +b, +n, fs}}:
      fd.sat(n, all, xs => T.BtCon{b, T.tba.args(xs)})
    case _:
      T.BtTodo{fd.cat(S.b("import:"), key)}

def fd.hglobal(home: Bool, +key: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match home:
    case True{}:
      fd.imp.g(fd.ix.findv(fd.env.ix(env), key, False{}), key, tys, all)
    case False{}:
      fd.bglobal(fd.is(k, "con"), key, tys, all, env)

def fd.global(own: Bool, +m: List<&2, U32>, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match own:
    case True{}:
      fd.con.fn(Bool.and(fd.is(k, "con"), fd.isfn.last(tys)), fd.own.g(fd.is(k, "var"), fd.is(k, "con"), n, k, tys, all, env))
    case False{}:
      +key = fd.cat3(m, S.b("."), n)
      +home = S.mem(m, fd.env.home(env))
      fd.con.fn(Bool.and(Bool.and(fd.is(k, "con"), fd.isfn.last(tys)), Bool.or(home, fd.is(key, "Control.Comonad.Trans.Cofree.:<"))), fd.hglobal(home, key, k, tys, all, env))

# a head applied to its type arguments and arguments
def fd.head(h: Hd, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match h:
    case HdT{t}:
      fd.apply(t, all)
    case HdL{x}:
      fd.apply(T.BtVar{x}, all)
    case HdSelf{+n}:
      fd.own(fd.df.find(fd.env.defs(env), n), fd.vname(n), fd.env.self(env), all)
    case HdG{+m, +n, +k}:
      fd.global(S.eq(m, fd.env.m(env)), m, n, k, tys, all, env)
    case _:
      fd.todo("fold:section")

# an expression written: the reassociations of $, . and the right section,
# and every call saturated (more: arguments already written, after the
# spine's own)
def fd.close(e: E, more: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match e more:
    case EArgs{a, rest} _:
      T.BtArgs{fd.close(a, Nil{}, env), fd.close(rest, Nil{}, env)}
    case ENil{} _:
      T.BtANil{}
    case ESp{HdDollar{}, tys, EArgs{f, rest}} _:
      fd.close(f, List.append(&2, T.Bt, fd.spine(fd.close(rest, Nil{}, env)), more), env)
    case ESp{HdDot{}, tys, EArgs{f, EArgs{g, ENil{}}}} Nil{}:
      T.BtLam{T.BmLive{}, S.b("x_c"), fd.close(f, fd.close(g, T.BtVar{S.b("x_c")} <> Nil{}, env) <> Nil{}, env)}
    case ESp{HdDot{}, tys, EArgs{f, EArgs{g, ENil{}}}} x <> xs:
      fd.close(f, fd.close(g, x <> Nil{}, env) <> xs, env)
    case ESp{HdRsec{}, tys, EArgs{op, EArgs{y, ENil{}}}} Nil{}:
      T.BtLam{T.BmLive{}, S.b("x_c"), fd.close(op, T.BtVar{S.b("x_c")} <> fd.close(y, Nil{}, env) <> Nil{}, env)}
    case ESp{HdRsec{}, tys, EArgs{op, EArgs{y, ENil{}}}} x <> xs:
      fd.close(op, x <> fd.close(y, Nil{}, env) <> xs, env)
    # (f . g) x .., (op y) x .. in one spine (a copy's argument in place
    # of its function parameter: rule 15)
    case ESp{HdDot{}, tys, EArgs{f, EArgs{g, EArgs{x, rest}}}} _:
      fd.close(f, fd.close(g, fd.close(x, Nil{}, env) <> Nil{}, env) <> List.append(&2, T.Bt, fd.spine(fd.close(rest, Nil{}, env)), more), env)
    case ESp{HdRsec{}, tys, EArgs{op, EArgs{y, EArgs{x, rest}}}} _:
      fd.close(op, fd.close(x, Nil{}, env) <> fd.close(y, Nil{}, env) <> List.append(&2, T.Bt, fd.spine(fd.close(rest, Nil{}, env)), more), env)
    case ESp{h, tys, args} _:
      fd.head(h, tys, List.append(&2, T.Bt, fd.spine(fd.close(args, Nil{}, env)), more), env)

# Results of the fold --------------------------------------------------------

# What the fold of one form gives: an expression, a type, pattern or body,
# a list, a clause (its patterns and body), a guarded right-hand side
# (None: no guard), a local binding, or a group of clauses (the argument
# types, the result type, the clauses).
type R is Data:
  RE{e: E}
  RT{t: T.Bt}
  RL{xs: List<&2, R>}
  RC{ps: List<&2, T.Bt>, b: T.Bt}
  RG{c: Maybe<&2, T.Bt>, b: T.Bt}
  RB{x: List<&2, U32>, v: T.Bt}
  RMs{tys: List<&2, T.Bt>, res: T.Bt, cls: List<&2, R>}
  RLf{x: List<&2, U32>, tys: List<&2, T.Bt>, res: T.Bt, cls: List<&2, R>}
  RPb{p: T.Bt, v: T.Bt, ty: T.Bt}

def fd.cons(h: R, t: R) -> R:
  match t:
    case RL{xs}:
      RL{h <> xs}
    case _:
      RL{h <> Nil{}}

def fd.nil() -> R:
  RL{Nil{}}

def fd.items(r: R) -> List<&2, R>:
  match r:
    case RL{xs}:
      xs
    case _:
      Nil{}

# an abs's bindings: the one, or with the rest (an RL: a group of several,
# one item of the let's bindings, fd.lets.go's %lgrp)
def fd.abs1(h: R, t: R) -> R:
  match t:
    case RL{Nil{}}:
      h
    case t:
      fd.cons(h, t)

def fd.rt(r: R) -> T.Bt:
  match r:
    case RT{t}:
      t
    case _:
      fd.todo("fold:shape")

def fd.re(r: R) -> E:
  match r:
    case RE{e}:
      e
    case RT{t}:
      fd.et(t)
    case _:
      fd.et(fd.todo("fold:shape"))

def fd.bts(xs: List<&2, R>) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      fd.rt(h) <> fd.bts(t)

# the expression of a result, written
def fd.ex(r: R, +env: Env) -> T.Bt:
  fd.close(fd.re(r), Nil{}, env)

def fd.exs(xs: List<&2, R>, +env: Env) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      fd.ex(h, env) <> fd.exs(t, env)

def fd.bad(why: List<&2, U32>) -> R:
  RT{T.BtTodo{why}}

# a list's elements as a chain of Con (a pattern's or a term's)
def fd.conchain(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case Nil{}:
      fd.con0("Nil")
    case h <> t:
      T.BtCon{S.b("Con"), T.tba.args([h, fd.conchain(t)])}

# a tuple's elements as nested Tuple (a pattern's or a term's)
def fd.tuple(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case a <> b <> Nil{}:
      T.BtCon{S.b("Tuple"), T.tba.args([a, b])}
    case a <> b <> c <> Nil{}:
      T.BtCon{S.b("Tuple"), T.tba.args([a, T.BtCon{S.b("Tuple"), T.tba.args([b, c])}])}
    case _:
      fd.todo("fold:tuple-size")

# Patterns --------------------------------------------------------------------

# a constructor pattern: Base's or the module's
def fd.pcon.own(m: Maybe<&2, Ctr>, ps: List<&2, T.Bt>) -> T.Bt:
  match m:
    case Some{Ctr{+c, +t, n, fs}}:
      T.BtCon{fd.cname(t, c), T.tba.args(ps)}
    case None{}:
      fd.todo("fold:unknown-constructor")

def fd.pcon.base(c: Cb, +key: List<&2, U32>, ps: List<&2, T.Bt>) -> T.Bt:
  match c:
    case CbNone{}:
      T.BtTodo{fd.cat(S.b("base:"), key)}
    case c1:
      fd.cb.mk(c1, ps)

# a constructor of an earlier module of the package
def fd.pcon.imp(found: Maybe<&2, Ix>, +key: List<&2, U32>, ps: List<&2, T.Bt>) -> T.Bt:
  match found:
    case Some{IxCon{k, b, n, fs}}:
      T.BtCon{b, T.tba.args(ps)}
    case _:
      T.BtTodo{fd.cat(S.b("import:"), key)}

def fd.pcon.other(home: Bool, +key: List<&2, U32>, ps: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match home:
    case True{}:
      fd.pcon.imp(fd.ix.findv(fd.env.ix(env), key, False{}), key, ps)
    case False{}:
      fd.pcon.base(fd.cb.find(fd.cbtab(), key), key, ps)

# MOD.NAME of (g MOD NAME KIND)
def fd.gkey(+g: X.Sx) -> List<&2, U32>:
  fd.cat3(V.sv.str(g, 1n), S.b("."), V.sv.str(g, 2n))

def fd.pcon.of(own: Bool, +g: X.Sx, ps: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match own:
    case True{}:
      fd.pcon.own(fd.ctr.find(fd.env.cons(env), V.sv.str(g, 2n)), ps)
    case False{}:
      fd.pcon.other(S.mem(V.sv.str(g, 1n), fd.env.home(env)), fd.gkey(g), ps, env)

# (pcon CON (ARGTYPE...) (args P...)): CON is (g MOD NAME con)
def fd.pcon(+g: X.Sx, ps: R, +env: Env) -> R:
  RT{fd.pcon.of(S.eq(V.sv.str(g, 1n), fd.env.m(env)), g, fd.bts(fd.items(ps)), env)}

# a constructor that has a twin: the package's, or Cofree's :<
def fd.con.twin(+g: X.Sx, +env: Env) -> Bool:
  +m = V.sv.str(g, 1n)
  Bool.or(Bool.or(S.eq(m, fd.env.m(env)), S.mem(m, fd.env.home(env))), fd.is(fd.gkey(g), "Control.Comonad.Trans.Cofree.:<"))

# a constructor pattern at its twin (its last type argument a function)
def fd.pcon.fn(fn: Bool, r: R) -> R:
  match r:
    case RT{t}:
      RT{fd.con.fn(fn, t)}
    case q:
      q

# Records ---------------------------------------------------------------------

# a constructor's field names: (con NAME (FIELD...) ...), a FIELD a string
# or (g MOD NAME sel)
def fd.fnames(fs: X.Sx) -> List<&2, List<&2, U32>>:
  match fs:
    case X.SxCons{X.SxStr{f}, t}:
      f <> fd.fnames(t)
    case X.SxCons{+f, t}:
      V.sv.str(f, 2n) <> fd.fnames(t)
    case _:
      Nil{}

# where the field f is among a constructor's fields
def fd.fpos(fs: List<&2, List<&2, U32>>, +f: List<&2, U32>, +i: Nat) -> Maybe<&2, Nat>:
  match fs:
    case Nil{}:
      None{}
    case h <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(h, f), Some{i}, fd.fpos(t, f, 1n+i))

# A record's fields as the fold gives them, in the order they are written:
# each an RL of the field's name (an RT of its BtVar) and what it is set
# to or matched with.
def fd.field(+sel: X.Sx, r: R) -> R:
  RL{[RT{T.BtVar{fd.bpick(V.sv.is(V.sv.hd(sel), "g"), V.sv.str(sel, 2n), V.sv.str(sel, 1n))}}, r]}

# the one named f
def fd.field.find(xs: List<&2, R>, +f: List<&2, U32>) -> Maybe<&2, R>:
  match xs:
    case Nil{}:
      None{}
    case RL{RT{T.BtVar{n}} <> r <> Nil{}} <> t:
      Bool.pick(Maybe<&2, R>, S.eq(n, f), Some{r}, fd.field.find(t, f))
    case _ <> t:
      fd.field.find(t, f)

# a record pattern's patterns in the constructor's order; _ for a field it
# leaves out
def fd.pfield(m: Maybe<&2, R>) -> T.Bt:
  match m:
    case Some{r}:
      fd.rt(r)
    case None{}:
      T.BtWild{}

def fd.pfields(fs: List<&2, List<&2, U32>>, +xs: List<&2, R>) -> List<&2, T.Bt>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> t:
      fd.pfield(fd.field.find(xs, f)) <> fd.pfields(t, xs)

# n wildcards (a record pattern C {} at a constructor without field names)
def fd.wilds(n: Nat) -> List<&2, T.Bt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      T.BtWild{} <> fd.wilds(p)

# a record pattern's patterns: by field name, or n wildcards when the
# constructor has none (C {})
def fd.pfields.n(fs: List<&2, List<&2, U32>>, n: Nat, +xs: List<&2, R>) -> List<&2, T.Bt>:
  match fs:
    case Nil{}:
      fd.wilds(n)
    case +f <> t:
      fd.pfields(f <> t, xs)

def fd.pconf.of(own: Bool, m: Maybe<&2, Ctr>, +xs: List<&2, R>) -> T.Bt:
  match own m:
    case True{} Some{Ctr{+c, +t, n, fs}}:
      T.BtCon{fd.cname(t, c), T.tba.args(fd.pfields.n(fs, n, xs))}
    case True{} None{}:
      fd.todo("fold:unknown-constructor")
    case False{} _:
      fd.todo("fold:record-pattern-base")

def fd.pconf.imp(found: Maybe<&2, Ix>, +xs: List<&2, R>) -> T.Bt:
  match found:
    case Some{IxCon{k, b, n, fs}}:
      T.BtCon{b, T.tba.args(fd.pfields.n(fs, n, xs))}
    case _:
      fd.todo("fold:unknown-constructor")

def fd.pconf.at(own: Bool, home: Bool, +g: X.Sx, +xs: List<&2, R>, +env: Env) -> T.Bt:
  match own home:
    case True{} _:
      fd.pconf.of(True{}, fd.ctr.find(fd.env.cons(env), V.sv.str(g, 2n)), xs)
    case False{} True{}:
      fd.pconf.imp(fd.ix.findv(fd.env.ix(env), fd.gkey(g), False{}), xs)
    case False{} False{}:
      fd.todo("fold:record-pattern-base")

# (pcon CON (ARGTYPE...) (fields (pfield SEL P)...))
def fd.pconf(+g: X.Sx, r: R, +env: Env) -> R:
  RT{fd.pconf.at(S.eq(V.sv.str(g, 1n), fd.env.m(env)), S.mem(V.sv.str(g, 1n), fd.env.home(env)), g, fd.items(r), env)}

# a record built: every field the constructor has, in its order (GHC has
# already filled in a `..`); one left out is undefined in Haskell, so out
def fd.efields.of(m: Maybe<&2, R>, rest: Maybe<&2, List<&2, T.Bt>>, +env: Env) -> Maybe<&2, List<&2, T.Bt>>:
  match m rest:
    case Some{r} Some{t}:
      Some{fd.ex(r, env) <> t}
    case _ _:
      None{}

def fd.efields(fs: List<&2, List<&2, U32>>, +xs: List<&2, R>, +env: Env) -> Maybe<&2, List<&2, T.Bt>>:
  match fs:
    case Nil{}:
      Some{Nil{}}
    case +f <> t:
      fd.efields.of(fd.field.find(xs, f), fd.efields(t, xs, env), env)

def fd.reccon.mkb(+b: List<&2, U32>, m: Maybe<&2, List<&2, T.Bt>>) -> T.Bt:
  match m:
    case Some{xs}:
      T.BtCon{b, T.tba.args(xs)}
    case None{}:
      fd.todo("fold:record-missing-field")

def fd.reccon.mk(+c: List<&2, U32>, +t: List<&2, U32>, m: Maybe<&2, List<&2, T.Bt>>) -> T.Bt:
  fd.reccon.mkb(fd.cname(t, c), m)

def fd.reccon.of(own: Bool, m: Maybe<&2, Ctr>, +xs: List<&2, R>, +env: Env) -> T.Bt:
  match own m:
    case True{} Some{Ctr{+c, +t, n, fs}}:
      fd.reccon.mk(c, t, fd.efields(fs, xs, env))
    case True{} None{}:
      fd.todo("fold:unknown-constructor")
    case False{} _:
      fd.todo("fold:record-base")

def fd.reccon.imp(found: Maybe<&2, Ix>, +xs: List<&2, R>, +env: Env) -> T.Bt:
  match found:
    case Some{IxCon{k, +b, n, fs}}:
      fd.reccon.mkb(b, fd.efields(fs, xs, env))
    case _:
      fd.todo("fold:unknown-constructor")

def fd.reccon.at(own: Bool, home: Bool, +g: X.Sx, +xs: List<&2, R>, +env: Env) -> T.Bt:
  match own home:
    case True{} _:
      fd.reccon.of(True{}, fd.ctr.find(fd.env.cons(env), V.sv.str(g, 2n)), xs, env)
    case False{} True{}:
      fd.reccon.imp(fd.ix.findv(fd.env.ix(env), fd.gkey(g), False{}), xs, env)
    case False{} False{}:
      fd.todo("fold:record-base")

# (reccon CON ((field SEL E)...) nodots|dotdot)
def fd.reccon(+g: X.Sx, r: R, +env: Env) -> R:
  RE{fd.et(fd.reccon.at(S.eq(V.sv.str(g, 1n), fd.env.m(env)), S.mem(V.sv.str(g, 1n), fd.env.home(env)), g, fd.items(r), env))}

# a literal: an Int's (int N) at Nat, a character
def fd.char(+n: Nat) -> T.Bt:
  +c = U32.from_nat(n)
  Bool.pick(T.Bt, Bool.and(Bool.and(U32.is_ge(c, 32), U32.is_le(c, 126)), Bool.and(U32.is_ne(c, 39), U32.is_ne(c, 92))), T.BtVar{39 <> c <> 39 <> Nil{}}, T.BtCon{S.b("Chr"), T.tba.args([T.BtVar{S.b(U32.show(c))}])})

# the bv's local name: (bv (l NAME N) TYPE)
def fd.bvname(+bv: X.Sx) -> List<&2, U32>:
  fd.vname(V.sv.str(V.sv.at(bv, 1n), 1n))

# a bind's VAR: (l NAME N), or (self (l NAME N)) inside an abs
def fd.unself(+v: X.Sx) -> X.Sx:
  Bool.pick(X.Sx, V.sv.is(V.sv.hd(v), "self"), V.sv.at(v, 1n), v)

# an olit: (olit (int N) TYPE WITNESS), N at Nat
# an integer literal as an HsInt: (int N) is Pos{N}, (int (neg N)) Neg{N}
def fd.hsint(neg: Bool, +n: List<&2, U32>) -> T.Bt:
  T.BtCon{fd.bpick(neg, S.b("HsPrelude.HsInt.Neg"), S.b("HsPrelude.HsInt.Pos")), T.tba.args([T.BtNat{n}])}

def fd.hsint.lit(+v: X.Sx) -> T.Bt:
  +a = V.sv.at(v, 1n)
  Bool.pick(T.Bt, V.sv.is(V.sv.hd(a), "neg"), fd.hsint(True{}, X.tsx.atom.of(V.sv.at(a, 1n))), fd.hsint(False{}, X.tsx.atom.of(a)))

def fd.olit.of(q: Tq, +v: X.Sx) -> T.Bt:
  match q:
    case TqInt{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), fd.hsint.lit(v), fd.todo("fold:literal"))
    case TqNat{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtNat{X.tsx.atom.of(V.sv.at(v, 1n))}, fd.todo("fold:literal"))
    case TqF32{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtVar{fd.cat(X.tsx.atom.of(V.sv.at(v, 1n)), S.b(".0"))}, Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "frac"), T.BtVar{V.sv.str(v, 3n)}, fd.todo("fold:literal")))
    # at Rational: N / 1, or (frac NUM DEN TEXT) reduced (HsRational.mk)
    case TqRat{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtCon{S.b("HsPrelude.HsRational"), T.tba.args([fd.hsint.lit(v), T.BtNat{S.b("1")}])}, Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "frac"), fd.callS("HsPrelude.HsRational.mk", [fd.hsint.lit(v), T.BtNat{X.tsx.atom.of(V.sv.at(v, 2n))}]), fd.todo("fold:literal")))
    case _:
      fd.todo("fold:literal-type")

# the names a pattern binds
def fd.pnames(ps: List<&2, T.Bt>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> t:
      T.tba.pvars(h, fd.pnames(t))

# Clauses --------------------------------------------------------------------

def fd.cl.ps(r: R) -> List<&2, T.Bt>:
  match r:
    case RC{ps, b}:
      ps
    case _:
      Nil{}

# a pattern that takes anything (a variable or _)
def fd.isvar(p: T.Bt) -> Bool:
  match p:
    case T.BtPv{m, x}:
      True{}
    case T.BtWild{}:
      True{}
    case _:
      False{}

def fd.pvname(p: T.Bt) -> Maybe<&2, List<&2, U32>>:
  match p:
    case T.BtPv{m, x}:
      Some{x}
    case _:
      None{}

# the patterns of every clause at parameter i
def fd.col(cls: List<&2, R>, +i: Nat) -> List<&2, T.Bt>:
  match cls:
    case Nil{}:
      Nil{}
    case h <> t:
      Maybe.default(&2, T.Bt, List.get(&2, T.Bt, fd.cl.ps(h), i), T.BtWild{}) <> fd.col(t, i)

def fd.allvar(ps: List<&2, T.Bt>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(fd.isvar(h), fd.allvar(t))

def fd.names.put(m: Maybe<&2, List<&2, U32>>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match m:
    case Some{x}:
      x <> rest
    case None{}:
      rest

def fd.names(ps: List<&2, T.Bt>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> t:
      fd.names.put(fd.pvname(h), fd.names(t))

def fd.same(+x: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(S.eq(h, x), fd.same(x, t))

# A parameter: its name, and whether the match splits it (some clause has
# a constructor or a literal there, or the clauses name it differently).
type Pm is Data:
  Pm{x: List<&2, U32>, split: Bool}

def fd.pm.of(ns: List<&2, List<&2, U32>>, +var: Bool, +i: Nat) -> Pm:
  match ns:
    case +h <> t:
      Pm{h, Bool.not(Bool.and(var, fd.same(h, t)))}
    case Nil{}:
      Pm{fd.cat(S.b("x"), fd.nshow(i)), Bool.not(var)}

def fd.pm(+col: List<&2, T.Bt>, +i: Nat) -> Pm:
  fd.pm.of(fd.names(col), fd.allvar(col), i)

def fd.pms(k: Nat, +i: Nat, +cls: List<&2, R>) -> List<&2, Pm>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      fd.pm(fd.col(cls, i), i) <> fd.pms(p, 1n+i, cls)

def fd.anysplit(pms: List<&2, Pm>) -> Bool:
  match pms:
    case Nil{}:
      False{}
    case Pm{x, s} <> t:
      Bool.or(s, fd.anysplit(t))

# the patterns at the split parameters
def fd.splitps(pms: List<&2, Pm>, ps: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match pms ps:
    case Pm{x, True{}} <> t p <> q:
      p <> fd.splitps(t, q)
    case Pm{x, False{}} <> t p <> q:
      fd.splitps(t, q)
    case _ _:
      Nil{}

def fd.scruts(pms: List<&2, Pm>) -> List<&2, T.Bt>:
  match pms:
    case Pm{x, True{}} <> t:
      T.BtVar{x} <> fd.scruts(t)
    case Pm{x, False{}} <> t:
      fd.scruts(t)
    case Nil{}:
      Nil{}

def fd.cases(cls: List<&2, R>, +pms: List<&2, Pm>) -> T.Bt:
  match cls:
    case RC{ps, b} <> t:
      T.BtCase{T.tba.args(fd.splitps(pms, ps)), fd.stmt(b), fd.cases(t, pms)}
    case _ <> t:
      fd.cases(t, pms)
    case Nil{}:
      T.BtCEnd{}

def fd.first.body(cls: List<&2, R>) -> T.Bt:
  match cls:
    case RC{ps, b} <> t:
      fd.stmt(b)
    case _:
      fd.todo("fold:no-clause")

def fd.body.of(split: Bool, +pms: List<&2, Pm>, cls: List<&2, R>) -> T.Bt:
  match split:
    case True{}:
      T.BtMatch{T.tba.args(fd.scruts(pms)), fd.cases(cls, pms)}
    case False{}:
      fd.first.body(cls)

# Quantities -------------------------------------------------------------------

# how many times x is used (the most of any one case of a match)
def fd.uses(t: T.Bt, +x: List<&2, U32>) -> Nat:
  match t:
    case T.BtVar{y}:
      Bool.pick(Nat, S.eq(y, x), 1n, 0n)
    case T.BtApp{f, a}:
      Nat.add(fd.uses(f, x), fd.uses(a, x))
    case T.BtArgs{a, rest}:
      Nat.add(fd.uses(a, x), fd.uses(rest, x))
    case T.BtTplArg{a}:
      fd.uses(a, x)
    case T.BtLam{m, y, b}:
      Bool.pick(Nat, S.eq(y, x), 0n, fd.uses(b, x))
    case T.BtCon{c, a}:
      fd.uses(a, x)
    case T.BtMatch{xs, cs}:
      Nat.add(fd.uses(xs, x), fd.uses(cs, x))
    case T.BtCase{p, b, rest}:
      Nat.max(Bool.pick(Nat, S.mem(x, T.tba.pvars(p, Nil{})), 0n, fd.uses(b, x)), fd.uses(rest, x))
    case T.BtLet{y, v, b}:
      Nat.add(fd.uses(v, x), Bool.pick(Nat, S.eq(y, x), 0n, fd.uses(b, x)))
    case T.BtExpr{e}:
      fd.uses(e, x)
    case T.BtAnn{a, ty}:
      fd.uses(a, x)
    case T.BtSucc{a}:
      fd.uses(a, x)
    case _:
      0n

def fd.mode(n: Nat) -> T.BMode:
  Bool.pick(T.BMode, Nat.is_gt(n, 1n), T.BmCopy{}, T.BmLive{})

# a pattern's variables marked + where the body b uses them twice
def fd.markp(p: T.Bt, +b: T.Bt) -> T.Bt:
  match p:
    case T.BtPv{m, +x}:
      T.BtPv{fd.mode(fd.uses(b, x)), x}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.markp(a, b)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.markp(a, b), fd.markp(rest, b)}
    case q:
      q

def fd.letname(+x: List<&2, U32>, n: Nat) -> List<&2, U32>:
  fd.bpick(Nat.is_gt(n, 1n), 43 <> x, x)

# every binder in a body marked + where it is used twice
def fd.mark(t: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{f, a}:
      T.BtApp{fd.mark(f), fd.mark(a)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.mark(a), fd.mark(rest)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.mark(a)}
    case T.BtLam{m, +y, +b}:
      T.BtLam{fd.mode(fd.uses(b, y)), y, fd.mark(b)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.mark(a)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.mark(cs)}
    case T.BtCase{p, +b, rest}:
      T.BtCase{fd.markp(p, b), fd.mark(b), fd.mark(rest)}
    case T.BtLet{+y, v, +b}:
      T.BtLet{fd.letname(y, fd.uses(b, y)), fd.mark(v), fd.mark(b)}
    case T.BtExpr{e}:
      T.BtExpr{fd.mark(e)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.mark(a), ty}
    case T.BtSucc{a}:
      T.BtSucc{fd.mark(a)}
    case u:
      u

# Defs ------------------------------------------------------------------------

def fd.tvparams(tvs: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match tvs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BParam{T.BmErased{}, h, fd.v("Data")} <> fd.tvparams(t)

def fd.params(pms: List<&2, Pm>, tys: List<&2, T.Bt>, +body: T.Bt) -> List<&2, T.BParam>:
  match pms tys:
    case Pm{+x, s} <> t ty <> u:
      T.BParam{fd.mode(fd.uses(body, x)), x, ty} <> fd.params(t, u, body)
    case _ _:
      Nil{}

def fd.tvbts(tvs: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match tvs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtVar{h} <> fd.tvbts(t)

# Lifting ----------------------------------------------------------------------
#
# Bend matches only parameters, and a lambda holds one expression, so a
# case on a computed value, a case in an argument, and a lambda whose body
# is a let or a match (or whose patterns are not all variables) become a
# def of their own.  Its parameters are the enclosing def's type
# variables, the locals its body uses (each with the type its binder has
# in GHC's tree, Env's lt) and the clauses' own; its result type is the
# clauses'.  The fold writes a marker in the term,
#
#   %lift(OWN, RES, BODY, ARGS, LTS, TVS)
#
# OWN its own parameters, a spine of {x : T}, RES the result type, BODY the
# new def's body, ARGS what the call passes for OWN, LTS the locals in
# scope with their types, TVS the type variables; then fd.def.of takes each
# marker out as a def NAME.lK (its parameters: TVS, the locals of LTS its
# body uses, OWN) and puts the call in its place.  A lambda becomes x0 => .. => NAME.lK(.., x0, ..), a case
# NAME.lK(.., e).  A body that calls the def it came from makes the two
# mutually recursive, which Bend refuses: the gate then takes both out.

def fd.lt1(+x: List<&2, U32>, r: R) -> R:
  RL{RB{x, fd.rt(r)} <> Nil{}}

def fd.lt.cat(a: R, b: R) -> R:
  RL{List.append(&2, R, fd.items(a), fd.items(b))}

def fd.lts.go(xs: List<&2, R>) -> List<&2, Lt>:
  match xs:
    case RB{x, t} <> r:
      Lt{x, t} <> fd.lts.go(r)
    case _ <> r:
      fd.lts.go(r)
    case Nil{}:
      Nil{}

def fd.lts.of(r: R) -> List<&2, Lt>:
  fd.lts.go(fd.items(r))

def fd.lts.spine(xs: List<&2, Lt>) -> T.Bt:
  match xs:
    case Lt{x, t} <> r:
      T.BtArgs{T.BtAnn{T.BtVar{x}, t}, fd.lts.spine(r)}
    case Nil{}:
      T.BtANil{}

def fd.lift.tvs(tvs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match tvs:
    case T.BtVar{x} <> t:
      T.BtAnn{T.BtPv{T.BmErased{}, x}, fd.v("Data")} <> fd.lift.tvs(t)
    case _ <> t:
      fd.lift.tvs(t)
    case Nil{}:
      Nil{}

def fd.lift.lts(xs: List<&2, Lt>) -> List<&2, T.Bt>:
  match xs:
    case Lt{x, t} <> r:
      T.BtAnn{T.BtPv{T.BmLive{}, x}, t} <> fd.lift.lts(r)
    case Nil{}:
      Nil{}

def fd.lt.vars(xs: List<&2, Lt>) -> List<&2, T.Bt>:
  match xs:
    case Lt{x, t} <> r:
      T.BtVar{x} <> fd.lt.vars(r)
    case Nil{}:
      Nil{}

def fd.lt.zip(xs: List<&2, List<&2, U32>>, ts: List<&2, T.Bt>) -> List<&2, Lt>:
  match xs ts:
    case x <> r t <> u:
      Lt{x, t} <> fd.lt.zip(r, u)
    case _ _:
      Nil{}

def fd.pm.names(pms: List<&2, Pm>) -> List<&2, List<&2, U32>>:
  match pms:
    case Pm{x, s} <> t:
      x <> fd.pm.names(t)
    case Nil{}:
      Nil{}

def fd.vars(xs: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match xs:
    case x <> t:
      T.BtVar{x} <> fd.vars(t)
    case Nil{}:
      Nil{}

def fd.lams(xs: List<&2, List<&2, U32>>, b: T.Bt) -> T.Bt:
  match xs:
    case x <> t:
      T.BtLam{T.BmLive{}, x, fd.lams(t, b)}
    case Nil{}:
      b

# the variables the matches of a body scrutinize (tba.frees reads a
# match's cases only)
def fd.scrs(t: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtMatch{xs, cs}:
      T.tba.refs(xs, fd.scrs(cs, acc))
    case T.BtCase{p, b, rest}:
      fd.scrs(b, fd.scrs(rest, acc))
    case T.BtLet{x, v, b}:
      fd.scrs(b, acc)
    case _:
      acc

# the locals a body uses, each once, with their types (a name no local in
# scope has is a global's); own: the new def's own parameters
def fd.fvs.put(found: Maybe<&2, T.Bt>, x: List<&2, U32>, rest: List<&2, Lt>) -> List<&2, Lt>:
  match found:
    case Some{t}:
      Lt{x, t} <> rest
    case None{}:
      rest

def fd.fvs.go(xs: List<&2, List<&2, U32>>, +lts: List<&2, Lt>, +own: List<&2, List<&2, U32>>) -> List<&2, Lt>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      fd.fvs.put(Bool.pick(Maybe<&2, T.Bt>, S.mem(x, own), None{}, fd.lt.find(lts, x)), x, fd.fvs.go(t, lts, own))

def fd.fvs(+body: T.Bt, +lts: List<&2, Lt>, +own: List<&2, List<&2, U32>>) -> List<&2, Lt>:
  fd.fvs.go(T.tba.nub(T.tba.frees(body, fd.scrs(body, Nil{}))), lts, own)

def fd.lift.args(lam: Bool, +own: List<&2, List<&2, U32>>, e: T.Bt) -> List<&2, T.Bt>:
  match lam:
    case True{}:
      fd.vars(own)
    case False{}:
      e <> Nil{}

def fd.lift.wrap(lam: Bool, +own: List<&2, List<&2, U32>>, t: T.Bt) -> T.Bt:
  match lam:
    case True{}:
      fd.lams(own, t)
    case False{}:
      t

# clauses (a lambda's, or a case's: one parameter) as a lifted def, as
# fd.def.of makes a def of a binding's; lam: a lambda (its parameters are
# the call's), else a case on e
def fd.lift.of(+lam: Bool, +tys: List<&2, T.Bt>, +res: T.Bt, +cls: List<&2, R>, +env: Env, e: T.Bt) -> T.Bt:
  +pms = fd.pms(List.length(&2, T.Bt, tys), 0n, cls)
  +own = fd.pm.names(pms)
  fd.lift.wrap(lam, own, fd.callS("%lift", [T.tba.args(fd.lift.lts(fd.lt.zip(own, tys))), res, fd.body.of(fd.anysplit(pms), pms, cls), T.tba.args(fd.lift.args(lam, own, e)), fd.lts.spine(fd.env.lt(env)), T.tba.args(fd.env.self(env))]))

# a body is a statement (a match, a let)
def fd.isexpr(t: T.Bt) -> Bool:
  match t:
    case T.BtMatch{xs, cs}:
      False{}
    case T.BtLet{x, v, b}:
      False{}
    case T.BtRw{e, p, b}:
      False{}
    case _:
      True{}

# a lambda that stays one: a clause of variables and an expression
def fd.lam.flat(cls: List<&2, R>) -> Bool:
  match cls:
    case RC{ps, b} <> Nil{}:
      Bool.and(fd.allvar(ps), fd.isexpr(b))
    case _:
      False{}

# Taking the markers out (see Lifting): a %lift becomes a def NAME.lK, K
# counting the markers in the order they close (one inside another's body
# or arguments first), a %ldef the def NAME.x.  A lifted def's parameters
# are counted here, from its body once its own markers are out and the
# local functions it uses are calls of their defs (whose arguments then
# count): the enclosing def's type variables, the locals in LTS its body
# uses, its own.  A walk is told by its caller what the term is (Bend
# allows no mutual recursion); ctx: the local functions in scope.
type Lf is Data:
  Lf{x: List<&2, U32>, h: List<&2, U32>, ex: List<&2, T.Bt>, k: Nat}

type Lq is Data:
  LqMark{}
  LqDef{}
  LqGrp{}
  LqApp{f: Lf}
  LqVar{f: Lf}
  LqNo{}

def fd.lf.find(ctx: List<&2, Lf>, +x: List<&2, U32>) -> Maybe<&2, Lf>:
  match ctx:
    case Lf{+y, h, ex, k} <> t:
      Bool.pick(Maybe<&2, Lf>, S.eq(y, x), Some{Lf{y, h, ex, k}}, fd.lf.find(t, x))
    case Nil{}:
      None{}

def fd.lq.app(mark: Bool, f: Maybe<&2, Lf>) -> Lq:
  match mark f:
    case True{} _:
      LqMark{}
    case False{} Some{g}:
      LqApp{g}
    case False{} None{}:
      LqNo{}

def fd.lq.var(f: Maybe<&2, Lf>) -> Lq:
  match f:
    case Some{g}:
      LqVar{g}
    case None{}:
      LqNo{}

def fd.lq(+t: T.Bt, +ctx: List<&2, Lf>) -> Lq:
  match t:
    case T.BtApp{T.BtVar{+x}, a}:
      fd.lq.app(fd.is(x, "%lift"), fd.lf.find(ctx, x))
    case T.BtLet{y, T.BtApp{T.BtVar{+x}, a}, b}:
      Bool.pick(Lq, fd.is(x, "%ldef"), LqDef{}, Bool.pick(Lq, fd.is(x, "%lgrp"), LqGrp{}, LqNo{}))
    case T.BtVar{+x}:
      fd.lq.var(fd.lf.find(ctx, x))
    case _:
      LqNo{}

def fd.lq0(+t: T.Bt) -> Lq:
  fd.lq(t, Nil{})

# how many %lift markers a term holds
def fd.lift.n(t: T.Bt, q: Lq) -> Nat:
  match t q:
    case T.BtApp{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{+b, T.BtArgs{+a, _}}}}} LqMark{}:
      1n+Nat.add(fd.lift.n(b, fd.lq0(b)), fd.lift.n(a, fd.lq0(a)))
    case T.BtLet{_, T.BtApp{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{+body, _}}}}, +b} LqDef{}:
      Nat.add(fd.lift.n(body, fd.lq0(body)), fd.lift.n(b, fd.lq0(b)))
    case T.BtApp{+f, +a} _:
      Nat.add(fd.lift.n(f, fd.lq0(f)), fd.lift.n(a, fd.lq0(a)))
    case T.BtArgs{+a, +r} _:
      Nat.add(fd.lift.n(a, fd.lq0(a)), fd.lift.n(r, fd.lq0(r)))
    case T.BtTplArg{+a} _:
      fd.lift.n(a, fd.lq0(a))
    case T.BtLam{m, x, +b} _:
      fd.lift.n(b, fd.lq0(b))
    case T.BtCon{c, +a} _:
      fd.lift.n(a, fd.lq0(a))
    case T.BtMatch{xs, +cs} _:
      fd.lift.n(cs, fd.lq0(cs))
    case T.BtCase{p, +b, +r} _:
      Nat.add(fd.lift.n(b, fd.lq0(b)), fd.lift.n(r, fd.lq0(r)))
    case T.BtLet{x, +v, +b} _:
      Nat.add(fd.lift.n(v, fd.lq0(v)), fd.lift.n(b, fd.lq0(b)))
    case T.BtExpr{+e} _:
      fd.lift.n(e, fd.lq0(e))
    case T.BtAnn{+a, ty} _:
      fd.lift.n(a, fd.lq0(a))
    case T.BtSucc{+a} _:
      fd.lift.n(a, fd.lq0(a))
    case T.BtDead{+a} _:
      fd.lift.n(a, fd.lq0(a))
    case _ _:
      0n

def fd.lift.name(+name: List<&2, U32>, k: Nat) -> List<&2, U32>:
  fd.cat(name, fd.cat(S.b(".l"), fd.nshow(1n+k)))

def fd.ldef.name(+name: List<&2, U32>, +x: List<&2, U32>) -> List<&2, U32>:
  fd.cat3(name, S.b("."), x)

# the own parameters' names, a spine of {x : T}; a spine of {x : T} as locals
def fd.ps.names(ps: T.Bt) -> List<&2, List<&2, U32>>:
  match ps:
    case T.BtArgs{T.BtAnn{T.BtPv{m, x}, ty}, r}:
      x <> fd.ps.names(r)
    case _:
      Nil{}

def fd.lts.un(s: T.Bt) -> List<&2, Lt>:
  match s:
    case T.BtArgs{T.BtAnn{T.BtVar{x}, t}, r}:
      Lt{x, t} <> fd.lts.un(r)
    case _:
      Nil{}

def fd.lf.call(+h: List<&2, U32>, ys: List<&2, T.Bt>) -> T.Bt:
  T.BtApp{T.BtVar{h}, T.tba.args(ys)}

# A group of mutually recursive locals, %lgrp(M1, .., Mk) with each Mi an
# %ldef (fd.lets.go): each member a def as one alone is, every member in
# scope of every body, all taking the group's locals (the union of the ones
# their bodies use), so a member's call of another is a call of its def
def fd.gm.own(ms: T.Bt) -> List<&2, List<&2, U32>>:
  match ms:
    case T.BtArgs{T.BtApp{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{T.BtVar{x}, _}}}}}, r}:
      x <> fd.gm.own(r)
    case T.BtArgs{_, r}:
      fd.gm.own(r)
    case _:
      Nil{}

def fd.gm.in(m: Maybe<&2, T.Bt>) -> Bool:
  match m:
    case Some{t}:
      True{}
    case None{}:
      False{}

def fd.gm.put(found: Bool, h: Lt, acc: List<&2, Lt>) -> List<&2, Lt>:
  match found:
    case True{}:
      acc
    case False{}:
      List.append(&2, Lt, acc, h <> Nil{})

# acc and the locals of xs it lacks, in order
def fd.gm.add(xs: List<&2, Lt>, +acc: List<&2, Lt>) -> List<&2, Lt>:
  match xs:
    case Lt{+y, t} <> r:
      fd.gm.add(r, fd.gm.put(fd.gm.in(fd.lt.find(acc, y)), Lt{y, t}, acc))
    case Nil{}:
      acc

# the locals the members' bodies use (ms: their markers, the bodies'
# own markers out), not the members nor a member's parameters
def fd.gm.fvs(ms: T.Bt, +own: List<&2, List<&2, U32>>, acc: List<&2, Lt>) -> List<&2, Lt>:
  match ms:
    case T.BtArgs{T.BtApp{_, T.BtArgs{ps, T.BtArgs{_, T.BtArgs{body, T.BtArgs{_, T.BtArgs{_, T.BtArgs{lts, _}}}}}}}, r}:
      fd.gm.fvs(r, own, fd.gm.add(fd.fvs(body, fd.lts.un(lts), List.append(&2, List<&2, U32>, own, fd.ps.names(ps))), acc))
    case T.BtArgs{_, r}:
      fd.gm.fvs(r, own, acc)
    case _:
      acc

# ctx with each member: its def, the type variables and the group's locals
# first
def fd.gm.ctx(ms: T.Bt, +name: List<&2, U32>, +fv: List<&2, Lt>, ctx: List<&2, Lf>) -> List<&2, Lf>:
  match ms:
    case T.BtArgs{T.BtApp{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{T.BtVar{+x}, T.BtArgs{ar, T.BtArgs{_, T.BtArgs{tvs, _}}}}}}}}, r}:
      Lf{x, fd.ldef.name(name, x), List.append(&2, T.Bt, fd.spine(tvs), fd.lt.vars(fv)), T.tba.args.len(ar)} <> fd.gm.ctx(r, name, fv, ctx)
    case T.BtArgs{_, r}:
      fd.gm.ctx(r, name, fv, ctx)
    case _:
      ctx

# the term with each marker (the first numbered n) a call of its def
def fd.lift.calls(t: T.Bt, q: Lq, +name: List<&2, U32>, +n: Nat, +ctx: List<&2, Lf>) -> T.Bt:
  match t q:
    case T.BtApp{_, T.BtArgs{+ps, T.BtArgs{res, T.BtArgs{+body, T.BtArgs{+oa, T.BtArgs{+lts, T.BtArgs{+tvs, _}}}}}}} LqMark{}:
      +nb = fd.lift.n(body, fd.lq0(body))
      +fv = fd.fvs(fd.lift.calls(body, fd.lq(body, ctx), name, n, ctx), fd.lts.un(lts), fd.ps.names(ps))
      fd.lf.call(fd.lift.name(name, Nat.add(n, Nat.add(nb, fd.lift.n(oa, fd.lq0(oa))))), List.concat(&2, T.Bt, [fd.spine(tvs), fd.lt.vars(fv), fd.spine(fd.lift.calls(oa, fd.lq(oa, ctx), name, Nat.add(n, nb), ctx))]))
    case T.BtLet{_, T.BtApp{_, T.BtArgs{+ps, T.BtArgs{res, T.BtArgs{+body, T.BtArgs{T.BtVar{+x}, T.BtArgs{+ar, T.BtArgs{+lts, T.BtArgs{+tvs, _}}}}}}}}, b} LqDef{}:
      +fv = fd.fvs(fd.lift.calls(body, fd.lq(body, ctx), name, n, ctx), fd.lts.un(lts), x <> fd.ps.names(ps))
      +ctx2 = {Lf{x, fd.ldef.name(name, x), List.append(&2, T.Bt, fd.spine(tvs), fd.lt.vars(fv)), T.tba.args.len(ar)} <> ctx : List<&2, Lf>}
      fd.lift.calls(b, fd.lq(b, ctx2), name, Nat.add(n, fd.lift.n(body, fd.lq0(body))), ctx2)
    case T.BtLet{_, T.BtApp{_, +ms}, +b} LqGrp{}:
      +fv = fd.gm.fvs(fd.lift.calls(ms, fd.lq(ms, ctx), name, n, ctx), fd.gm.own(ms), Nil{})
      +ctx2 = fd.gm.ctx(ms, name, fv, ctx)
      fd.lift.calls(b, fd.lq(b, ctx2), name, Nat.add(n, fd.lift.n(ms, fd.lq0(ms))), ctx2)
    case T.BtApp{f, +a} LqApp{Lf{x, +h, +ex, k}}:
      fd.sat(Nat.add(List.length(&2, T.Bt, ex), k), List.append(&2, T.Bt, ex, fd.spine(fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx))), ys => fd.lf.call(h, ys))
    case _ LqVar{Lf{x, +h, +ex, k}}:
      fd.sat(Nat.add(List.length(&2, T.Bt, ex), k), ex, ys => fd.lf.call(h, ys))
    case T.BtApp{+f, +a} _:
      T.BtApp{fd.lift.calls(f, fd.lq(f, ctx), name, n, ctx), fd.lift.calls(a, fd.lq(a, ctx), name, Nat.add(n, fd.lift.n(f, fd.lq0(f))), ctx)}
    case T.BtArgs{+a, +r} _:
      T.BtArgs{fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx), fd.lift.calls(r, fd.lq(r, ctx), name, Nat.add(n, fd.lift.n(a, fd.lq0(a))), ctx)}
    case T.BtTplArg{+a} _:
      T.BtTplArg{fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx)}
    case T.BtLam{m, x, +b} _:
      T.BtLam{m, x, fd.lift.calls(b, fd.lq(b, ctx), name, n, ctx)}
    case T.BtCon{c, +a} _:
      T.BtCon{c, fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx)}
    case T.BtMatch{xs, +cs} _:
      T.BtMatch{xs, fd.lift.calls(cs, fd.lq(cs, ctx), name, n, ctx)}
    case T.BtCase{p, +b, +r} _:
      T.BtCase{p, fd.lift.calls(b, fd.lq(b, ctx), name, n, ctx), fd.lift.calls(r, fd.lq(r, ctx), name, Nat.add(n, fd.lift.n(b, fd.lq0(b))), ctx)}
    case T.BtLet{x, +v, +b} _:
      T.BtLet{x, fd.lift.calls(v, fd.lq(v, ctx), name, n, ctx), fd.lift.calls(b, fd.lq(b, ctx), name, Nat.add(n, fd.lift.n(v, fd.lq0(v))), ctx)}
    case T.BtExpr{+e} _:
      T.BtExpr{fd.lift.calls(e, fd.lq(e, ctx), name, n, ctx)}
    case T.BtAnn{+a, ty} _:
      T.BtAnn{fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx), ty}
    case T.BtSucc{+a} _:
      T.BtSucc{fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx)}
    case T.BtDead{+a} _:
      T.BtDead{fd.lift.calls(a, fd.lq(a, ctx), name, n, ctx)}
    case u _:
      u

# a lifted def's parameters, each live one + where its body uses it twice
def fd.lift.ps(ps: T.Bt, +b: T.Bt) -> List<&2, T.BParam>:
  match ps:
    case T.BtArgs{T.BtAnn{T.BtPv{T.BmErased{}, x}, ty}, r}:
      T.BParam{T.BmErased{}, x, ty} <> fd.lift.ps(r, b)
    case T.BtArgs{T.BtAnn{T.BtPv{m, +x}, ty}, r}:
      T.BParam{fd.mode(fd.uses(b, x)), x, ty} <> fd.lift.ps(r, b)
    case _:
      Nil{}

# a lifted def: the type variables, the locals fv, its own parameters ps
def fd.lift.def(+k: List<&2, U32>, +name: List<&2, U32>, tvs: T.Bt, fv: List<&2, Lt>, ps: T.Bt, res: T.Bt, body: T.Bt) -> T.BItem:
  +b = fd.mark(body)
  T.BiDef{k, fd.lift.ps(T.tba.args(List.concat(&2, T.Bt, [fd.lift.tvs(fd.spine(tvs)), fd.lift.lts(fv), fd.spine(ps)])), b), res, b, fd.cat(S.b("generated: lifted out of "), name) <> Nil{}}

# a group's defs (fd.gm.own): ms the members' markers, bs the same with
# their bodies' calls written
def fd.gm.defs(ms: T.Bt, bs: T.Bt, +name: List<&2, U32>, +fv: List<&2, Lt>) -> List<&2, T.BItem>:
  match ms bs:
    case T.BtArgs{T.BtApp{_, T.BtArgs{ps, T.BtArgs{res, T.BtArgs{_, T.BtArgs{T.BtVar{x}, T.BtArgs{_, T.BtArgs{_, T.BtArgs{tvs, _}}}}}}}}, r} T.BtArgs{T.BtApp{_, T.BtArgs{_, T.BtArgs{_, T.BtArgs{body, _}}}}, rb}:
      fd.lift.def(fd.ldef.name(name, x), name, tvs, fv, ps, res, body) <> fd.gm.defs(r, rb, name, fv)
    case T.BtArgs{_, r} T.BtArgs{_, rb}:
      fd.gm.defs(r, rb, name, fv)
    case _ _:
      Nil{}

# the defs the markers make, in order (one before any def it is in)
def fd.lift.items(t: T.Bt, q: Lq, +name: List<&2, U32>, +n: Nat, +ctx: List<&2, Lf>) -> List<&2, T.BItem>:
  match t q:
    case T.BtApp{_, T.BtArgs{+ps, T.BtArgs{res, T.BtArgs{+body, T.BtArgs{+oa, T.BtArgs{+lts, T.BtArgs{tvs, _}}}}}}} LqMark{}:
      +nb = fd.lift.n(body, fd.lq0(body))
      +na = fd.lift.n(oa, fd.lq0(oa))
      +b1 = fd.lift.calls(body, fd.lq(body, ctx), name, n, ctx)
      List.concat(&2, T.BItem, [fd.lift.items(body, fd.lq(body, ctx), name, n, ctx), fd.lift.items(oa, fd.lq(oa, ctx), name, Nat.add(n, nb), ctx), fd.lift.def(fd.lift.name(name, Nat.add(n, Nat.add(nb, na))), name, tvs, fd.fvs(b1, fd.lts.un(lts), fd.ps.names(ps)), ps, res, b1) <> Nil{}])
    case T.BtLet{_, T.BtApp{_, T.BtArgs{+ps, T.BtArgs{res, T.BtArgs{+body, T.BtArgs{T.BtVar{+x}, T.BtArgs{+ar, T.BtArgs{+lts, T.BtArgs{+tvs, _}}}}}}}}, b} LqDef{}:
      +h = fd.ldef.name(name, x)
      +b1 = fd.lift.calls(body, fd.lq(body, ctx), name, n, ctx)
      +fv = fd.fvs(b1, fd.lts.un(lts), x <> fd.ps.names(ps))
      +ctx2 = {Lf{x, h, List.append(&2, T.Bt, fd.spine(tvs), fd.lt.vars(fv)), T.tba.args.len(ar)} <> ctx : List<&2, Lf>}
      List.concat(&2, T.BItem, [fd.lift.items(body, fd.lq(body, ctx2), name, n, ctx2), fd.lift.def(h, name, tvs, fv, ps, res, fd.lift.calls(body, fd.lq(body, ctx2), name, n, ctx2)) <> Nil{}, fd.lift.items(b, fd.lq(b, ctx2), name, Nat.add(n, fd.lift.n(body, fd.lq0(body))), ctx2)])
    case T.BtLet{_, T.BtApp{_, +ms}, +b} LqGrp{}:
      +fv = fd.gm.fvs(fd.lift.calls(ms, fd.lq(ms, ctx), name, n, ctx), fd.gm.own(ms), Nil{})
      +ctx2 = fd.gm.ctx(ms, name, fv, ctx)
      List.concat(&2, T.BItem, [fd.lift.items(ms, fd.lq(ms, ctx2), name, n, ctx2), fd.gm.defs(ms, fd.lift.calls(ms, fd.lq(ms, ctx2), name, n, ctx2), name, fv), fd.lift.items(b, fd.lq(b, ctx2), name, Nat.add(n, fd.lift.n(ms, fd.lq0(ms))), ctx2)])
    case T.BtApp{f, +a} LqApp{g}:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case T.BtApp{+f, +a} _:
      List.append(&2, T.BItem, fd.lift.items(f, fd.lq(f, ctx), name, n, ctx), fd.lift.items(a, fd.lq(a, ctx), name, Nat.add(n, fd.lift.n(f, fd.lq0(f))), ctx))
    case T.BtArgs{+a, +r} _:
      List.append(&2, T.BItem, fd.lift.items(a, fd.lq(a, ctx), name, n, ctx), fd.lift.items(r, fd.lq(r, ctx), name, Nat.add(n, fd.lift.n(a, fd.lq0(a))), ctx))
    case T.BtTplArg{+a} _:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case T.BtLam{m, x, +b} _:
      fd.lift.items(b, fd.lq(b, ctx), name, n, ctx)
    case T.BtCon{c, +a} _:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case T.BtMatch{xs, +cs} _:
      fd.lift.items(cs, fd.lq(cs, ctx), name, n, ctx)
    case T.BtCase{p, +b, +r} _:
      List.append(&2, T.BItem, fd.lift.items(b, fd.lq(b, ctx), name, n, ctx), fd.lift.items(r, fd.lq(r, ctx), name, Nat.add(n, fd.lift.n(b, fd.lq0(b))), ctx))
    case T.BtLet{x, +v, +b} _:
      List.append(&2, T.BItem, fd.lift.items(v, fd.lq(v, ctx), name, n, ctx), fd.lift.items(b, fd.lq(b, ctx), name, Nat.add(n, fd.lift.n(v, fd.lq0(v))), ctx))
    case T.BtExpr{+e} _:
      fd.lift.items(e, fd.lq(e, ctx), name, n, ctx)
    case T.BtAnn{+a, ty} _:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case T.BtSucc{+a} _:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case T.BtDead{+a} _:
      fd.lift.items(a, fd.lq(a, ctx), name, n, ctx)
    case _ _:
      Nil{}

# a def from its name, its type variables and its clauses (an RMs)
def fd.def.of(+name: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, +tys: List<&2, T.Bt>, res: T.Bt, +cls: List<&2, R>) -> List<&2, T.BItem>:
  +pms = fd.pms(List.length(&2, T.Bt, tys), 0n, cls)
  +b0 = fd.body.of(fd.anysplit(pms), pms, cls)
  +vn = fd.vname(name)
  +body = fd.mark(fd.lift.calls(b0, fd.lq0(b0), vn, 0n, Nil{}))
  List.append(&2, T.BItem, fd.lift.items(b0, fd.lq0(b0), vn, 0n, Nil{}), T.BiDef{vn, List.append(&2, T.BParam, fd.tvparams(tvs), fd.params(pms, tys, body)), res, body, Nil{}} <> Nil{})

def fd.def(+name: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, r: R) -> List<&2, T.BItem>:
  match r:
    case RMs{tys, res, cls}:
      fd.def.of(name, tvs, tys, res, cls)
    case _:
      T.BiDef{fd.vname(name), Nil{}, fd.todo("fold:shape"), fd.todo("fold:shape"), Nil{}} <> Nil{}

# Right-hand sides --------------------------------------------------------------

# a guard's condition: none for otherwise (True)
def fd.cond.of(t: T.Bt) -> Maybe<&2, T.Bt>:
  match t:
    case T.BtCon{+c, T.BtANil{}}:
      Bool.pick(Maybe<&2, T.Bt>, fd.is(c, "True"), None{}, Some{T.BtCon{c, T.BtANil{}}})
    case u:
      Some{u}

def fd.conds(cs: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match cs:
    case Nil{}:
      None{}
    case c <> Nil{}:
      fd.cond.of(c)
    case c <> t:
      Some{fd.callS("Bool.and", [c, Maybe.default(&2, T.Bt, fd.conds(t), fd.con0("True"))])}

# a branch of Bool.if, Unit -> R: its binder is _, so that it names no
# variable of the branch (it was u, which hid a u the branch used: `\(t, u)
# -> if u > 2 then Just (t + u) ..` saw u as the Unit)
def fd.thunk(t: T.Bt) -> T.Bt:
  T.BtLam{T.BmLive{}, S.b("_"), fd.expr(t)}

def fd.if(res: Maybe<&2, T.Bt>, c: T.Bt, a: T.Bt, b: T.Bt) -> T.Bt:
  match res:
    case Some{r}:
      fd.callS("Bool.if", [r, c, fd.thunk(a), fd.thunk(b)])
    case None{}:
      fd.todo("fold:if-in-argument")

# guarded right-hand sides as one body
def fd.chain(gs: List<&2, R>, +res: Maybe<&2, T.Bt>) -> T.Bt:
  match gs:
    case RG{None{}, b} <> t:
      b
    case RG{Some{c}, b} <> Nil{}:
      fd.todo("fold:guard-falls-through")
    case RG{Some{c}, b} <> t:
      fd.if(res, c, b, fd.chain(t, res))
    case _:
      fd.todo("fold:right-hand-side")

def fd.bnames(bs: List<&2, R>) -> List<&2, List<&2, U32>>:
  match bs:
    case RB{x, v} <> t:
      x <> fd.bnames(t)
    case RPb{p, v, ty} <> t:
      T.tba.pvars(p, fd.bnames(t))
    case RLf{x, tys, res, cls} <> t:
      x <> fd.bnames(t)
    case RL{ys} <> t:
      List.append(&2, List<&2, U32>, fd.bnames(ys), fd.bnames(t))
    case _ <> t:
      fd.bnames(t)
    case Nil{}:
      Nil{}

def fd.grhs(gs: R, e: R, +env: Env) -> R:
  RG{fd.conds(fd.exs(fd.items(gs), env)), fd.ex(e, env)}

def fd.clause(ps: R, b: R) -> R:
  RC{fd.bts(fd.items(ps)), fd.rt(b)}

def fd.ms(tys: R, +res: T.Bt, cls: R) -> R:
  RMs{fd.bts(fd.items(tys)), res, fd.items(cls)}

# a lambda: one clause of variables
def fd.lam.go(ps: List<&2, T.Bt>, b: T.Bt) -> T.Bt:
  match ps:
    case T.BtPv{m, x} <> t:
      T.BtLam{T.BmLive{}, x, fd.lam.go(t, b)}
    case T.BtWild{} <> t:
      T.BtLam{T.BmLive{}, S.b("_"), fd.lam.go(t, b)}
    case _ <> t:
      fd.todo("fold:lambda-pattern")
    case Nil{}:
      fd.expr(b)

def fd.lam.one(cls: List<&2, R>) -> T.Bt:
  match cls:
    case RC{ps, b} <> Nil{}:
      fd.lam.go(ps, b)
    case _:
      fd.todo("fold:lambda")

def fd.lam.if(flat: Bool, tys: List<&2, T.Bt>, res: T.Bt, cls: List<&2, R>, +env: Env) -> T.Bt:
  match flat:
    case True{}:
      fd.lam.one(cls)
    case False{}:
      fd.lift.of(True{}, tys, res, cls, env, fd.con0("Unit"))

# a lambda: one clause of variables and an expression, else lifted
def fd.lam(r: R, +env: Env) -> R:
  match r:
    case RMs{tys, res, +cls}:
      RE{fd.et(fd.lam.if(fd.lam.flat(cls), tys, res, cls, env))}
    case _:
      fd.bad(S.b("fold:lambda"))

def fd.ecase.of(r0: Maybe<&2, T.Bt>, +x: List<&2, U32>, tys: List<&2, T.Bt>, res: T.Bt, cls: List<&2, R>, +env: Env) -> T.Bt:
  match r0:
    case Some{r}:
      T.BtMatch{T.tba.args([T.BtVar{x}]), fd.cases(cls, [Pm{x, True{}}])}
    case None{}:
      fd.lift.of(False{}, tys, res, cls, env, T.BtVar{x})

# case x of ..: a match on the local x (lifted in an argument)
def fd.ecase(+x: List<&2, U32>, r: R, +env: Env) -> R:
  match r:
    case RMs{tys, res, cls}:
      RE{fd.et(fd.ecase.of(fd.env.res(env), x, tys, res, cls, env))}
    case _:
      fd.bad(S.b("fold:case"))

# case e of .. on a computed e: lifted
def fd.ecasec(e: R, r: R, +env: Env) -> R:
  match r:
    case RMs{tys, res, cls}:
      RE{fd.et(fd.lift.of(False{}, tys, res, cls, env, fd.ex(e, env)))}
    case _:
      fd.bad(S.b("fold:case"))


# A local function (a where- or let-bound binding with arguments) is lifted
# too: %ldef(PARAMS, RES, BODY, x, EXTRA, ARITY) stands as a let's value
# (_ = %ldef(..)) in front of the rest of its scope; fd.def.of takes it out
# as a def NAME.x and makes each use of x in the scope a call of NAME.x with
# EXTRA (the type variables and the locals it uses) before the use's own
# arguments (ARITY: a spine as long as its parameters; a use with fewer is
# eta-expanded).  A recursive local (a rec group of one binding) calls its own
# def the same way.
def fd.ldef.of(+x: List<&2, U32>, +tys: List<&2, T.Bt>, res: T.Bt, +cls: List<&2, R>, +env: Env) -> T.Bt:
  +pms = fd.pms(List.length(&2, T.Bt, tys), 0n, cls)
  fd.callS("%ldef", [T.tba.args(fd.lift.lts(fd.lt.zip(fd.pm.names(pms), tys))), res, fd.body.of(fd.anysplit(pms), pms, cls), T.BtVar{x}, T.tba.args(fd.wilds(List.length(&2, T.Bt, tys))), fd.lts.spine(fd.env.lt(env)), T.tba.args(fd.env.self(env))])

# a match after a let: Bend matches before any local statement, so it is
# lifted, its own def a match on parameters (the locals it uses)
def fd.ismatch(t: T.Bt) -> Bool:
  match t:
    case T.BtMatch{xs, cs}:
      True{}
    case _:
      False{}

def fd.lift.stmt(r: Maybe<&2, T.Bt>, b: T.Bt, +env: Env) -> T.Bt:
  match r:
    case Some{res}:
      T.BtExpr{fd.callS("%lift", [T.BtANil{}, res, b, T.BtANil{}, fd.lts.spine(fd.env.lt(env)), T.tba.args(fd.env.self(env))])}
    case None{}:
      b

def fd.lets.m(m: Bool, b: T.Bt, +env: Env) -> T.Bt:
  match m:
    case True{}:
      fd.lift.stmt(fd.env.res(env), b, env)
    case False{}:
      fd.stmt(b)

def fd.lets.end(some: Bool, +b: T.Bt, +env: Env) -> T.Bt:
  match some:
    case True{}:
      fd.lets.m(fd.ismatch(b), b, env)
    case False{}:
      fd.stmt(b)

# a group's members (fd.abs1), each a local function
def fd.ldef.ofs(rs: List<&2, R>, +env: Env) -> List<&2, T.Bt>:
  match rs:
    case RLf{x, tys, res, cls} <> t:
      fd.ldef.of(x, tys, res, cls, env) <> fd.ldef.ofs(t, env)
    case _ <> t:
      fd.todo("fold:local-group-value") <> fd.ldef.ofs(t, env)
    case Nil{}:
      Nil{}

def fd.lt.minus.put(drop: Bool, h: Lt, rest: List<&2, Lt>) -> List<&2, Lt>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

def fd.lt.minus(xs: List<&2, Lt>, +ns: List<&2, List<&2, U32>>) -> List<&2, Lt>:
  match xs:
    case Lt{+x, t} <> r:
      fd.lt.minus.put(S.mem(x, ns), Lt{x, t}, fd.lt.minus(r, ns))
    case Nil{}:
      Nil{}

# env without the locals ns' types: names a case binds, not locals the
# lifted def takes
def fd.env.ltless(e: Env, +ns: List<&2, List<&2, U32>>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y, p, q}:
      Env{m, c, d, r, s, l, y, p, fd.lt.minus(q, ns)}

# a local pattern binding, (a, b) = e, in front of the rest b: a case on e
# (Bend matches no computed value nor a let's local), lifted as fd.ecasec's
# is, at the pattern's type (Spec's sp.pb wrote it); the pattern's
# variables are the case's, not locals the lifted def takes
def fd.pb.of(res: Maybe<&2, T.Bt>, +p: T.Bt, v: T.Bt, +ty: T.Bt, b: T.Bt, +env: Env) -> T.Bt:
  match res:
    case Some{r}:
      fd.lift.of(False{}, [ty], r, [RC{[p], b}], fd.env.ltless(env, T.tba.pvars(p, Nil{})), fd.expr(v))
    case None{}:
      fd.todo("fold:let-in-argument")

# local bindings in front of a body (some: a statement is written already;
# a local function's %ldef is not one, fd.def.of takes it out)
def fd.lets.go(bs: List<&2, R>, b: T.Bt, +env: Env, some: Bool) -> T.Bt:
  match bs:
    case RB{x, v} <> t:
      T.BtLet{x, fd.expr(v), fd.lets.go(t, b, env, True{})}
    case RPb{p, v, ty} <> t:
      fd.pb.of(fd.env.res(env), p, v, ty, fd.lets.go(t, b, env, True{}), env)
    case RLf{x, tys, res, cls} <> t:
      T.BtLet{S.b("_"), fd.ldef.of(x, tys, res, cls, env), fd.lets.go(t, b, env, some)}
    case RL{ys} <> t:
      T.BtLet{S.b("_"), fd.callS("%lgrp", fd.ldef.ofs(ys, env)), fd.lets.go(t, b, env, some)}
    case RT{v} <> t:
      T.BtLet{S.b("_"), v, fd.lets.go(t, b, env, True{})}
    case _ <> t:
      T.BtLet{S.b("_"), fd.todo("fold:local-binding"), fd.lets.go(t, b, env, True{})}
    case Nil{}:
      fd.lets.end(some, b, env)

def fd.lets(bs: List<&2, R>, b: T.Bt, +env: Env) -> T.Bt:
  fd.lets.go(bs, b, env, False{})

# whether the local t occurs in x (a recursive local value: its body names
# it)
def fd.occurs(x: X.Sx, +t: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +tl}:
      Bool.or(V.sv.sxeq(X.SxCons{h, tl}, t), Bool.or(fd.occurs(h, t), fd.occurs(tl, t)))
    case y:
      V.sv.sxeq(y, t)

# a local value: a let, lifted when its body is a statement; one that names
# itself (go = do .. go ..) is a local function of no parameters, lifted
# (its def recurs: the gate's fuel)
def fd.lbind.val(rec: Bool, +x: List<&2, U32>, +res: T.Bt, +cls: List<&2, R>, +env: Env) -> R:
  match rec:
    case True{}:
      RLf{x, Nil{}, res, cls}
    case False{}:
      RB{x, T.BtAnn{fd.lam.if(fd.lam.flat(cls), Nil{}, res, cls, env), res}}

# a local binding: a value (a fun with no arguments) is a let (see
# fd.lbind.val); a local function is lifted (RLf)
def fd.lbind(+x: List<&2, U32>, r: R, +env: Env, rec: Bool) -> R:
  match r:
    case RMs{Nil{}, +res, +cls}:
      fd.lbind.val(rec, x, res, cls, env)
    case RMs{tys, res, cls}:
      RLf{x, tys, res, cls}
    case _:
      RB{x, fd.todo("fold:local-function")}

# the local functions' names, and the types of the others (a local
# function is no local of the defs lifted in its scope: its uses there are
# calls of its own def)
def fd.rlf.names(xs: List<&2, R>) -> List<&2, List<&2, U32>>:
  match xs:
    case RLf{x, tys, res, cls} <> t:
      x <> fd.rlf.names(t)
    case RL{ys} <> t:
      List.append(&2, List<&2, U32>, fd.rlf.names(ys), fd.rlf.names(t))
    case _ <> t:
      fd.rlf.names(t)
    case Nil{}:
      Nil{}

# An if whose branches both use a local that is a function (or a twin, see
# Twins), which Bend's Type does not copy: each branch takes it as an
# argument, and the if is applied to it once, Bool.if(T -> R, c, u => x =>
# a, u => x => b)(x).
def fd.if.lin(lts: List<&2, Lt>, +fa: List<&2, List<&2, U32>>, +fb: List<&2, List<&2, U32>>) -> List<&2, Lt>:
  match lts:
    case Nil{}:
      Nil{}
    case Lt{+x, +t} <> r:
      +rest = fd.lt.minus(fd.if.lin(r, fa, fb), [x])
      Bool.pick(List<&2, Lt>, Bool.and(fd.isfn(t), Bool.and(S.mem(x, fa), S.mem(x, fb))), Lt{x, t} <> rest, rest)

def fd.if.lams(vs: List<&2, Lt>, b: T.Bt) -> T.Bt:
  match vs:
    case Nil{}:
      b
    case Lt{x, t} <> r:
      T.BtLam{T.BmLive{}, x, fd.if.lams(r, b)}

def fd.if.pis(vs: List<&2, Lt>, r: T.Bt) -> T.Bt:
  match vs:
    case Nil{}:
      r
    case Lt{x, t} <> u:
      T.BtPi{T.BmLive{}, S.b("_"), False{}, t, fd.if.pis(u, r)}

def fd.if.vars(vs: List<&2, Lt>) -> List<&2, T.Bt>:
  match vs:
    case Nil{}:
      Nil{}
    case Lt{x, t} <> r:
      T.BtVar{x} <> fd.if.vars(r)

def fd.if.at(+vs: List<&2, Lt>, res: Maybe<&2, T.Bt>, c: T.Bt, a: T.Bt, b: T.Bt) -> T.Bt:
  match vs res:
    case Nil{} r:
      fd.if(r, c, a, b)
    case _ Some{r}:
      T.tba.call(fd.if(Some{fd.if.pis(vs, r)}, c, fd.if.lams(vs, a), fd.if.lams(vs, b)), fd.if.vars(vs))
    case _ None{}:
      fd.todo("fold:if-in-argument")

def fd.eif(c: R, a: R, b: R, +env: Env) -> R:
  +ta = fd.ex(a, env)
  +tb = fd.ex(b, env)
  +vs = fd.if.lin(fd.env.lt(env), T.tba.frees(ta, Nil{}), T.tba.frees(tb, Nil{}))
  RE{fd.et(fd.if.at(vs, fd.env.res(env), fd.ex(c, env), ta, tb))}

def fd.elet.of(res: Maybe<&2, T.Bt>, bs: List<&2, R>, b: T.Bt, +env: Env) -> T.Bt:
  match res:
    case Some{r}:
      fd.lets(bs, b, env)
    case None{}:
      fd.todo("fold:let-in-argument")

def fd.elet(bs: R, e: R, +env: Env) -> R:
  RE{fd.et(fd.elet.of(fd.env.res(env), fd.items(bs), fd.ex(e, env), env))}

def fd.grhss(bs: R, gs: R, +env: Env) -> R:
  RT{fd.lets(fd.items(bs), fd.chain(fd.items(gs), fd.env.res(env)), env)}

def fd.multiif(+ty: R, gs: R) -> R:
  RE{fd.et(fd.expr(fd.chain(fd.items(gs), Some{fd.rt(ty)})))}

# A type synonym is replaced by its right-hand side, its variables by the
# arguments, all at once: first each variable X becomes X% (no Haskell
# name has a %), then each X% its argument.
def fd.syn.mark(tvs: List<&2, List<&2, U32>>, body: T.Bt) -> T.Bt:
  match tvs:
    case +v <> t:
      fd.syn.mark(t, T.tba.subst(body, v, T.BtVar{fd.cat(v, S.b("%"))}))
    case Nil{}:
      body

# the marker hs.Pc (a parser's monad) applied to its result: a parser
def fd.ty.app.pc(pc: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match pc args:
    case True{} r <> Nil{}:
      fd.ty.pc(r)
    case _ xs:
      T.BtTyApp{n, T.tba.args(List.append(&2, T.Bt, fd.spine(a), xs))}

def fd.ty.app.wr(wr: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match wr:
    case True{}:
      fd.ty.wrs(fd.is(n, "hs.WriterE"), List.append(&2, T.Bt, fd.spine(a), args))
    case False{}:
      fd.ty.app.pc(fd.is(n, "hs.Pc"), n, a, args)

def fd.ty.app.rd(rd: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match rd:
    case True{}:
      fd.ty.rds(fd.is(n, "hs.ReaderE"), List.append(&2, T.Bt, fd.spine(a), args))
    case False{}:
      fd.ty.app.wr(Bool.or(fd.is(n, "hs.Writer"), fd.is(n, "hs.WriterE")), n, a, args)

# a type applied to more arguments (a synonym of fewer variables than its
# use has arguments: type M = State Meter, used as M ())
def fd.ty.app.ex(ex: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match ex:
    case True{}:
      fd.ty.exs(List.append(&2, T.Bt, fd.spine(a), args))
    case False{}:
      fd.ty.app.rd(Bool.or(fd.is(n, "hs.Reader"), fd.is(n, "hs.ReaderE")), n, a, args)

def fd.ty.app.if(st: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match st:
    case True{}:
      fd.ty.state(List.append(&2, T.Bt, fd.spine(a), args))
    case False{}:
      fd.ty.app.ex(fd.is(n, "hs.ExceptS"), n, a, args)

def fd.ty.app(t: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match t:
    case T.BtTyApp{+n, a}:
      fd.ty.app.if(fd.is(n, "hs.State"), n, a, args)
    case _:
      fd.todo("fold:synonym-arity")

def fd.syn.fill(tvs: List<&2, List<&2, U32>>, body: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match tvs args:
    case v <> t a <> u:
      fd.syn.fill(t, T.tba.subst(body, fd.cat(v, S.b("%")), a), u)
    case Nil{} Nil{}:
      body
    case Nil{} a <> u:
      fd.ty.app(body, a <> u)
    case _ _:
      fd.todo("fold:synonym-arity")

# the module's synonym named n (none for another module's type)
def fd.syn.find(ss: List<&2, Syn>, +n: List<&2, U32>) -> Maybe<&2, Syn>:
  match ss:
    case Syn{+sn, tvs, body} <> t:
      Bool.pick(Maybe<&2, Syn>, S.eq(sn, n), Some{Syn{sn, tvs, body}}, fd.syn.find(t, n))
    case Nil{}:
      None{}

def fd.syn.own(own: Bool, ss: List<&2, Syn>) -> List<&2, Syn>:
  match own:
    case True{}:
      ss
    case False{}:
      Nil{}

def fd.tc.syn(found: Maybe<&2, Syn>, +k: Tk, tn: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>, +args: List<&2, T.Bt>) -> T.Bt:
  match found:
    case Some{Syn{sn, +tvs, body}}:
      fd.syn.fill(tvs, fd.syn.mark(tvs, body), args)
    case None{}:
      fd.tc.of(k, tn, key, args)

def fd.tc.imp(found: Maybe<&2, Ix>) -> Maybe<&2, List<&2, U32>>:
  match found:
    case Some{IxTy{k, b}}:
      Some{b}
    case _:
      None{}

# a type's Bend name: the module's own, or an earlier module's of the package
def fd.tc.name(own: Bool, home: Bool, +n: List<&2, U32>, +key: List<&2, U32>, +env: Env) -> Maybe<&2, List<&2, U32>>:
  match own home:
    case True{} _:
      Some{fd.tyname(n)}
    case False{} True{}:
      fd.tc.imp(fd.ix.findv(fd.env.ix(env), key, True{}))
    case False{} False{}:
      None{}

# (tc MOD NAME ARG...): a synonym of the module (by its name) or of an
# earlier module of the package (by its key) is expanded
def fd.tc(+m: List<&2, U32>, +n: List<&2, U32>, args: R, +env: Env) -> R:
  +key = fd.cat3(m, S.b("."), n)
  +own = S.eq(m, fd.env.m(env))
  +home = S.mem(m, fd.env.home(env))
  RT{fd.tc.syn(fd.syn.find(fd.syn.own(Bool.or(own, home), fd.env.syn(env)), fd.bpick(own, n, key)), fd.tk.find(fd.tktab(), key), fd.tc.name(own, home, n, key, env), key, fd.bts(fd.items(args)))}

def fd.tfun(a: R, b: R) -> R:
  RT{T.BtPi{T.BmLive{}, S.b("_"), False{}, fd.rt(a), fd.rt(b)}}

def fd.olit(+v: X.Sx, t: R) -> R:
  RE{fd.et(fd.olit.of(fd.tq(fd.rt(t)), v))}

def fd.etuple(es: R, +env: Env) -> R:
  RE{fd.et(fd.tuple(fd.exs(fd.items(es), env)))}

def fd.elist(es: R, +env: Env) -> R:
  RE{fd.et(fd.conchain(fd.exs(fd.items(es), env)))}

def fd.ptuple(ps: R) -> R:
  RT{fd.tuple(fd.bts(fd.items(ps)))}

def fd.plist(ps: R) -> R:
  RT{fd.conchain(fd.bts(fd.items(ps)))}

def fd.pnlit.at(q: Tq, +neg: Bool, +v: X.Sx) -> T.Bt:
  match q:
    case TqInt{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), fd.hsint(neg, X.tsx.atom.of(V.sv.at(v, 1n))), fd.todo("fold:literal-pattern"))
    case _:
      Bool.pick(T.Bt, Bool.and(Bool.not(neg), V.sv.is(V.sv.hd(v), "int")), T.BtNat{X.tsx.atom.of(V.sv.at(v, 1n))}, T.BtTodo{fd.bpick(neg, S.b("int-sub"), S.b("fold:literal-pattern"))})

def fd.pnlit(+v: X.Sx, +sg: X.Sx, t: R) -> R:
  RT{fd.pnlit.at(fd.tq(fd.rt(t)), V.sv.is(X.tsx.atom.of(sg), "neg"), v)}

# a string literal as a pattern: its characters' list (printable ASCII
# characters but ' and \, which a Bend pattern writes as themselves)
def fd.plit.str(bs: List<&2, U32>) -> T.Bt:
  match bs:
    case Nil{}:
      T.BtCon{S.b("Nil"), T.BtANil{}}
    case +c <> t:
      +ok = Bool.and(Bool.and(U32.is_ge(c, 32), U32.is_le(c, 126)), Bool.and(U32.is_ne(c, 39), U32.is_ne(c, 92)))
      Bool.pick(T.Bt, ok, T.BtCon{S.b("Con"), T.tba.args([fd.char(U32.to_nat(c)), fd.plit.str(t)])}, fd.todo("fold:literal-pattern"))

def fd.plit(+v: X.Sx) -> R:
  RT{Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "char"), fd.char(X.tsx.nat(V.sv.at(v, 1n))), Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "string"), fd.plit.str(X.tsx.str.of(V.sv.at(v, 1n))), fd.todo("fold:literal-pattern")))}

def fd.selfname(+v: X.Sx) -> List<&2, U32>:
  fd.bpick(V.sv.is(V.sv.hd(v), "g"), V.sv.str(v, 2n), V.sv.str(v, 1n))

# a recursive reference: the def's own (self (g ..)), called at the def's
# type parameters, or a local's (self (l ..)), a local like any other (its
# lifting passes the def's type parameters, once)
def fd.self.hd(top: Bool, +v: X.Sx) -> Hd:
  match top:
    case True{}:
      HdSelf{fd.selfname(v)}
    case False{}:
      HdL{fd.vname(V.sv.str(v, 1n))}

def fd.kind.of(x: X.Sx) -> List<&2, U32>:
  match x:
    case X.SxAtom{a}:
      a
    case X.SxCons{X.SxAtom{a}, t}:
      a
    case _:
      Nil{}

# The forms -------------------------------------------------------------------

# Where a form stands: a type, a pattern, an expression.
type Ro is Data:
  RoTy{}
  RoPat{}
  RoEx{}

# Which form a node is, given where it stands (or a container the parent
# names): one constructor per form the fold writes, and KBad with the
# reason for one it does not.
type K is Data:
  KTv{}
  KTc{}
  KTfun{}
  KTys{}
  KPwild{}
  KPvar{}
  KPbang{}
  KPlist{}
  KPtuple{}
  KPcon{}
  KPconF{}
  KPfs{}
  KPf{}
  KPlit{}
  KPnlit{}
  KPs{}
  KEg{}
  KEl{}
  KEself{}
  KEapp{}
  KEtyapp{}
  KEevapp{}
  KEskip1{}
  KEskip2{}
  KEolit{}
  KEnegapp{}
  KEchar{}
  KEstring{}
  KElam{}
  KEtuple{}
  KEcase{}
  KEif{}
  KEmultiif{}
  KElet{}
  KElist{}
  KEreccon{}
  KRfs{}
  KRf{}
  KEs{}
  KMatches{}
  KMs{}
  KMatch{}
  KGrhss{}
  KGrhsL{}
  KGrhs{}
  KGuards{}
  KGbody{}
  KBinds{}
  KGroups{}
  KNonrec{}
  KBfun{}
  KBabs{}
  KBpat{}
  KAbs1{}
  KAbsN{}
  KEcaseC{}
  KLtw{}
  KLbv{}
  KLfun{}
  KLstop{}
  KBad{why: List<&2, U32>}

type Kt is Data:
  Kt{s: String, k: K}

def fd.k.find(xs: List<&2, Kt>, +h: List<&2, U32>, +d: K) -> K:
  match xs:
    case Nil{}:
      d
    case Kt{s, k} <> t:
      Bool.pick(K, S.eq(S.b(s), h), k, fd.k.find(t, h, d))

def fd.k.tys() -> List<&2, Kt>:
  [Kt{"tv", KTv{}}, Kt{"tc", KTc{}}, Kt{"tfun", KTfun{}}]

def fd.k.pats() -> List<&2, Kt>:
  [Kt{"pwild", KPwild{}}, Kt{"pvar", KPvar{}}, Kt{"pbang", KPbang{}}, Kt{"plist", KPlist{}}, Kt{"ptuple", KPtuple{}}, Kt{"pcon", KPcon{}}, Kt{"plit", KPlit{}}, Kt{"pnlit", KPnlit{}}]

def fd.k.exs() -> List<&2, Kt>:
  [Kt{"g", KEg{}}, Kt{"l", KEl{}}, Kt{"self", KEself{}}, Kt{"app", KEapp{}}, Kt{"tyapp", KEtyapp{}}, Kt{"evapp", KEevapp{}}, Kt{"cast", KEskip1{}}, Kt{"expanded", KEskip2{}}, Kt{"tylam", KEskip2{}}, Kt{"evlam", KEskip2{}}, Kt{"evlet", KEskip2{}}, Kt{"olit", KEolit{}}, Kt{"negapp", KEnegapp{}}, Kt{"char", KEchar{}}, Kt{"string", KEstring{}}, Kt{"lam", KElam{}}, Kt{"tuple", KEtuple{}}, Kt{"case", KEcase{}}, Kt{"if", KEif{}}, Kt{"multiif", KEmultiif{}}, Kt{"let", KElet{}}, Kt{"list", KElist{}}, Kt{"reccon", KEreccon{}}]

def fd.k.bad(s: String, +h: List<&2, U32>) -> K:
  KBad{fd.cat(S.b(s), h)}

# the refinements: a constructor pattern with fields, a negative literal,
# a case on a computed value, \case
def fd.k.pat(k: K, +x: X.Sx) -> K:
  match k:
    case KPcon{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 3n)), "args"), KPcon{}, KPconF{})
    case KPnlit{}:
      KPnlit{}
    case k1:
      k1

def fd.k.ex(k: K, +x: X.Sx) -> K:
  match k:
    case KEcase{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 1n)), "l"), KEcase{}, KEcaseC{})
    case KElam{}:
      KElam{}
    case k1:
      k1

def fd.k(ro: Ro, +x: X.Sx) -> K:
  match ro:
    case RoTy{}:
      fd.k.find(fd.k.tys(), V.sv.hd(x), fd.k.bad("type:", V.sv.hd(x)))
    case RoPat{}:
      fd.k.pat(fd.k.find(fd.k.pats(), V.sv.hd(x), fd.k.bad("fold:pattern-", V.sv.hd(x))), x)
    case RoEx{}:
      fd.k.ex(fd.k.find(fd.k.exs(), V.sv.hd(x), fd.k.bad("fold:", V.sv.hd(x))), x)

def fd.k.guard(+x: X.Sx) -> K:
  Bool.pick(K, V.sv.is(V.sv.hd(x), "body"), KGbody{}, KBad{S.b("fold:pattern-guard")})

def fd.k.group(+x: X.Sx) -> K:
  Bool.pick(K, Bool.or(V.sv.is(V.sv.hd(x), "nonrec"), Bool.and(V.sv.is(V.sv.hd(x), "rec"), Nat.is_eq(X.tsx.len(x), 2n))), KNonrec{}, KBad{S.b("fold:recursive-local")})

# a local abs (GHC's generalised group) that takes no dictionary is its one
# bind (its type variables are erased in a let)
def fd.k.abs(+x: X.Sx) -> K:
  Bool.pick(K, Nat.is_eq(X.tsx.len(V.sv.at(x, 2n)), 0n), KBabs{}, KBad{S.b("fold:local-abs-class")})

def fd.k.bind(+x: X.Sx) -> K:
  Bool.pick(K, V.sv.is(V.sv.hd(x), "fun"), KBfun{}, Bool.pick(K, V.sv.is(V.sv.hd(x), "abs"), fd.k.abs(x), Bool.pick(K, V.sv.is(V.sv.hd(x), "patbind"), KBpat{}, fd.k.bad("fold:local-", V.sv.hd(x)))))

# a binder's type (see Lifting): (bv VAR TYPE) in a pattern, and a local
# binding's head, (fun VAR TYPE ..) and (export VAR TYPE); a body (matches,
# grhss) and a dictionary's binding are not looked into
def fd.k.lt(+x: X.Sx) -> K:
  +h = V.sv.hd(x)
  Bool.pick(K, V.sv.is(h, "bv"), KLbv{}, Bool.pick(K, Bool.or(V.sv.is(h, "fun"), V.sv.is(h, "export")), KLfun{}, Bool.pick(K, Bool.or(V.sv.is(h, "matches"), Bool.or(V.sv.is(h, "grhss"), V.sv.is(h, "evbinds"))), KLstop{}, KLtw{})))

# The fold: one def over the export's tree, the form k of x given by the
# parent (Bend allows no mutual recursion, so types, patterns, expressions
# and clauses are one walk).  Each case takes x apart and folds its parts.
def fd.go(x: X.Sx, k: K, +env: Env) -> R:
  match x k:
    # types
    case X.SxCons{_, X.SxCons{X.SxStr{n}, _}} KTv{}:
      RT{T.BtVar{fd.tvname(n)}}
    case X.SxCons{_, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, args}}} KTc{}:
      fd.tc(m, n, fd.go(args, KTys{}, env), env)
    case X.SxCons{_, X.SxCons{+a, X.SxCons{+b, _}}} KTfun{}:
      fd.tfun(fd.go(a, fd.k(RoTy{}, a), env), fd.go(b, fd.k(RoTy{}, b), env))
    case X.SxCons{+h, t} KTys{}:
      fd.cons(fd.go(h, fd.k(RoTy{}, h), env), fd.go(t, KTys{}, env))
    case _ KTys{}:
      fd.nil()
    # patterns
    case _ KPwild{}:
      RT{T.BtWild{}}
    case X.SxCons{_, X.SxCons{+bv, _}} KPvar{}:
      RT{T.BtPv{T.BmLive{}, fd.bvname(bv)}}
    case X.SxCons{_, X.SxCons{+p, _}} KPbang{}:
      fd.go(p, fd.k(RoPat{}, p), env)
    case X.SxCons{_, X.SxCons{_, X.SxCons{ps, _}}} KPlist{}:
      fd.plist(fd.go(ps, KPs{}, env))
    case X.SxCons{_, X.SxCons{ps, _}} KPtuple{}:
      fd.ptuple(fd.go(ps, KPs{}, env))
    case X.SxCons{_, X.SxCons{+g, X.SxCons{tys, X.SxCons{X.SxCons{_, ps}, _}}}} KPcon{}:
      fd.pcon.fn(Bool.and(fd.con.twin(g, env), fd.isfn.last(fd.bts(fd.items(fd.go(tys, KTys{}, env))))), fd.pcon(g, fd.go(ps, KPs{}, env), env))
    case X.SxCons{_, X.SxCons{+g, X.SxCons{_, X.SxCons{X.SxCons{_, fps}, _}}}} KPconF{}:
      fd.pconf(g, fd.go(fps, KPfs{}, env), env)
    case X.SxCons{+h, t} KPfs{}:
      fd.cons(fd.go(h, KPf{}, env), fd.go(t, KPfs{}, env))
    case _ KPfs{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{+sel, X.SxCons{+p, _}}} KPf{}:
      fd.field(sel, fd.go(p, fd.k(RoPat{}, p), env))
    case X.SxCons{_, X.SxCons{+v, _}} KPlit{}:
      fd.plit(v)
    case X.SxCons{_, X.SxCons{X.SxCons{_, X.SxCons{+v, _}}, X.SxCons{+sg, X.SxCons{+t, _}}}} KPnlit{}:
      fd.pnlit(v, sg, fd.go(t, fd.k(RoTy{}, t), env))
    case X.SxCons{+h, t} KPs{}:
      fd.cons(fd.go(h, fd.k(RoPat{}, h), env), fd.go(t, KPs{}, env))
    case _ KPs{}:
      fd.nil()
    # expressions
    case +g KEg{}:
      RE{fd.e0(fd.hd(V.sv.str(g, 1n), V.sv.str(g, 2n), fd.kind.of(V.sv.at(g, 3n))))}
    case +l KEl{}:
      RE{fd.e0(HdL{fd.vname(V.sv.str(l, 1n))})}
    case X.SxCons{_, X.SxCons{+v, _}} KEself{}:
      RE{fd.e0(fd.self.hd(V.sv.is(V.sv.hd(v), "g"), v))}
    case X.SxCons{_, X.SxCons{+f, X.SxCons{+a, _}}} KEapp{}:
      RE{fd.eapp(fd.re(fd.go(f, fd.k(RoEx{}, f), fd.notail(env))), fd.re(fd.go(a, fd.k(RoEx{}, a), fd.notail(env))))}
    case X.SxCons{_, X.SxCons{+e, X.SxCons{+t, _}}} KEtyapp{}:
      RE{fd.etyapp(fd.re(fd.go(e, fd.k(RoEx{}, e), env)), fd.rt(fd.go(t, fd.k(RoTy{}, t), env)))}
    case X.SxCons{_, X.SxCons{+e, _}} KEevapp{}:
      fd.go(e, fd.k(RoEx{}, e), env)
    case X.SxCons{_, X.SxCons{+e, _}} KEskip1{}:
      fd.go(e, fd.k(RoEx{}, e), env)
    case X.SxCons{_, X.SxCons{_, X.SxCons{+e, _}}} KEskip2{}:
      fd.go(e, fd.k(RoEx{}, e), env)
    case X.SxCons{_, X.SxCons{+e, X.SxCons{+n, _}}} KEnegapp{}:
      RE{fd.eapp(fd.re(fd.go(n, fd.k(RoEx{}, n), fd.notail(env))), fd.re(fd.go(e, fd.k(RoEx{}, e), fd.notail(env))))}
    case X.SxCons{_, X.SxCons{+v, X.SxCons{+t, _}}} KEolit{}:
      fd.olit(v, fd.go(t, fd.k(RoTy{}, t), env))
    case X.SxCons{_, X.SxCons{+c, _}} KEchar{}:
      RE{fd.et(fd.char(X.tsx.nat(c)))}
    case X.SxCons{_, X.SxCons{X.SxStr{s}, _}} KEstring{}:
      RE{fd.et(fd.callS("String.to_list", [T.BtStr{s}]))}
    case X.SxCons{_, X.SxCons{_, X.SxCons{ms, _}}} KElam{}:
      fd.lam(fd.go(ms, KMatches{}, env), env)
    case X.SxCons{_, es} KEtuple{}:
      fd.etuple(fd.go(es, KEs{}, fd.notail(env)), env)
    case X.SxCons{_, X.SxCons{+e, X.SxCons{ms, _}}} KEcase{}:
      fd.ecase(fd.vname(V.sv.str(e, 1n)), fd.go(ms, KMatches{}, env), env)
    case X.SxCons{_, X.SxCons{+c, X.SxCons{+a, X.SxCons{+b, _}}}} KEif{}:
      fd.eif(fd.go(c, fd.k(RoEx{}, c), fd.notail(env)), fd.go(a, fd.k(RoEx{}, a), env), fd.go(b, fd.k(RoEx{}, b), env), env)
    case X.SxCons{_, X.SxCons{+t, X.SxCons{gs, _}}} KEmultiif{}:
      +ty = fd.go(t, fd.k(RoTy{}, t), env)
      fd.multiif(ty, fd.go(gs, KGrhsL{}, fd.withres(env, fd.rt(ty))))
    case X.SxCons{_, X.SxCons{+bs, X.SxCons{+e, _}}} KElet{}:
      +rb = fd.go(bs, KBinds{}, fd.notail(env))
      +env2 = fd.addlts(fd.addls(env, fd.bnames(fd.items(rb))), fd.lt.minus(fd.lts.of(fd.go(bs, KLtw{}, env)), fd.rlf.names(fd.items(rb))))
      fd.elet(rb, fd.go(e, fd.k(RoEx{}, e), env2), env2)
    case X.SxCons{_, X.SxCons{_, X.SxCons{es, _}}} KElist{}:
      fd.elist(fd.go(es, KEs{}, fd.notail(env)), env)
    case X.SxCons{_, X.SxCons{+g, X.SxCons{fs, _}}} KEreccon{}:
      fd.reccon(g, fd.go(fs, KRfs{}, fd.notail(env)), env)
    case X.SxCons{+h, t} KRfs{}:
      fd.cons(fd.go(h, KRf{}, env), fd.go(t, KRfs{}, env))
    case _ KRfs{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{+sel, X.SxCons{+e, _}}} KRf{}:
      fd.field(sel, fd.go(e, fd.k(RoEx{}, e), env))
    case X.SxCons{+h, t} KEs{}:
      fd.cons(fd.go(h, fd.k(RoEx{}, h), env), fd.go(t, KEs{}, env))
    case _ KEs{}:
      fd.nil()
    # clauses
    case X.SxCons{_, X.SxCons{ats, X.SxCons{+rt, X.SxCons{_, X.SxCons{ms, _}}}}} KMatches{}:
      +r = fd.rt(fd.go(rt, fd.k(RoTy{}, rt), env))
      fd.ms(fd.go(ats, KTys{}, env), r, fd.go(ms, KMs{}, fd.withres(env, r)))
    case X.SxCons{h, t} KMs{}:
      fd.cons(fd.go(h, KMatch{}, env), fd.go(t, KMs{}, env))
    case _ KMs{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{+ps, X.SxCons{g, _}}} KMatch{}:
      +rp = fd.go(ps, KPs{}, env)
      fd.clause(rp, fd.go(g, KGrhss{}, fd.addlts(fd.addls(env, fd.pnames(fd.bts(fd.items(rp)))), fd.lts.of(fd.go(ps, KLtw{}, env)))))
    case X.SxCons{_, X.SxCons{gs, X.SxCons{+bs, _}}} KGrhss{}:
      +rb = fd.go(bs, KBinds{}, fd.notail(env))
      +env2 = fd.addlts(fd.addls(env, fd.bnames(fd.items(rb))), fd.lt.minus(fd.lts.of(fd.go(bs, KLtw{}, env)), fd.rlf.names(fd.items(rb))))
      fd.grhss(rb, fd.go(gs, KGrhsL{}, env2), env2)
    case X.SxCons{h, t} KGrhsL{}:
      fd.cons(fd.go(h, KGrhs{}, env), fd.go(t, KGrhsL{}, env))
    case _ KGrhsL{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{gd, X.SxCons{+e, _}}} KGrhs{}:
      fd.grhs(fd.go(gd, KGuards{}, fd.notail(env)), fd.go(e, fd.k(RoEx{}, e), env), env)
    case X.SxCons{+h, t} KGuards{}:
      fd.cons(fd.go(h, fd.k.guard(h), env), fd.go(t, KGuards{}, env))
    case _ KGuards{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{+e, _}} KGbody{}:
      fd.go(e, fd.k(RoEx{}, e), env)
    # local bindings
    case X.SxCons{_, gs} KBinds{}:
      fd.go(gs, KGroups{}, env)
    case X.SxCons{+h, t} KGroups{}:
      fd.cons(fd.go(h, fd.k.group(h), env), fd.go(t, KGroups{}, env))
    case _ KGroups{}:
      fd.nil()
    case X.SxCons{_, X.SxCons{+b, _}} KNonrec{}:
      fd.go(b, fd.k.bind(b), env)
    case X.SxCons{_, X.SxCons{_, X.SxCons{_, X.SxCons{_, X.SxCons{_, X.SxCons{bs, _}}}}}} KBabs{}:
      fd.go(bs, KAbs1{}, env)
    # one binding, or a group of several: mutually recursive locals (EAL's
    # classIfaces and tau), each a binding of the let, lifted as one alone
    # is; their calls of each other are calls of their defs, a cycle
    # fd.mu.all writes
    case X.SxCons{+b, t} KAbs1{}:
      fd.abs1(fd.go(b, fd.k.bind(b), env), fd.go(t, KAbsN{}, env))
    case _ KAbs1{}:
      fd.bad(S.b("fold:local-group"))
    case X.SxCons{+b, t} KAbsN{}:
      fd.cons(fd.go(b, fd.k.bind(b), env), fd.go(t, KAbsN{}, env))
    case _ KAbsN{}:
      fd.nil()
    # a local pattern binding, (a, b) = e: a match on e (fd.lets.go's RPb);
    # Spec's sp.pb made its binders plain locals
    case X.SxCons{_, X.SxCons{+p, X.SxCons{_, X.SxCons{g, X.SxCons{+ty, _}}}}} KBpat{}:
      RPb{fd.rt(fd.go(p, fd.k(RoPat{}, p), env)), fd.rt(fd.go(g, KGrhss{}, fd.notail(env))), fd.rt(fd.go(ty, fd.k(RoTy{}, ty), env))}
    case X.SxCons{_, X.SxCons{+v, X.SxCons{_, X.SxCons{_, X.SxCons{+ms, _}}}}} KBfun{}:
      fd.lbind(fd.bvname(X.SxCons{X.SxAtom{S.b("bv")}, X.SxCons{fd.unself(v), X.SxNil{}}}), fd.go(ms, KMatches{}, fd.notail(env)), env, fd.occurs(ms, fd.unself(v)))
    # binders' types (see Lifting)
    case X.SxCons{_, X.SxCons{+v, X.SxCons{+t, _}}} KLbv{}:
      fd.lt1(fd.vname(V.sv.str(v, 1n)), fd.go(t, fd.k(RoTy{}, t), env))
    case X.SxCons{_, X.SxCons{+v, X.SxCons{+t, _}}} KLfun{}:
      fd.lt1(fd.vname(V.sv.str(fd.unself(v), 1n)), fd.go(t, fd.k(RoTy{}, t), env))
    case X.SxCons{+h, t} KLtw{}:
      fd.lt.cat(fd.go(h, fd.k.lt(h), env), fd.go(t, KLtw{}, env))
    case _ KLtw{}:
      fd.nil()
    case _ KLbv{}:
      fd.nil()
    case _ KLfun{}:
      fd.nil()
    case _ KLstop{}:
      fd.nil()
    # case e of .. on a computed e (see Lifting)
    case X.SxCons{_, X.SxCons{+e, X.SxCons{ms, _}}} KEcaseC{}:
      fd.ecasec(fd.go(e, fd.k(RoEx{}, e), fd.notail(env)), fd.go(ms, KMatches{}, env), env)
    case _ KBad{why}:
      fd.bad(why)
    case _ _:
      fd.bad(S.b("fold:form"))

# Data types ---------------------------------------------------------------------

def fd.tvs(xs: X.Sx) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{X.SxStr{s}, t}:
      fd.tvname(s) <> fd.tvs(t)
    case _:
      Nil{}

def fd.fields.named(fs: X.Sx, tys: List<&2, T.Bt>) -> List<&2, T.BField>:
  match fs tys:
    case X.SxCons{X.SxStr{f}, t} ty <> u:
      T.BField{fd.vname(f), ty} <> fd.fields.named(t, u)
    case X.SxCons{+f, t} ty <> u:
      T.BField{fd.vname(V.sv.str(f, 2n)), ty} <> fd.fields.named(t, u)
    case _ _:
      Nil{}

def fd.fields.pos(tys: List<&2, T.Bt>, +i: Nat, +one: Bool) -> List<&2, T.BField>:
  match tys:
    case ty <> t:
      T.BField{fd.bpick(one, S.b("value"), fd.cat(S.b("f"), fd.nshow(i))), ty} <> fd.fields.pos(t, 1n+i, one)
    case Nil{}:
      Nil{}

def fd.fields(named: Bool, fs: X.Sx, +tys: List<&2, T.Bt>) -> List<&2, T.BField>:
  match named:
    case True{}:
      fd.fields.named(fs, tys)
    case False{}:
      fd.fields.pos(tys, 0n, Nat.is_eq(List.length(&2, T.Bt, tys), 1n))

# (con NAME (FIELD...) (ARGTYPE...) (ex NEX NTHETA))
def fd.ctor(+ty: List<&2, U32>, +c: X.Sx, +env: Env) -> T.BCtor:
  +fs = V.sv.at(c, 2n)
  T.BCtor{fd.cname(ty, V.sv.str(c, 1n)), fd.fields(Nat.is_gt(X.tsx.len(fs), 0n), fs, fd.bts(fd.items(fd.go(V.sv.at(c, 3n), KTys{}, env))))}

def fd.ctors(+ty: List<&2, U32>, cs: X.Sx, +env: Env) -> List<&2, T.BCtor>:
  match cs:
    case X.SxCons{+c, t}:
      fd.ctor(ty, c, env) <> fd.ctors(ty, t, env)
    case _:
      Nil{}

# (data NAME (TV...) (CON...) SPAN)
def fd.data(+x: X.Sx, +env: Env) -> T.BItem:
  +n = V.sv.str(x, 1n)
  T.BiType{fd.tyname(n), fd.tvparams(fd.tvs(V.sv.at(x, 2n))), fd.v("Data"), fd.ctors(n, V.sv.at(x, 3n), env), Nil{}}

# the constructors of a data type, for the table
def fd.ctrs.of(+ty: List<&2, U32>, cs: X.Sx, acc: List<&2, Ctr>) -> List<&2, Ctr>:
  match cs:
    case X.SxCons{+c, t}:
      fd.ctrs.of(ty, t, Ctr{V.sv.str(c, 1n), ty, X.tsx.len(V.sv.at(c, 3n)), fd.fnames(V.sv.at(c, 2n))} <> acc)
    case _:
      acc

def fd.isdata(+x: X.Sx) -> Bool:
  Bool.or(V.sv.is(V.sv.hd(x), "data"), V.sv.is(V.sv.hd(x), "newtype"))

def fd.ctrs.if(d: Bool, +x: X.Sx, acc: List<&2, Ctr>) -> List<&2, Ctr>:
  match d:
    case True{}:
      fd.ctrs.of(V.sv.str(x, 1n), V.sv.at(x, 3n), acc)
    case False{}:
      acc

def fd.ctrs(xs: List<&2, X.Sx>) -> List<&2, Ctr>:
  match xs:
    case +h <> t:
      fd.ctrs.if(fd.isdata(h), h, fd.ctrs(t))
    case Nil{}:
      Nil{}

# Top-level bindings -----------------------------------------------------------------

# A binding of the module: its Haskell name, its type variables, and the
# fun that holds its clauses (or the reason it is not one the fold writes).
type Tb is Data:
  TbFun{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, f: X.Sx}
  TbNo{n: List<&2, U32>, why: List<&2, U32>}
  TbSkip{}

# (fun VAR TYPE SPAN MATCHES)
def fd.isfun(+b: X.Sx) -> Bool:
  V.sv.is(V.sv.hd(b), "fun")

def fd.tb.abs.of(one: Bool, nodict: Bool, +n: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, +binds: X.Sx) -> Tb:
  match one nodict:
    case True{} True{}:
      Bool.pick(Tb, fd.isfun(V.sv.at(binds, 0n)), TbFun{n, tvs, V.sv.at(binds, 0n)}, TbNo{n, S.b("fold:binding-shape")})
    case False{} _:
      TbNo{n, S.b("fold:binding-group")}
    case True{} False{}:
      TbNo{n, S.b("fold:class-constraint")}

# the type variables of a type (tforall NAME T)
def fd.isforall(+x: X.Sx) -> Bool:
  V.sv.is(V.sv.hd(x), "tforall")

def fd.foralls(x: X.Sx, hit: Bool) -> List<&2, List<&2, U32>>:
  match x hit:
    case X.SxCons{_, X.SxCons{X.SxStr{n}, X.SxCons{+t, _}}} True{}:
      fd.tvname(n) <> fd.foralls(t, fd.isforall(t))
    case _ _:
      Nil{}

def fd.tvs.of(+t: X.Sx) -> List<&2, List<&2, U32>>:
  fd.foralls(t, fd.isforall(t))

# (abs (TV...) (EVBINDER...) ((export VAR TYPE)...) (EVBINDS...) (BIND...) SPAN)
def fd.tb.abs(+b: X.Sx) -> Tb:
  fd.tb.abs.of(Bool.and(Nat.is_eq(X.tsx.len(V.sv.at(b, 3n)), 1n), Nat.is_eq(X.tsx.len(V.sv.at(b, 5n)), 1n)), Nat.is_eq(X.tsx.len(V.sv.at(b, 2n)), 0n), V.sv.name(V.sv.at(V.sv.at(V.sv.at(b, 3n), 0n), 1n)), fd.tvs.of(V.sv.at(V.sv.at(V.sv.at(b, 3n), 0n), 2n)), V.sv.at(b, 5n))

def fd.tb.of(abs: Bool, fun: Bool, +b: X.Sx) -> Tb:
  match abs fun:
    case True{} _:
      fd.tb.abs(b)
    case False{} True{}:
      TbFun{V.sv.name(V.sv.at(b, 1n)), fd.tvs.of(V.sv.at(b, 2n)), b}
    case False{} False{}:
      TbNo{V.sv.name(V.sv.at(b, 1n)), fd.cat(S.b("fold:top-"), V.sv.hd(b))}

def fd.tb(+top: X.Sx) -> Tb:
  +b = V.sv.at(top, 1n)
  fd.tb.of(V.sv.is(V.sv.hd(b), "abs"), fd.isfun(b), b)

def fd.tbs.if(top: Bool, +x: X.Sx, acc: List<&2, Tb>) -> List<&2, Tb>:
  match top:
    case True{}:
      fd.tb(x) <> acc
    case False{}:
      acc

def fd.tbs(xs: List<&2, X.Sx>) -> List<&2, Tb>:
  match xs:
    case +h <> t:
      fd.tbs.if(V.sv.is(V.sv.hd(h), "top"), h, fd.tbs(t))
    case Nil{}:
      Nil{}

# a fun's arity: (fun VAR TYPE SPAN (matches (ARGTYPE...) ...))
def fd.arity(+f: X.Sx) -> Nat:
  X.tsx.len(V.sv.at(V.sv.at(f, 4n), 1n))

def fd.dfs(tbs: List<&2, Tb>) -> List<&2, Df>:
  match tbs:
    case TbFun{n, tvs, +f} <> t:
      Df{n, fd.arity(f)} <> fd.dfs(t)
    case _ <> t:
      fd.dfs(t)
    case Nil{}:
      Nil{}

# What became of a binding: the item written, or why it is out.
type Got is Data:
  GotDef{n: List<&2, U32>, it: T.BItem}
  GotOut{n: List<&2, U32>, why: List<&2, U32>}

def fd.got.todos(+n: List<&2, U32>, +it: T.BItem, todos: List<&2, List<&2, U32>>) -> Got:
  match todos:
    case Nil{}:
      GotDef{n, it}
    case +w <> t:
      GotOut{n, w}

def fd.got.def(+n: List<&2, U32>, +it: T.BItem) -> Got:
  fd.got.todos(n, it, List.reverse(&2, List<&2, U32>, T.tba.item.fold(~T.tba.todos, it, Nil{})))

# Selectors: a record's field names are functions in Haskell; each is a def
# here, a match on the type's constructors.  A field some constructor lacks
# is a partial function in Haskell and has no def.

# the field names of all the constructors, each once, in order
def fd.addnew(xs: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      fd.addnew(t, Bool.pick(List<&2, List<&2, U32>>, S.mem(h, acc), acc, List.append(&2, List<&2, U32>, acc, h <> Nil{})))

def fd.allf(cs: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case X.SxCons{+c, t}:
      fd.allf(t, fd.addnew(fd.fnames(V.sv.at(c, 2n)), acc))
    case _:
      acc

# the patterns of a constructor of n fields: the i-th bound to v
def fd.selpats(n: Nat, +i: Nat, +j: Nat) -> List<&2, T.Bt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Bool.pick(T.Bt, Nat.is_eq(i, j), T.BtPv{T.BmLive{}, S.b("v")}, T.BtWild{}) <> fd.selpats(p, i, 1n+j)

def fd.selpat.of(+ty: List<&2, U32>, +c: X.Sx, m: Maybe<&2, Nat>) -> Maybe<&2, T.Bt>:
  match m:
    case Some{i}:
      Some{T.BtCon{fd.cname(ty, V.sv.str(c, 1n)), T.tba.args(fd.selpats(X.tsx.len(V.sv.at(c, 3n)), i, 0n))}}
    case None{}:
      None{}

# (con NAME (FIELD...) (ARGTYPE...) ..)
def fd.selpat(+ty: List<&2, U32>, +c: X.Sx, +f: List<&2, U32>) -> Maybe<&2, T.Bt>:
  fd.selpat.of(ty, c, fd.fpos(fd.fnames(V.sv.at(c, 2n)), f, 0n))

def fd.selcases.of(p: Maybe<&2, T.Bt>, r: Maybe<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match p r:
    case Some{q} Some{rest}:
      Some{T.BtCase{T.tba.args([q]), T.BtExpr{T.BtVar{S.b("v")}}, rest}}
    case _ _:
      None{}

def fd.selcases(+ty: List<&2, U32>, cs: X.Sx, +f: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match cs:
    case X.SxCons{+c, t}:
      fd.selcases.of(fd.selpat(ty, c, f), fd.selcases(ty, t, f))
    case _:
      Some{T.BtCEnd{}}

# the field's type, at the first constructor that has it
def fd.selty.of(m: Maybe<&2, Nat>, +c: X.Sx, rest: Maybe<&2, T.Bt>, +env: Env) -> Maybe<&2, T.Bt>:
  match m:
    case Some{i}:
      List.get(&2, T.Bt, fd.bts(fd.items(fd.go(V.sv.at(c, 3n), KTys{}, env))), i)
    case None{}:
      rest

def fd.selty(cs: X.Sx, +f: List<&2, U32>, +env: Env) -> Maybe<&2, T.Bt>:
  match cs:
    case X.SxCons{+c, t}:
      fd.selty.of(fd.fpos(fd.fnames(V.sv.at(c, 2n)), f, 0n), c, fd.selty(t, f, env), env)
    case _:
      None{}

def fd.sel.item(+ty: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, +f: List<&2, U32>, cs: Maybe<&2, T.Bt>, rt: Maybe<&2, T.Bt>) -> List<&2, Got>:
  match cs rt:
    case Some{c} Some{r}:
      +x = S.b("x")
      +p = {T.BParam{T.BmLive{}, x, T.BtTyApp{fd.tyname(ty), T.tba.args(fd.tvbts(tvs))}} : T.BParam}
      fd.got.def(f, T.BiDef{fd.vname(f), List.append(&2, T.BParam, fd.tvparams(tvs), p <> Nil{}), r, T.BtMatch{T.tba.args([T.BtVar{x}]), c}, Nil{}}) <> Nil{}
    case _ _:
      Nil{}

def fd.sels.go(+ty: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, +cs: X.Sx, fs: List<&2, List<&2, U32>>, +env: Env) -> List<&2, Got>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> t:
      List.append(&2, Got, fd.sel.item(ty, tvs, f, fd.selcases(ty, cs, f), fd.selty(cs, f, env)), fd.sels.go(ty, tvs, cs, t, env))

# (data NAME (TV...) (CON...) SPAN)
def fd.sels(+x: X.Sx, +env: Env) -> List<&2, Got>:
  +cs = V.sv.at(x, 3n)
  fd.sels.go(V.sv.str(x, 1n), fd.tvs(V.sv.at(x, 2n)), cs, fd.allf(cs, Nil{}), env)

# the module's data types; one with a field type the fold cannot write is
# out, with that type as the reason, like a def
# the type's ==: T.eq when its Eq instance is derived, out when written
# by hand (pruned when nothing uses it), none when it has no Eq instance
def fd.eq.got(drv: Bool, ins: Bool, +it: T.BItem) -> List<&2, Got>:
  match drv ins:
    case True{} _:
      [fd.got.def(fd.eq.iname(it), fd.eq.def(it))]
    case False{} True{}:
      [GotOut{fd.eq.iname(it), S.b("fold:eq-instance")}]
    case False{} False{}:
      Nil{}

# a let's name without the + fd.mark gave it
def fd.unplus(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case 43 <> t:
      t
    case u:
      u

# ns without the names in xs, in front of acc
def fd.less.vs(+xs: List<&2, List<&2, U32>>, ns: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case +n <> t:
      T.tba.keep(S.mem(n, xs), n, fd.less.vs(xs, t, acc))
    case Nil{}:
      acc

# The names a term mentions from outside it: tba.frees, less what its
# cases' patterns bind, and with what its matches scrutinize. A template
# argument `x0 => match x0: case Tuple{t, Sigma{_, ty}}: ..` names neither
# t nor ty (tba.frees keeps a case's binders in), so neither a parameter
# named t becomes a template nor is a def that binds a t elsewhere out
# (fold:closure-argument), as EAL's selfReferential was.
def fd.sfrees(t: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtCase{p, b, rest}:
      fd.less.vs(T.tba.pvars(p, Nil{}), fd.sfrees(b, Nil{}), fd.sfrees(rest, acc))
    case T.BtMatch{xs, cs}:
      T.tba.refs(xs, fd.sfrees(cs, acc))
    case T.BtRw{e, p, b}:
      fd.sfrees(e, fd.sfrees(p, fd.sfrees(b, acc)))
    case T.BtLet{x, v, b}:
      fd.sfrees(v, T.tba.less(fd.unplus(x), fd.sfrees(b, Nil{}), acc))
    case T.BtDead{a}:
      fd.sfrees(a, acc)
    case T.BtVar{x}:
      x <> acc
    case T.BtApp{f, a}:
      fd.sfrees(f, fd.sfrees(a, acc))
    case T.BtTplArg{a}:
      fd.sfrees(a, acc)
    case T.BtLam{m, x, b}:
      T.tba.less(x, fd.sfrees(b, Nil{}), acc)
    case T.BtPi{m, x, d, a, b}:
      fd.sfrees(a, T.tba.less(x, fd.sfrees(b, Nil{}), acc))
    case T.BtCon{c, a}:
      c <> fd.sfrees(a, acc)
    case T.BtTyApp{n, a}:
      n <> fd.sfrees(a, acc)
    case T.BtEq{ty, a, b}:
      fd.sfrees(ty, fd.sfrees(a, fd.sfrees(b, acc)))
    case T.BtSucc{a}:
      fd.sfrees(a, acc)
    case T.BtAnn{a, ty}:
      fd.sfrees(a, fd.sfrees(ty, acc))
    case T.BtExpr{e}:
      fd.sfrees(e, acc)
    case T.BtArgs{a, rest}:
      fd.sfrees(a, fd.sfrees(rest, acc))
    case _:
      acc

# an eq out (fold:eq-...) that nothing uses goes
# the names the template arguments in t use
def fd.tas(t: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtTplArg{a}:
      fd.sfrees(a, acc)
    case T.BtRw{e, p, b}:
      fd.tas(e, fd.tas(p, fd.tas(b, acc)))
    case T.BtLet{x, v, b}:
      fd.tas(v, fd.tas(b, acc))
    case T.BtDead{a}:
      fd.tas(a, acc)
    case T.BtApp{f, a}:
      fd.tas(f, fd.tas(a, acc))
    case T.BtLam{m, x, b}:
      fd.tas(b, acc)
    case T.BtPi{m, x, d, a, b}:
      fd.tas(a, fd.tas(b, acc))
    case T.BtCon{c, a}:
      fd.tas(a, acc)
    case T.BtTyApp{n, a}:
      fd.tas(a, acc)
    case T.BtEq{ty, a, b}:
      fd.tas(ty, fd.tas(a, fd.tas(b, acc)))
    case T.BtSucc{a}:
      fd.tas(a, acc)
    case T.BtAnn{a, ty}:
      fd.tas(a, fd.tas(ty, acc))
    case T.BtMatch{xs, cs}:
      fd.tas(xs, fd.tas(cs, acc))
    case T.BtExpr{e}:
      fd.tas(e, acc)
    case T.BtCase{p, b, rest}:
      fd.tas(b, fd.tas(rest, acc))
    case T.BtArgs{a, rest}:
      fd.tas(a, fd.tas(rest, acc))
    case _:
      acc

def fd.got.items(gs: List<&2, Got>) -> List<&2, T.BItem>:
  match gs:
    case GotDef{n, it} <> t:
      it <> fd.got.items(t)
    case _ <> t:
      fd.got.items(t)
    case Nil{}:
      Nil{}

def fd.eq.prune(gs: List<&2, Got>, +its: List<&2, T.BItem>) -> List<&2, Got>:
  match gs:
    case Nil{}:
      Nil{}
    case GotOut{+n, +w} <> t:
      +rest = fd.eq.prune(t, its)
      Bool.pick(List<&2, Got>, Bool.and(S.suffix(n, S.b(".eq")), Bool.and(S.prefix(w, S.b("fold:eq-")), Bool.not(fd.uses.name(its, n)))), rest, GotOut{n, w} <> rest)
    case g <> t:
      g <> fd.eq.prune(t, its)

def fd.twin.isx(m: Maybe<&2, T.Bt>, +x: List<&2, U32>) -> Bool:
  match m:
    case Some{T.BtVar{v}}:
      S.eq(v, x)
    case _:
      False{}

# Base's types and the prelude's, which have no twin
def fd.twin.base(+n: List<&2, U32>) -> Bool:
  Bool.or(Bool.or(Bool.or(fd.is(n, "List"), fd.is(n, "Maybe")), Bool.or(fd.is(n, "Either"), fd.is(n, "Sigma"))), S.prefix(n, S.b("HsPrelude.")))

# A type's twin (see Twins), when its fields allow one: a field of the last
# variable x is itself, one of another of the package's types at x (x its
# last argument, alone) that type's twin, one without x unchanged; another
# (a list, a pair, a Maybe of x) none.
def fd.twin.at(+x: List<&2, U32>, ty: T.Bt) -> Maybe<&2, T.Bt>:
  match ty:
    case T.BtVar{+v}:
      Some{T.BtVar{v}}
    case T.BtTyApp{+n, +args}:
      +sp = fd.spine(args)
      +pre = fd.init(sp)
      +last = List.last(&2, T.Bt, sp)
      +free = S.mem(x, T.tba.frees(T.BtTyApp{n, args}, Nil{}))
      +lastx = Bool.and(fd.twin.isx(last, x), Bool.not(fd.twin.base(n)))
      +prex = S.mem(x, T.tba.frees(T.BtTyApp{n, T.tba.args(pre)}, Nil{}))
      Bool.pick(Maybe<&2, T.Bt>, Bool.not(free), Some{T.BtTyApp{n, args}}, Bool.pick(Maybe<&2, T.Bt>, Bool.and(lastx, Bool.not(prex)), Some{T.BtTyApp{fd.cat(n, S.b(".fn")), args}}, None{}))
    case +t:
      Bool.pick(Maybe<&2, T.Bt>, S.mem(x, T.tba.frees(t, Nil{})), None{}, Some{t})

def fd.twin.fcons(f: List<&2, U32>, h: Maybe<&2, T.Bt>, t: Maybe<&2, List<&2, T.BField>>) -> Maybe<&2, List<&2, T.BField>>:
  match h t:
    case Some{ty} Some{fs}:
      Some{T.BField{f, ty} <> fs}
    case _ _:
      None{}

def fd.twin.fields(+x: List<&2, U32>, fs: List<&2, T.BField>) -> Maybe<&2, List<&2, T.BField>>:
  match fs:
    case Nil{}:
      Some{Nil{}}
    case T.BField{f, ty} <> t:
      fd.twin.fcons(f, fd.twin.at(x, ty), fd.twin.fields(x, t))

def fd.twin.ccons(c: List<&2, U32>, h: Maybe<&2, List<&2, T.BField>>, t: Maybe<&2, List<&2, T.BCtor>>) -> Maybe<&2, List<&2, T.BCtor>>:
  match h t:
    case Some{fs} Some{cs}:
      Some{T.BCtor{c, fs} <> cs}
    case _ _:
      None{}

def fd.twin.ctors(+x: List<&2, U32>, cs: List<&2, T.BCtor>) -> Maybe<&2, List<&2, T.BCtor>>:
  match cs:
    case Nil{}:
      Some{Nil{}}
    case T.BCtor{+c, fs} <> t:
      fd.twin.ccons(fd.cfn(c), fd.twin.fields(x, fs), fd.twin.ctors(x, t))

# the parameters, the last a Type
def fd.twin.ps(ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match ps:
    case T.BParam{m, x, ty} <> Nil{}:
      T.BParam{m, x, fd.v("Type")} <> Nil{}
    case p <> t:
      p <> fd.twin.ps(t)
    case Nil{}:
      Nil{}

def fd.twin.last(ps: List<&2, T.BParam>) -> List<&2, U32>:
  match ps:
    case T.BParam{m, x, ty} <> Nil{}:
      x
    case p <> t:
      fd.twin.last(t)
    case Nil{}:
      Nil{}

def fd.twin.got(+n: List<&2, U32>, +b: List<&2, U32>, ps: List<&2, T.BParam>, m: Maybe<&2, List<&2, T.BCtor>>) -> List<&2, Got>:
  match m:
    case Some{cs}:
      [fd.got.def(fd.cat(n, S.b(".fn")), T.BiType{fd.cat(b, S.b(".fn")), fd.twin.ps(ps), fd.v("Type"), cs, [fd.cat(S.b("generated: the twin of "), b), S.b("(its last variable a function: a layer of a monad's actions)")]})]
    case None{}:
      Nil{}

def fd.twin(+n: List<&2, U32>, ty: T.BItem) -> List<&2, Got>:
  match ty:
    case T.BiType{+b, +ps, k, cs, d}:
      +x = fd.twin.last(ps)
      Bool.pick(List<&2, Got>, Nat.is_eq(S.len(x), 0n), Nil{}, fd.twin.got(n, b, ps, fd.twin.ctors(x, cs)))
    case _:
      Nil{}

def fd.datas.if(d: Bool, +x: X.Sx, +drv: List<&2, List<&2, U32>>, +ins: List<&2, List<&2, U32>>, +env: Env, acc: List<&2, Got>) -> List<&2, Got>:
  match d:
    case True{}:
      +n = V.sv.str(x, 1n)
      +ty = fd.data(x, env)
      fd.got.def(n, ty) <> List.append(&2, Got, fd.twin(n, ty), List.append(&2, Got, fd.sels(x, env), List.append(&2, Got, fd.eq.got(S.mem(n, drv), S.mem(n, ins), ty), acc)))
    case False{}:
      acc

def fd.datas.go(xs: List<&2, X.Sx>, +drv: List<&2, List<&2, U32>>, +ins: List<&2, List<&2, U32>>, +env: Env) -> List<&2, Got>:
  match xs:
    case +h <> t:
      fd.datas.if(fd.isdata(h), h, drv, ins, env, fd.datas.go(t, drv, ins, env))
    case Nil{}:
      Nil{}

# the module's types, their selectors and their ==
def fd.datas(+xs: List<&2, X.Sx>, +env: Env) -> List<&2, Got>:
  fd.datas.go(xs, fd.eq.drv(xs), fd.eq.ins(xs), env)

def fd.lift.iname(it: T.BItem) -> List<&2, U32>:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      n
    case _:
      S.b("?")

# a binding's def and the defs lifted out of it (last the binding's own):
# each a GotDef, the lifted ones by their own names; or, for the first
# place one could not fill, the binding out
def fd.got.lifted(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, Got>:
  match its:
    case it <> Nil{}:
      GotDef{n, it} <> Nil{}
    case +it <> t:
      GotDef{fd.lift.iname(it), it} <> fd.got.lifted(t, n)
    case Nil{}:
      Nil{}

def fd.todos.all(its: List<&2, T.BItem>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match its:
    case it <> t:
      fd.todos.all(t, T.tba.item.fold(~T.tba.todos, it, acc))
    case Nil{}:
      acc

def fd.got.defs.of(todos: List<&2, List<&2, U32>>, +n: List<&2, U32>, its: List<&2, T.BItem>) -> List<&2, Got>:
  match todos:
    case Nil{}:
      fd.got.lifted(its, n)
    case w <> t:
      GotOut{n, w} <> Nil{}

def fd.got.defs(+n: List<&2, U32>, +its: List<&2, T.BItem>) -> List<&2, Got>:
  fd.got.defs.of(List.reverse(&2, List<&2, U32>, fd.todos.all(its, Nil{})), n, its)

def fd.got.of(ok: Bool, tb: Tb, +env: Env) -> List<&2, Got>:
  match ok tb:
    case True{} TbFun{+n, +tvs, f}:
      fd.got.defs(n, fd.def(n, tvs, fd.go(V.sv.at(f, 4n), KMatches{}, fd.withself(env, fd.tvbts(tvs)))))
    case True{} TbNo{n, why}:
      GotOut{n, why} <> Nil{}
    case False{} TbFun{n, tvs, f}:
      GotOut{n, S.b("survey")} <> Nil{}
    case False{} TbNo{n, why}:
      GotOut{n, S.b("survey")} <> Nil{}
    case _ _:
      GotOut{S.b("?"), S.b("fold:skip")} <> Nil{}

def fd.tb.name(tb: Tb) -> List<&2, U32>:
  match tb:
    case TbFun{n, tvs, f}:
      n
    case TbNo{n, w}:
      n
    case TbSkip{}:
      S.b("?")

# whether the binding is one a user wrote (not GHC's $-names; a pattern
# synonym's builder $bX is kept: a def other modules call)
def fd.tb.user(+tb: Tb) -> Bool:
  Bool.not(V.sv.dollar.out(fd.tb.name(tb)))

def fd.gots.if(user: Bool, +ok: List<&2, List<&2, U32>>, +tb: Tb, +env: Env, acc: List<&2, Got>) -> List<&2, Got>:
  match user:
    case True{}:
      List.append(&2, Got, fd.got.of(S.mem(fd.tb.name(tb), ok), tb, env), acc)
    case False{}:
      acc

def fd.gots(tbs: List<&2, Tb>, +ok: List<&2, List<&2, U32>>, +env: Env) -> List<&2, Got>:
  match tbs:
    case +h <> t:
      fd.gots.if(fd.tb.user(h), ok, h, env, fd.gots(t, ok, env))
    case Nil{}:
      Nil{}

# the names of the items, written or out (a type's, a selector's)
def fd.got.defnames(gs: List<&2, Got>) -> List<&2, List<&2, U32>>:
  match gs:
    case GotDef{n, it} <> t:
      n <> fd.got.defnames(t)
    case GotOut{n, w} <> t:
      n <> fd.got.defnames(t)
    case Nil{}:
      Nil{}

def fd.got.n(+g: Got) -> List<&2, U32>:
  match g:
    case GotDef{n, it}:
      n
    case GotOut{n, w}:
      n

# the bindings, less those the data types already wrote: GHC exports a
# record's selectors as bindings of their own, which the survey refuses
def fd.gots.less.if(dup: Bool, h: Got, rest: List<&2, Got>) -> List<&2, Got>:
  match dup:
    case True{}:
      rest
    case False{}:
      h <> rest

def fd.gots.less(gs: List<&2, Got>, +names: List<&2, List<&2, U32>>) -> List<&2, Got>:
  match gs:
    case +h <> t:
      fd.gots.less.if(S.mem(fd.got.n(h), names), h, fd.gots.less(t, names))
    case Nil{}:
      Nil{}

# The survey's verdict --------------------------------------------------------------

# the names the survey puts in the first version (Survey.bend's sv.module.ok)
def fd.ok(+xs: List<&2, X.Sx>, +imp: V.Imp) -> List<&2, List<&2, U32>>:
  +tb = V.sv.tb()
  +m = V.sv.modname(xs)
  +bad = V.sv.tys(xs, V.Env{m, tb, Nil{}, imp}, Nil{})
  +fs0 = V.sv.tops(xs, V.Env{m, tb, bad, imp}, Nil{})
  +all = V.sv.names(fs0)
  V.sv.ok.fix(1n+List.length(&2, V.Fn, fs0), False{}, fs0, all, all)

# Recursion schemes ---------------------------------------------------------------
#
# A functor of the module is a data type with a Functor instance in it; Fix
# and Cofree recurse through its last type variable.  Each field of its
# constructors is copied (its type has no such variable), recursed into
# (it is the variable), or taken apart: a Maybe, a pair, or a functor of
# the package applied to the variable last (StuckExprB (BasicExprF f)).
# For each, G.cata and G.cata.cofree are written: Data.Functor.Foldable's
# cata at Fix G and at Cofree G w, as nested matches down to the variable,
# where Bend sees the argument shrink (it does not see it through a
# template such as an fmap).

# whether the type x names the type variable f
def fd.has.tv(x: X.Sx, +f: List<&2, U32>) -> Bool:
  match x:
    case X.SxCons{X.SxAtom{a}, X.SxCons{X.SxStr{n}, X.SxNil{}}}:
      Bool.and(fd.is(a, "tv"), S.eq(n, f))
    case X.SxCons{h, t}:
      Bool.or(fd.has.tv(h, f), fd.has.tv(t, f))
    case _:
      False{}

def fd.fr.one(+key: List<&2, U32>, +r: Fr) -> Fr:
  match r:
    case FrCopy{}:
      FrCopy{}
    case FrRec{}:
      Bool.pick(Fr, fd.is(key, "GHC.Internal.Maybe.Maybe"), FrMaybe{FrRec{}}, Bool.pick(Fr, fd.is(key, "GHC.Types.List"), FrList{FrRec{}}, FrIn{key}))
    case r1:
      Bool.pick(Fr, fd.is(key, "GHC.Internal.Maybe.Maybe"), FrMaybe{r1}, Bool.pick(Fr, fd.is(key, "GHC.Types.List"), FrList{r1}, FrNo{}))

def fd.fr.two(+key: List<&2, U32>, r1: Fr, r2: Fr) -> Fr:
  match r1 r2:
    case FrCopy{} FrCopy{}:
      FrCopy{}
    case FrCopy{} FrRec{}:
      Bool.pick(Fr, fd.is(key, "GHC.Tuple.Tuple2"), FrPair{FrCopy{}, FrRec{}}, FrIn{key})
    case a b:
      Bool.pick(Fr, fd.is(key, "GHC.Tuple.Tuple2"), FrPair{a, b}, FrNo{})

def fd.fr.three(+key: List<&2, U32>, r1: Fr, r2: Fr, r3: Fr) -> Fr:
  match r1 r2 r3:
    case FrCopy{} FrCopy{} FrCopy{}:
      FrCopy{}
    case FrCopy{} FrCopy{} FrRec{}:
      FrIn{key}
    case _ _ _:
      FrNo{}

def fd.fr.fun(r1: Fr, r2: Fr) -> Fr:
  match r1 r2:
    case FrCopy{} FrCopy{}:
      FrCopy{}
    case _ _:
      FrNo{}

# the role of a field of type x, for the functor's variable f
def fd.fr(x: X.Sx, +f: List<&2, U32>) -> Fr:
  match x:
    case X.SxCons{X.SxAtom{a}, X.SxCons{X.SxStr{n}, X.SxNil{}}}:
      Bool.pick(Fr, Bool.and(fd.is(a, "tv"), S.eq(n, f)), FrRec{}, FrCopy{})
    case X.SxCons{_, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, X.SxNil{}}}}:
      FrCopy{}
    case X.SxCons{_, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, X.SxCons{p, X.SxNil{}}}}}:
      fd.fr.one(fd.cat3(m, S.b("."), n), fd.fr(p, f))
    case X.SxCons{_, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, X.SxCons{p, X.SxCons{q, X.SxNil{}}}}}}:
      fd.fr.two(fd.cat3(m, S.b("."), n), fd.fr(p, f), fd.fr(q, f))
    case X.SxCons{_, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, X.SxCons{p, X.SxCons{q, X.SxCons{s, X.SxNil{}}}}}}}:
      fd.fr.three(fd.cat3(m, S.b("."), n), fd.fr(p, f), fd.fr(q, f), fd.fr(s, f))
    case X.SxCons{_, X.SxCons{p, X.SxCons{q, X.SxNil{}}}}:
      fd.fr.fun(fd.fr(p, f), fd.fr(q, f))
    case +y:
      Bool.pick(Fr, fd.has.tv(y, f), FrNo{}, FrCopy{})

def fd.frs(xs: X.Sx, +f: List<&2, U32>) -> List<&2, Fr>:
  match xs:
    case X.SxCons{h, t}:
      fd.fr(h, f) <> fd.frs(t, f)
    case _:
      Nil{}

# (con NAME (FIELD...) (ARGTYPE...) (ex NEX NTHETA))
def fd.fcs(+ty: List<&2, U32>, +f: List<&2, U32>, cs: X.Sx) -> List<&2, Fc>:
  match cs:
    case X.SxCons{+c, t}:
      Fc{fd.cname(ty, V.sv.str(c, 1n)), fd.frs(V.sv.at(c, 3n), f)} <> fd.fcs(ty, f, t)
    case _:
      Nil{}

# the last of the (TV...) of a data type, as Haskell names it
def fd.lasttv(xs: X.Sx, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case X.SxCons{X.SxStr{s}, t}:
      fd.lasttv(t, s)
    case _:
      acc

def fd.inits.go(t: List<&2, List<&2, U32>>, h: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match t:
    case Nil{}:
      Nil{}
    case h2 <> t2:
      h <> fd.inits.go(t2, h2)

def fd.inits(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case h <> t:
      fd.inits.go(t, h)
    case Nil{}:
      Nil{}

# (data NAME (TV...) (CON...) SPAN), a functor
def fd.fz.of(+m: List<&2, U32>, +x: X.Sx) -> Fz:
  +n = V.sv.str(x, 1n)
  +tvs = V.sv.at(x, 2n)
  Fz{V.sv.key(m, n), fd.tyname(n), fd.inits(fd.tvs(tvs)), fd.fcs(n, fd.lasttv(tvs, Nil{}), V.sv.at(x, 3n))}

# (instance CLSMOD CLS (TYPE ...) DFUN SPAN) of Functor: its type's key
def fd.fkey.if(f: Bool, +x: X.Sx, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match f:
    case True{}:
      +t = V.sv.at(V.sv.at(x, 3n), 0n)
      V.sv.key(V.sv.str(t, 1n), V.sv.str(t, 2n)) <> acc
    case False{}:
      acc

def fd.fkeys(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case +h <> t:
      fd.fkey.if(Bool.and(V.sv.is(V.sv.hd(h), "instance"), Bool.and(V.sv.is(V.sv.str(h, 1n), "GHC.Internal.Base"), V.sv.is(V.sv.str(h, 2n), "Functor"))), h, fd.fkeys(t))
    case Nil{}:
      Nil{}

def fd.fz.if(f: Bool, +m: List<&2, U32>, +x: X.Sx, acc: List<&2, Fz>) -> List<&2, Fz>:
  match f:
    case True{}:
      fd.fz.of(m, x) <> acc
    case False{}:
      acc

def fd.fzs.go(xs: List<&2, X.Sx>, +m: List<&2, U32>, +ks: List<&2, List<&2, U32>>) -> List<&2, Fz>:
  match xs:
    case +h <> t:
      fd.fz.if(Bool.and(fd.isdata(h), S.mem(V.sv.key(m, V.sv.str(h, 1n)), ks)), m, h, fd.fzs.go(t, m, ks))
    case Nil{}:
      Nil{}

# the module's functors
def fd.fzs(+xs: List<&2, X.Sx>, +m: List<&2, U32>) -> List<&2, Fz>:
  fd.fzs.go(xs, m, fd.fkeys(xs))

# the package's earlier functors
def fd.ix.fzs(xs: List<&2, Ix>) -> List<&2, Fz>:
  match xs:
    case IxFun{k, b, cs} <> t:
      Fz{k, b, Nil{}, cs} <> fd.ix.fzs(t)
    case _ <> t:
      fd.ix.fzs(t)
    case Nil{}:
      Nil{}

def fd.fz.find(xs: List<&2, Fz>, +k: List<&2, U32>) -> Maybe<&2, List<&2, Fc>>:
  match xs:
    case Fz{k2, b, tvs, cs} <> t:
      Bool.pick(Maybe<&2, List<&2, Fc>>, S.eq(k2, k), Some{cs}, fd.fz.find(t, k))
    case Nil{}:
      None{}

# The writing: a walk over work, each a field (its variable, its role), a
# constructor to build of the last n values, or the cases of a match still
# to write; vs are the values built so far, last first.  A field taken apart
# is a match whose cases are written by the same walk (Bend has no mutual
# recursion), each case's body then the cases after it.
type Cw is Data:
  CwF{v: List<&2, U32>, r: Fr}
  CwB{c: List<&2, U32>, n: Nat}
  CwC{v: List<&2, U32>, cs: List<&2, Fc>}

# what the walk writes for: the functors, the recursive call's name and its
# arguments before the value, and whether at Cofree
type Cg is Data:
  Cg{fz: List<&2, Fz>, n: List<&2, U32>, tas: List<&2, T.Bt>, cof: Bool, fn: Bool}

def fd.cg.fz(+c: Cg) -> List<&2, Fz>:
  match c:
    case Cg{fz, n, tas, cof, fn}:
      fz

def fd.cg.call(+c: Cg, +v: List<&2, U32>) -> T.Bt:
  match c:
    case Cg{fz, n, tas, cof, fn}:
      T.tba.call(T.BtVar{n}, List.append(&2, T.Bt, tas, T.BtVar{v} <> Nil{}))

def fd.cg.leaf.of(cof: Bool, fn: Bool, v: T.Bt) -> T.Bt:
  match cof:
    case True{}:
      T.BtExpr{T.tba.call(T.BtVar{S.b("alg")}, [T.BtCon{fd.bpick(fn, S.b("HsPrelude.CofreeF.fn.CofreeF"), S.b("HsPrelude.CofreeF.CofreeF")), T.tba.args([T.BtVar{S.b("w0")}, v])}])}
    case False{}:
      T.BtExpr{T.tba.call(T.BtVar{S.b("alg")}, [v])}

def fd.cg.leaf(+c: Cg, vs: List<&2, T.Bt>) -> T.Bt:
  match c vs:
    case Cg{fz, n, tas, cof, fn} v <> Nil{}:
      fd.cg.leaf.of(cof, fn, v)
    case _ _:
      fd.todo("fold:cata-shape")

# a layer's constructor, at the twin when the cata is (a Maybe's or a
# pair's, Base's, unchanged)
def fd.cg.cname(+c: Cg, +b: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Cg{fz, n, tas, cof, fn}:
      fd.bpick(Bool.and(fn, S.infix(b, S.b("."))), fd.cfn(b), b)

# the constructor c of the last n values
def fd.cg.build(+c: List<&2, U32>, +n: Nat, +vs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  T.BtCon{c, T.tba.args(List.reverse(&2, T.Bt, List.take(&2, T.Bt, vs, n)))} <> List.drop(&2, T.Bt, vs, n)

def fd.cg.ys(n: Nat, +k: Nat) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      fd.cat(S.b("y"), fd.nshow(k)) <> fd.cg.ys(p, 1n+k)

def fd.cg.pvs(ys: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match ys:
    case y <> t:
      T.BtPv{T.BmLive{}, y} <> fd.cg.pvs(t)
    case Nil{}:
      Nil{}

def fd.cg.fields(ys: List<&2, List<&2, U32>>, rs: List<&2, Fr>, rest: List<&2, Cw>) -> List<&2, Cw>:
  match ys rs:
    case y <> t r <> u:
      CwF{y, r} <> fd.cg.fields(t, u, rest)
    case _ _:
      rest

def fd.cg.maybe(r: Fr) -> List<&2, Fc>:
  [Fc{S.b("None"), Nil{}}, Fc{S.b("Some"), [r]}]

def fd.cg.pair(a: Fr, b: Fr) -> List<&2, Fc>:
  [Fc{S.b("Tuple"), [a, b]}]

def fd.cg.match(+v: List<&2, U32>, cases: T.Bt) -> T.Bt:
  T.BtMatch{T.tba.args([T.BtVar{v}]), cases}

def fd.cg.in(m: Maybe<&2, List<&2, Fc>>) -> List<&2, Fc>:
  match m:
    case Some{cs}:
      cs
    case None{}:
      Nil{}

def fd.cg.found(m: Maybe<&2, List<&2, Fc>>) -> Bool:
  match m:
    case Some{cs}:
      True{}
    case None{}:
      False{}

def fd.cg(fuel: Nat, ws: List<&2, Cw>, +vs: List<&2, T.Bt>, +k: Nat, +c: Cg) -> T.Bt:
  match fuel ws:
    case 0n _:
      fd.todo("fold:cata-depth")
    case 1n+p Nil{}:
      fd.cg.leaf(c, vs)
    case 1n+p CwF{+v, FrCopy{}} <> rest:
      fd.cg(p, rest, T.BtVar{v} <> vs, k, c)
    case 1n+p CwF{+v, FrRec{}} <> rest:
      fd.cg(p, rest, fd.cg.call(c, v) <> vs, k, c)
    case 1n+p CwF{+v, FrIn{key}} <> rest:
      +m = fd.fz.find(fd.cg.fz(c), key)
      Bool.pick(T.Bt, fd.cg.found(m), fd.cg.match(v, fd.cg(p, CwC{v, fd.cg.in(m)} <> rest, vs, k, c)), fd.todo("fold:cata-functor"))
    case 1n+p CwF{+v, FrMaybe{r}} <> rest:
      fd.cg.match(v, fd.cg(p, CwC{v, fd.cg.maybe(r)} <> rest, vs, k, c))
    case 1n+p CwF{+v, FrPair{a, b}} <> rest:
      fd.cg.match(v, fd.cg(p, CwC{v, fd.cg.pair(a, b)} <> rest, vs, k, c))
    case 1n+p CwF{v, FrNo{}} <> rest:
      fd.todo("fold:cata-field")
    case 1n+p CwF{v, FrList{r}} <> rest:
      fd.todo("fold:cata-list")
    case 1n+p CwB{+b, +n} <> rest:
      fd.cg(p, rest, fd.cg.build(fd.cg.cname(c, b), n, vs), k, c)
    case 1n+p CwC{v, Nil{}} <> rest:
      T.BtCEnd{}
    case 1n+(+p) CwC{+v, Fc{+b, +rs} <> more} <> +rest:
      +n = List.length(&2, Fr, rs)
      +ys = fd.cg.ys(n, k)
      T.BtCase{T.tba.args([T.BtCon{b, T.tba.args(fd.cg.pvs(ys))}]), fd.cg(p, fd.cg.fields(ys, rs, CwB{b, n} <> rest), vs, Nat.add(k, n), c), fd.cg(p, CwC{v, more} <> rest, vs, k, c)}

# whether a role is flat: copied, recursed into, or a Maybe or pair of those
def fd.fr.flat(r: Fr) -> Bool:
  match r:
    case FrCopy{}:
      True{}
    case FrRec{}:
      True{}
    case FrMaybe{a}:
      fd.fr.flat(a)
    case FrPair{a, b}:
      Bool.and(fd.fr.flat(a), fd.fr.flat(b))
    case _:
      False{}

def fd.frs.flat(rs: List<&2, Fr>) -> Bool:
  match rs:
    case r <> t:
      Bool.and(fd.fr.flat(r), fd.frs.flat(t))
    case Nil{}:
      True{}

def fd.fcs.flat(cs: List<&2, Fc>) -> Bool:
  match cs:
    case Fc{c, rs} <> t:
      Bool.and(fd.frs.flat(rs), fd.fcs.flat(t))
    case Nil{}:
      True{}

# a functor H the role takes apart must be another one, and flat (one
# level: StuckExprF's BasicExprF), so the nested matches end
def fd.in.ok(m: Maybe<&2, List<&2, Fc>>, +own: List<&2, U32>, +key: List<&2, U32>) -> Bool:
  match m:
    case Some{cs}:
      Bool.and(Bool.not(S.eq(own, key)), fd.fcs.flat(cs))
    case None{}:
      False{}

def fd.fr.ok(r: Fr, +own: List<&2, U32>, +fz: List<&2, Fz>) -> Bool:
  match r:
    case FrNo{}:
      False{}
    case FrList{a}:
      False{}
    case FrIn{+key}:
      fd.in.ok(fd.fz.find(fz, key), own, key)
    case FrMaybe{a}:
      fd.fr.ok(a, own, fz)
    case FrPair{a, b}:
      Bool.and(fd.fr.ok(a, own, fz), fd.fr.ok(b, own, fz))
    case _:
      True{}

def fd.fc.ok(rs: List<&2, Fr>, +own: List<&2, U32>, +fz: List<&2, Fz>) -> Bool:
  match rs:
    case r <> t:
      Bool.and(fd.fr.ok(r, own, fz), fd.fc.ok(t, own, fz))
    case Nil{}:
      True{}

def fd.fz.ok(cs: List<&2, Fc>, +own: List<&2, U32>, +fz: List<&2, Fz>) -> Bool:
  match cs:
    case Fc{c, rs} <> t:
      Bool.and(fd.fc.ok(rs, own, fz), fd.fz.ok(t, own, fz))
    case Nil{}:
      True{}

def fd.cata.doc(cof: Bool, +b: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match cof:
    case True{}:
      [fd.cat3(S.b("generated: Data.Functor.Foldable.cata at Cofree "), b, S.b(" w (Base: CofreeF)"))]
    case False{}:
      [fd.cat(S.b("generated: Data.Functor.Foldable.cata at Fix "), b)]

# G.cata (cof False) or G.cata.cofree (cof True); at a function, a monad's
# action (fn True), G.cata.fn or G.cata.cofree.fn, the layer G's twin
def fd.cata.def(+cof: Bool, +fn: Bool, z: Fz, +fz: List<&2, Fz>) -> T.BItem:
  match z:
    case Fz{k, +b, +tvs, +cs}:
      +name = fd.cat3(b, fd.bpick(cof, S.b(".cata.cofree"), S.b(".cata")), fd.bpick(fn, S.b(".fn"), Nil{}))
      +tas = fd.tvbts(tvs)
      +lam = {T.BtLam{T.BmLive{}, fd.rv(), T.BtTyApp{b, T.tba.args(List.append(&2, T.Bt, tas, T.BtVar{fd.rv()} <> Nil{}))}} : T.Bt}
      +bl = fd.bpick(fn, fd.cat(b, S.b(".fn")), b)
      +laml = {T.BtLam{T.BmLive{}, fd.rv(), T.BtTyApp{bl, T.tba.args(List.append(&2, T.Bt, tas, T.BtVar{fd.rv()} <> Nil{}))}} : T.Bt}
      +r = {T.BtVar{S.b("R_c")} : T.Bt}
      +w = {T.BtVar{S.b("W_c")} : T.Bt}
      +layer = Bool.pick(T.Bt, cof, T.BtTyApp{fd.bpick(fn, S.b("HsPrelude.CofreeF.fn"), S.b("HsPrelude.CofreeF")), T.tba.args([laml, w, r])}, T.BtTyApp{bl, T.tba.args(List.append(&2, T.Bt, tas, r <> Nil{}))})
      +xty = Bool.pick(T.Bt, cof, T.BtTyApp{S.b("HsPrelude.Cofree"), T.tba.args([lam, w])}, T.BtTyApp{S.b("HsPrelude.Fix"), T.tba.args([lam])})
      +wp = Bool.pick(List<&2, T.BParam>, cof, [T.BParam{T.BmTpl{}, S.b("W_c"), fd.v("Data")}], Nil{})
      +ps = List.append(&2, T.BParam, fd.tvtpls(tvs), List.append(&2, T.BParam, wp, [T.BParam{T.BmTpl{}, S.b("R_c"), Bool.pick(T.Bt, fn, fd.v("Type"), fd.v("Data"))}, T.BParam{T.BmTpl{}, S.b("alg"), T.BtPi{T.BmLive{}, S.b("_"), False{}, layer, r}}, T.BParam{T.BmLive{}, S.b("x"), xty}]))
      +targs = fd.tpls(List.append(&2, T.Bt, tas, List.append(&2, T.Bt, Bool.pick(List<&2, T.Bt>, cof, [w], Nil{}), [r, T.BtVar{S.b("alg")}])))
      +pat = Bool.pick(T.Bt, cof, T.BtCon{S.b("HsPrelude.Cofree.Cofree"), T.tba.args([T.BtPv{T.BmLive{}, S.b("w0")}, T.BtPv{T.BmLive{}, S.b("y0")}])}, T.BtCon{S.b("HsPrelude.Fix.Fix"), T.tba.args([T.BtPv{T.BmLive{}, S.b("y0")}])})
      +inner = fd.cg(4096n, CwC{S.b("y0"), cs} <> Nil{}, Nil{}, 1n, Cg{fz, name, targs, cof, fn})
      T.BiDef{name, ps, r, T.BtMatch{T.tba.args([T.BtVar{S.b("x")}]), T.BtCase{T.tba.args([pat]), fd.cg.match(S.b("y0"), inner), T.BtCEnd{}}}, fd.cata.doc(cof, b)}

def fd.fz.k(z: Fz) -> List<&2, U32>:
  match z:
    case Fz{k, b, tvs, cs}:
      k

def fd.fz.b(z: Fz) -> List<&2, U32>:
  match z:
    case Fz{k, b, tvs, cs}:
      b

# whether a functor has a twin: its fields copied, recursed into, or another
# functor at the recursive variable (no Maybe, pair or list of it)
def fd.fr.twin(rs: List<&2, Fr>) -> Bool:
  match rs:
    case FrCopy{} <> t:
      fd.fr.twin(t)
    case FrRec{} <> t:
      fd.fr.twin(t)
    case FrIn{k} <> t:
      fd.fr.twin(t)
    case Nil{}:
      True{}
    case _:
      False{}

def fd.fc.twin(cs: List<&2, Fc>) -> Bool:
  match cs:
    case Fc{c, rs} <> t:
      Bool.and(fd.fr.twin(rs), fd.fc.twin(t))
    case Nil{}:
      True{}

def fd.fz.twin(z: Fz) -> Bool:
  match z:
    case Fz{k, b, tvs, cs}:
      fd.fc.twin(cs)

def fd.cata.got(ok: Bool, +z: Fz, +fz: List<&2, Fz>) -> List<&2, Got>:
  match ok:
    case True{}:
      +b = fd.fz.b(z)
      +base = {[fd.got.def(fd.cat(b, S.b(".cata")), fd.cata.def(False{}, False{}, z, fz)), fd.got.def(fd.cat(b, S.b(".cata.cofree")), fd.cata.def(True{}, False{}, z, fz))] : List<&2, Got>}
      +fns = {[fd.got.def(fd.cat(b, S.b(".cata.fn")), fd.cata.def(False{}, True{}, z, fz)), fd.got.def(fd.cat(b, S.b(".cata.cofree.fn")), fd.cata.def(True{}, True{}, z, fz))] : List<&2, Got>}
      List.append(&2, Got, base, Bool.pick(List<&2, Got>, fd.fz.twin(z), fns, Nil{}))
    case False{}:
      Nil{}

def fd.fz.cs(z: Fz) -> List<&2, Fc>:
  match z:
    case Fz{k, b, tvs, cs}:
      cs

def fd.catas.go(zs: List<&2, Fz>, +fz: List<&2, Fz>) -> List<&2, Got>:
  match zs:
    case +z <> t:
      List.append(&2, Got, fd.cata.got(fd.fz.ok(fd.fz.cs(z), fd.fz.k(z), fz), z, fz), fd.catas.go(t, fz))
    case Nil{}:
      Nil{}

# the cata defs of the module's functors
def fd.catas(+xs: List<&2, X.Sx>, +env: Env) -> List<&2, Got>:
  +own = fd.fzs(xs, fd.env.m(env))
  fd.catas.go(own, List.append(&2, Fz, own, fd.ix.fzs(fd.env.ix(env))))

# the data types (and their selectors), then the bindings
# a generated T.eq Bend refuses: one that calls itself inside a template
# argument (T nested in a list or a Maybe of its own: Bend sees no
# decreasing call), or one that calls a U.eq calling it back (Bend takes
# no mutual recursion)
def fd.eq.isgen(it: T.BItem) -> Bool:
  match it:
    case T.BiDef{n, ps, r, b, d <> t}:
      S.prefix(d, S.b("generated: Eq's == at "))
    case _:
      False{}

def fd.eq.body(it: T.BItem) -> T.Bt:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      b
    case _:
      T.BtWild{}

def fd.eq.find(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, T.BItem>:
  match its:
    case +h <> t:
      Bool.pick(List<&2, T.BItem>, S.eq(fd.lift.iname(h), n), [h], fd.eq.find(t, n))
    case Nil{}:
      Nil{}

# whether one of the defs ms (not n itself) calls n
def fd.eq.back(ms: List<&2, List<&2, U32>>, +n: List<&2, U32>, +its: List<&2, T.BItem>) -> Bool:
  match ms:
    case +m <> t:
      Bool.or(Bool.and(Bool.not(S.eq(m, n)), Bool.and(S.suffix(m, S.b(".eq")), fd.uses.name(fd.eq.find(its, m), n))), fd.eq.back(t, n, its))
    case Nil{}:
      False{}

def fd.eq.why(+n: List<&2, U32>, +it: T.BItem, +its: List<&2, T.BItem>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, S.mem(n, fd.tas(fd.eq.body(it), Nil{})), S.b("fold:eq-nested"), Bool.pick(List<&2, U32>, fd.eq.back(T.tba.item.fold(~T.tba.refs, it, Nil{}), n, its), S.b("fold:eq-mutual"), Nil{}))

def fd.eq.check(gen: Bool, +n: List<&2, U32>, +it: T.BItem, +its: List<&2, T.BItem>) -> Got:
  match gen:
    case True{}:
      +w = fd.eq.why(n, it, its)
      Bool.pick(Got, List.is_empty(&2, U32, w), GotDef{n, it}, GotOut{n, w})
    case False{}:
      GotDef{n, it}

def fd.eq.fix(gs: List<&2, Got>, +its: List<&2, T.BItem>) -> List<&2, Got>:
  match gs:
    case Nil{}:
      Nil{}
    case GotDef{+n, +it} <> t:
      fd.eq.check(fd.eq.isgen(it), n, it, its) <> fd.eq.fix(t, its)
    case g <> t:
      g <> fd.eq.fix(t, its)

# the Bend names of an earlier module's defs the package has
def fd.ix.defs(xs: List<&2, Ix>) -> List<&2, List<&2, U32>>:
  match xs:
    case IxDef{k, b, a} <> t:
      b <> fd.ix.defs(t)
    case _ <> t:
      fd.ix.defs(t)
    case Nil{}:
      Nil{}

# an == (some T.eq) the item calls that is neither the module's nor an
# earlier module's (that module's T.eq is out) nor HsPrelude's: its name,
# or none
def fd.eq.missing(rs: List<&2, List<&2, U32>>, +have: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match rs:
    case +r <> t:
      +miss = Bool.and(S.suffix(r, S.b(".eq")), Bool.and(Bool.not(Bool.or(S.prefix(r, S.b("hs.eq.")), S.prefix(r, S.b("HsPrelude.")))), Bool.not(S.mem(r, have))))
      fd.bpicks(miss, [r], fd.eq.missing(t, have))
    case Nil{}:
      Nil{}

def fd.eq.imp.check(miss: List<&2, List<&2, U32>>, +n: List<&2, U32>, +it: T.BItem) -> Got:
  match miss:
    case Nil{}:
      GotDef{n, it}
    case m <> t:
      GotOut{n, fd.cat(S.b("fold:eq-imported:"), m)}

# what calls an earlier module's T.eq that module has not is out
def fd.eq.imp(gs: List<&2, Got>, +have: List<&2, List<&2, U32>>) -> List<&2, Got>:
  match gs:
    case Nil{}:
      Nil{}
    case GotDef{+n, +it} <> t:
      fd.eq.imp.check(fd.eq.missing(T.tba.item.fold(~T.tba.refs, it, Nil{}), have), n, it) <> fd.eq.imp(t, have)
    case g <> t:
      g <> fd.eq.imp(t, have)

def fd.allgots(+xs: List<&2, X.Sx>, +tbs: List<&2, Tb>, +env: Env) -> List<&2, Got>:
  +ds = List.append(&2, Got, fd.datas(xs, env), fd.catas(xs, env))
  +gs = List.append(&2, Got, ds, fd.gots.less(fd.gots(tbs, fd.ok(xs, fd.px.imp(fd.env.px(env))), env), fd.got.defnames(ds)))
  +g2 = fd.eq.fix(gs, fd.got.items(gs))
  +g3 = fd.eq.imp(g2, List.append(&2, List<&2, U32>, fd.got.defnames(g2), fd.ix.defs(fd.px.ix(fd.env.px(env)))))
  fd.eq.prune(g3, fd.got.items(g3))

# The prelude ---------------------------------------------------------------------

# what the written defs call that Base does not have, as Bend text
def fd.pre.if() -> String:
  "# an if: Bend has no if, and matches only parameters, so the branches\n# are thunks, as Base's List.any.if writes it\ndef Bool.if(-R: Type, c: Bool, t: Unit -> R, e: Unit -> R) -> R:\n  match c:\n    case True{}:\n      t(Unit{})\n    case False{}:\n      e(Unit{})\n\n"

def fd.pre.map() -> String:
  "# map over a list Bend may copy (Base's List.map takes List<&1, A>)\ndef hs.map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case h <> t:\n      f(h) <> hs.map(~A, ~B, ~f, t)\n\n"

# HsPrelude.bend, written next to the modules: Haskell's Fix, Cofree and
# CofreeF, each with its functor as a type function (see Types), and the
# defs project and embed are at them
def fd.hsprelude() -> String:
  "# Written by cata: the recursion-scheme types of Haskell's data-fix and free\n# (Data.Fix, Control.Comonad.Cofree, Control.Comonad.Trans.Cofree), each\n# with its functor as a type function, and recursion-schemes' project and\n# embed at them (Data.Functor.Foldable).\nimport Base\n\n# Fix f: a layer of f whose holes are Fix f again\ntype Fix<-F: Data -> Data> is Data:\n  Fix.Fix{unFix: F(Fix<F>)}\n\n# Cofree f a: a :< f (Cofree f a), a layer of f under an annotation\ntype Cofree<-F: Data -> Data, -A: Data> is Data:\n  Cofree.Cofree{head: A, tail: F(Cofree<F, A>)}\n\n# CofreeF f a b: a :< f b, Cofree f a's base functor\ntype CofreeF<-F: Data -> Data, -A: Data, -B: Data> is Data:\n  CofreeF.CofreeF{head: A, tail: F(B)}\n\n# CofreeF's twin (see the fold's Twins): its b a function, its layer a\n# twin\ntype CofreeF.fn<-F: Type -> Type, -A: Data, -B: Type> is Type:\n  CofreeF.fn.CofreeF{head: A, tail: F(B)}\n\ndef Fix.unFix(-F: Data -> Data, x: Fix<F>) -> F(Fix<F>):\n  match x:\n    case Fix.Fix{y}:\n      y\n\ndef Cofree.project(-F: Data -> Data, -A: Data, x: Cofree<F, A>) -> CofreeF<F, A, Cofree<F, A>>:\n  match x:\n    case Cofree.Cofree{h, t}:\n      CofreeF.CofreeF{h, t}\n\ndef Cofree.embed(-F: Data -> Data, -A: Data, x: CofreeF<F, A, Cofree<F, A>>) -> Cofree<F, A>:\n  match x:\n    case CofreeF.CofreeF{h, t}:\n      Cofree.Cofree{h, t}\n"

# HsPrelude's Data.Map and Data.Set (see Types), in pieces: bend's
# compiler takes no longer literal
def fd.hsprelude.m1() -> String:
  "# Data.Map's Map k v and Data.Set's Set k (IntMap a is Map Int a, IntSet\n# Set Int): the pairs (keys) in ascending order of the key, each key once,\n# so two equal maps are one term. compare at K is a template, ~cmp; the\n# functions are structural on the map (a list), Data.Map's semantics, not\n# its balanced tree's cost.\ntype HsMap<-K: Data, -V: Data> is Data:\n  HsMap.Tip{}\n  HsMap.Bin{key: K, val: V, rest: HsMap<K, V>}\n\ntype HsSet<-K: Data> is Data:\n  HsSet.Tip{}\n  HsSet.Bin{key: K, rest: HsSet<K>}\n\n# an if (Bend matches only parameters)\ndef HsBool.if(-R: Type, c: Bool, t: Unit -> R, e: Unit -> R) -> R:\n  match c:\n    case True{}:\n      t(Unit{})\n    case False{}:\n      e(Unit{})\n\n# Cmp's three cases, the branches thunks (Bend matches only parameters)\ndef HsCmp.on(-R: Type, c: Cmp, lt: Unit -> R, eq: Unit -> R, gt: Unit -> R) -> R:\n  match c:\n    case LT{}:\n      lt(Unit{})\n    case EQ{}:\n      eq(Unit{})\n    case GT{}:\n      gt(Unit{})\n\ndef HsMap.insert(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +v: V, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Bin{k, v, HsMap.Tip{}}\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(HsMap<K, V>, cmp(k, k2), _ => HsMap.Bin{k, v, HsMap.Bin{k2, v2, t}}, _ => HsMap.Bin{k, v, t}, _ => HsMap.Bin{k2, v2, HsMap.insert(~K, ~V, ~cmp, k, v, t)})\n\n# insertWith f k new: f new old at a key there\ndef HsMap.insertWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, +k: K, +v: V, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Bin{k, v, HsMap.Tip{}}\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(HsMap<K, V>, cmp(k, k2), _ => HsMap.Bin{k, v, HsMap.Bin{k2, v2, t}}, _ => HsMap.Bin{k, f(v)(v2), t}, _ => HsMap.Bin{k2, v2, HsMap.insertWith(~K, ~V, ~cmp, ~f, k, v, t)})\n\ndef HsMap.lookup(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, m: HsMap<K, V>) -> Maybe<&2, V>:\n  match m:\n    case HsMap.Tip{}:\n      None{}\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(Maybe<&2, V>, cmp(k, k2), _ => None{}, _ => Some{v2}, _ => HsMap.lookup(~K, ~V, ~cmp, k, t))\n\ndef HsMap.member(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, m: HsMap<K, V>) -> Bool:\n  match m:\n    case HsMap.Tip{}:\n      False{}\n    case HsMap.Bin{+k2, v2, +t}:\n      HsCmp.on(Bool, cmp(k, k2), _ => False{}, _ => True{}, _ => HsMap.member(~K, ~V, ~cmp, k, t))\n\ndef HsMap.findWithDefault(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +d: V, +k: K, m: HsMap<K, V>) -> V:\n  match m:\n    case HsMap.Tip{}:\n      d\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(V, cmp(k, k2), _ => d, _ => v2, _ => HsMap.findWithDefault(~K, ~V, ~cmp, d, k, t))\n\ndef HsMap.delete(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(HsMap<K, V>, cmp(k, k2), _ => HsMap.Bin{k2, v2, t}, _ => t, _ => HsMap.Bin{k2, v2, HsMap.delete(~K, ~V, ~cmp, k, t)})\n\n"

def fd.hsprelude.m2() -> String:
  "def HsMap.adjust(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V, +k: K, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{+k2, +v2, +t}:\n      HsCmp.on(HsMap<K, V>, cmp(k, k2), _ => HsMap.Bin{k2, v2, t}, _ => HsMap.Bin{k2, f(v2), t}, _ => HsMap.Bin{k2, v2, HsMap.adjust(~K, ~V, ~cmp, ~f, k, t)})\n\ndef HsMap.toList(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, Sigma<&2, &2, K, _ => V>>:\n  match m:\n    case HsMap.Tip{}:\n      Nil{}\n    case HsMap.Bin{k, v, t}:\n      (k, v) <> HsMap.toList(~K, ~V, t)\n\ndef HsMap.fromList.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Sigma<&2, &2, K, _ => V>>, acc: HsMap<K, V>) -> HsMap<K, V>:\n  match xs:\n    case Nil{}:\n      acc\n    case (k, v) <> t:\n      HsMap.fromList.go(~K, ~V, ~cmp, t, HsMap.insert(~K, ~V, ~cmp, k, v, acc))\n\ndef HsMap.fromList(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap<K, V>:\n  HsMap.fromList.go(~K, ~V, ~cmp, xs, HsMap.Tip{})\n\ndef HsMap.fromListWith.go(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, xs: List<&2, Sigma<&2, &2, K, _ => V>>, acc: HsMap<K, V>) -> HsMap<K, V>:\n  match xs:\n    case Nil{}:\n      acc\n    case (k, v) <> t:\n      HsMap.fromListWith.go(~K, ~V, ~cmp, ~f, t, HsMap.insertWith(~K, ~V, ~cmp, ~f, k, v, acc))\n\ndef HsMap.fromListWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> HsMap<K, V>:\n  HsMap.fromListWith.go(~K, ~V, ~cmp, ~f, xs, HsMap.Tip{})\n\ndef HsMap.elems(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, V>:\n  match m:\n    case HsMap.Tip{}:\n      Nil{}\n    case HsMap.Bin{k, v, t}:\n      v <> HsMap.elems(~K, ~V, t)\n\ndef HsMap.keys(~K: Data, ~V: Data, m: HsMap<K, V>) -> List<&2, K>:\n  match m:\n    case HsMap.Tip{}:\n      Nil{}\n    case HsMap.Bin{k, v, t}:\n      k <> HsMap.keys(~K, ~V, t)\n\ndef HsMap.keysSet(~K: Data, ~V: Data, m: HsMap<K, V>) -> HsSet<K>:\n  match m:\n    case HsMap.Tip{}:\n      HsSet.Tip{}\n    case HsMap.Bin{k, v, t}:\n      HsSet.Bin{k, HsMap.keysSet(~K, ~V, t)}\n\ndef HsMap.size(~K: Data, ~V: Data, m: HsMap<K, V>) -> Nat:\n  match m:\n    case HsMap.Tip{}:\n      0n\n    case HsMap.Bin{k, v, t}:\n      Succ{HsMap.size(~K, ~V, t)}\n\ndef HsMap.null(~K: Data, ~V: Data, m: HsMap<K, V>) -> Bool:\n  match m:\n    case HsMap.Tip{}:\n      True{}\n    case HsMap.Bin{k, v, t}:\n      False{}\n\n# union is left-biased: a's value at a key both have\ndef HsMap.union(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:\n  match a:\n    case HsMap.Tip{}:\n      b\n    case HsMap.Bin{k, v, t}:\n      HsMap.insert(~K, ~V, ~cmp, k, v, HsMap.union(~K, ~V, ~cmp, t, b))\n\ndef HsMap.unionWith(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~f: V -> V -> V, a: HsMap<K, V>, b: HsMap<K, V>) -> HsMap<K, V>:\n  match a:\n    case HsMap.Tip{}:\n      b\n    case HsMap.Bin{k, v, t}:\n      HsMap.insertWith(~K, ~V, ~cmp, ~f, k, v, HsMap.unionWith(~K, ~V, ~cmp, ~f, t, b))\n\n"

def fd.hsprelude.m3() -> String:
  "# the keys of a not in b (IntMap's and Set's difference, \\\\)\ndef HsMap.difference(~K: Data, ~V: Data, ~W: Data, ~cmp: K -> K -> Cmp, a: HsMap<K, V>, +b: HsMap<K, W>) -> HsMap<K, V>:\n  match a:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{+k, v, +t}:\n      HsBool.if(HsMap<K, V>, HsMap.member(~K, ~W, ~cmp, k, b), _ => HsMap.difference(~K, ~V, ~W, ~cmp, t, b), _ => HsMap.Bin{k, v, HsMap.difference(~K, ~V, ~W, ~cmp, t, b)})\n\ndef HsMap.map(~K: Data, ~V: Data, ~W: Data, ~f: V -> W, m: HsMap<K, V>) -> HsMap<K, W>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{k, v, t}:\n      HsMap.Bin{k, f(v), HsMap.map(~K, ~V, ~W, ~f, t)}\n\ndef HsMap.mapWithKey(~K: Data, ~V: Data, ~W: Data, ~f: K -> V -> W, m: HsMap<K, V>) -> HsMap<K, W>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{+k, v, t}:\n      HsMap.Bin{k, f(k)(v), HsMap.mapWithKey(~K, ~V, ~W, ~f, t)}\n\ndef HsMap.filter(~K: Data, ~V: Data, ~p: V -> Bool, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{k, +v, +t}:\n      HsBool.if(HsMap<K, V>, p(v), _ => HsMap.Bin{k, v, HsMap.filter(~K, ~V, ~p, t)}, _ => HsMap.filter(~K, ~V, ~p, t))\n\ndef HsMap.filterWithKey(~K: Data, ~V: Data, ~p: K -> V -> Bool, m: HsMap<K, V>) -> HsMap<K, V>:\n  match m:\n    case HsMap.Tip{}:\n      HsMap.Tip{}\n    case HsMap.Bin{+k, +v, +t}:\n      HsBool.if(HsMap<K, V>, p(k)(v), _ => HsMap.Bin{k, v, HsMap.filterWithKey(~K, ~V, ~p, t)}, _ => HsMap.filterWithKey(~K, ~V, ~p, t))\n\ndef HsMap.foldr(~K: Data, ~V: Data, ~B: Data, ~f: V -> B -> B, z: B, m: HsMap<K, V>) -> B:\n  match m:\n    case HsMap.Tip{}:\n      z\n    case HsMap.Bin{k, v, t}:\n      f(v)(HsMap.foldr(~K, ~V, ~B, ~f, z, t))\n\ndef HsMap.foldrWithKey(~K: Data, ~V: Data, ~B: Data, ~f: K -> V -> B -> B, z: B, m: HsMap<K, V>) -> B:\n  match m:\n    case HsMap.Tip{}:\n      z\n    case HsMap.Bin{k, v, t}:\n      f(k)(v)(HsMap.foldrWithKey(~K, ~V, ~B, ~f, z, t))\n\ndef HsMap.eq(~K: Data, ~V: Data, ~eqk: K -> K -> Bool, ~eqv: V -> V -> Bool, a: HsMap<K, V>, b: HsMap<K, V>) -> Bool:\n  match a b:\n    case HsMap.Tip{} HsMap.Tip{}:\n      True{}\n    case HsMap.Bin{k1, v1, t1} HsMap.Bin{k2, v2, t2}:\n      Bool.and(Bool.and(eqk(k1)(k2), eqv(v1)(v2)), HsMap.eq(~K, ~V, ~eqk, ~eqv, t1, t2))\n    case _ _:\n      False{}\n\ndef HsSet.insert(~K: Data, ~cmp: K -> K -> Cmp, +k: K, s: HsSet<K>) -> HsSet<K>:\n  match s:\n    case HsSet.Tip{}:\n      HsSet.Bin{k, HsSet.Tip{}}\n    case HsSet.Bin{+k2, +t}:\n      HsCmp.on(HsSet<K>, cmp(k, k2), _ => HsSet.Bin{k, HsSet.Bin{k2, t}}, _ => HsSet.Bin{k2, t}, _ => HsSet.Bin{k2, HsSet.insert(~K, ~cmp, k, t)})\n\ndef HsSet.member(~K: Data, ~cmp: K -> K -> Cmp, +k: K, s: HsSet<K>) -> Bool:\n  match s:\n    case HsSet.Tip{}:\n      False{}\n    case HsSet.Bin{+k2, +t}:\n      HsCmp.on(Bool, cmp(k, k2), _ => False{}, _ => True{}, _ => HsSet.member(~K, ~cmp, k, t))\n\n"

def fd.hsprelude.m4() -> String:
  "def HsSet.delete(~K: Data, ~cmp: K -> K -> Cmp, +k: K, s: HsSet<K>) -> HsSet<K>:\n  match s:\n    case HsSet.Tip{}:\n      HsSet.Tip{}\n    case HsSet.Bin{+k2, +t}:\n      HsCmp.on(HsSet<K>, cmp(k, k2), _ => HsSet.Bin{k2, t}, _ => t, _ => HsSet.Bin{k2, HsSet.delete(~K, ~cmp, k, t)})\n\ndef HsSet.toList(~K: Data, s: HsSet<K>) -> List<&2, K>:\n  match s:\n    case HsSet.Tip{}:\n      Nil{}\n    case HsSet.Bin{k, t}:\n      k <> HsSet.toList(~K, t)\n\ndef HsSet.fromList.go(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>, acc: HsSet<K>) -> HsSet<K>:\n  match xs:\n    case Nil{}:\n      acc\n    case k <> t:\n      HsSet.fromList.go(~K, ~cmp, t, HsSet.insert(~K, ~cmp, k, acc))\n\ndef HsSet.fromList(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, K>) -> HsSet<K>:\n  HsSet.fromList.go(~K, ~cmp, xs, HsSet.Tip{})\n\ndef HsSet.union(~K: Data, ~cmp: K -> K -> Cmp, a: HsSet<K>, b: HsSet<K>) -> HsSet<K>:\n  match a:\n    case HsSet.Tip{}:\n      b\n    case HsSet.Bin{k, t}:\n      HsSet.insert(~K, ~cmp, k, HsSet.union(~K, ~cmp, t, b))\n\ndef HsSet.unions(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, HsSet<K>>) -> HsSet<K>:\n  match xs:\n    case Nil{}:\n      HsSet.Tip{}\n    case s <> t:\n      HsSet.union(~K, ~cmp, s, HsSet.unions(~K, ~cmp, t))\n\ndef HsSet.difference(~K: Data, ~cmp: K -> K -> Cmp, a: HsSet<K>, +b: HsSet<K>) -> HsSet<K>:\n  match a:\n    case HsSet.Tip{}:\n      HsSet.Tip{}\n    case HsSet.Bin{+k, +t}:\n      HsBool.if(HsSet<K>, HsSet.member(~K, ~cmp, k, b), _ => HsSet.difference(~K, ~cmp, t, b), _ => HsSet.Bin{k, HsSet.difference(~K, ~cmp, t, b)})\n\ndef HsSet.filter(~K: Data, ~p: K -> Bool, s: HsSet<K>) -> HsSet<K>:\n  match s:\n    case HsSet.Tip{}:\n      HsSet.Tip{}\n    case HsSet.Bin{+k, +t}:\n      HsBool.if(HsSet<K>, p(k), _ => HsSet.Bin{k, HsSet.filter(~K, ~p, t)}, _ => HsSet.filter(~K, ~p, t))\n\ndef HsSet.map.go(~K: Data, ~L: Data, ~cmp: L -> L -> Cmp, ~f: K -> L, s: HsSet<K>, acc: HsSet<L>) -> HsSet<L>:\n  match s:\n    case HsSet.Tip{}:\n      acc\n    case HsSet.Bin{k, t}:\n      HsSet.map.go(~K, ~L, ~cmp, ~f, t, HsSet.insert(~L, ~cmp, f(k), acc))\n\ndef HsSet.map(~K: Data, ~L: Data, ~cmp: L -> L -> Cmp, ~f: K -> L, s: HsSet<K>) -> HsSet<L>:\n  HsSet.map.go(~K, ~L, ~cmp, ~f, s, HsSet.Tip{})\n\ndef HsSet.size(~K: Data, s: HsSet<K>) -> Nat:\n  match s:\n    case HsSet.Tip{}:\n      0n\n    case HsSet.Bin{k, t}:\n      Succ{HsSet.size(~K, t)}\n\ndef HsSet.null(~K: Data, s: HsSet<K>) -> Bool:\n  match s:\n    case HsSet.Tip{}:\n      True{}\n    case HsSet.Bin{k, t}:\n      False{}\n\ndef HsSet.eq(~K: Data, ~eqk: K -> K -> Bool, a: HsSet<K>, b: HsSet<K>) -> Bool:\n  match a b:\n    case HsSet.Tip{} HsSet.Tip{}:\n      True{}\n    case HsSet.Bin{k1, t1} HsSet.Bin{k2, t2}:\n      Bool.and(eqk(k1)(k2), HsSet.eq(~K, ~eqk, t1, t2))\n    case _ _:\n      False{}\n\ndef HsMap.empty(~K: Data, ~V: Data) -> HsMap<K, V>:\n  HsMap.Tip{}\n\ndef HsMap.singleton(~K: Data, ~V: Data, k: K, v: V) -> HsMap<K, V>:\n  HsMap.Bin{k, v, HsMap.Tip{}}\n\n"

def fd.hsprelude.m5() -> String:
  "def HsMap.notMember(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, k: K, m: HsMap<K, V>) -> Bool:\n  Bool.not(HsMap.member(~K, ~V, ~cmp, k, m))\n\ndef HsSet.empty(~K: Data) -> HsSet<K>:\n  HsSet.Tip{}\n\ndef HsSet.singleton(~K: Data, k: K) -> HsSet<K>:\n  HsSet.Bin{k, HsSet.Tip{}}\n\ndef HsSet.notMember(~K: Data, ~cmp: K -> K -> Cmp, k: K, s: HsSet<K>) -> Bool:\n  Bool.not(HsSet.member(~K, ~cmp, k, s))\n\n# compare at Bool, (), a list, a pair and Maybe (Haskell's derived Ord:\n# False < True, [] first, then lexicographic; Nothing first)\ndef HsCmp.bool(a: Bool, b: Bool) -> Cmp:\n  match a b:\n    case False{} True{}:\n      LT{}\n    case True{} False{}:\n      GT{}\n    case _ _:\n      EQ{}\n\ndef HsCmp.unit(a: Unit, b: Unit) -> Cmp:\n  EQ{}\n\ndef HsCmp.list(~A: Data, ~cmp: A -> A -> Cmp, a: List<&2, A>, b: List<&2, A>) -> Cmp:\n  match a b:\n    case Nil{} Nil{}:\n      EQ{}\n    case Nil{} _:\n      LT{}\n    case _ Nil{}:\n      GT{}\n    case h1 <> t1 h2 <> t2:\n      HsCmp.on(Cmp, cmp(h1)(h2), _ => LT{}, _ => HsCmp.list(~A, ~cmp, t1, t2), _ => GT{})\n\ndef HsCmp.pair(~A: Data, ~B: Data, ~ca: A -> A -> Cmp, ~cb: B -> B -> Cmp, p: Sigma<&2, &2, A, _ => B>, q: Sigma<&2, &2, A, _ => B>) -> Cmp:\n  match p q:\n    case Tuple{a1, b1} Tuple{a2, b2}:\n      HsCmp.on(Cmp, ca(a1)(a2), _ => LT{}, _ => cb(b1)(b2), _ => GT{})\n\ndef HsCmp.maybe(~A: Data, ~cmp: A -> A -> Cmp, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Cmp:\n  match a b:\n    case None{} None{}:\n      EQ{}\n    case None{} _:\n      LT{}\n    case _ None{}:\n      GT{}\n    case Some{x} Some{y}:\n      cmp(x)(y)\n\ndef HsCmp.char(a: Char, b: Char) -> Cmp:\n  U32.cmp(Char.to_u32(a), Char.to_u32(b))\n\n\n"

def fd.hsprelude.maps() -> String:
  fd.hsprelude.m1() ++ fd.hsprelude.m2() ++ fd.hsprelude.m3() ++ fd.hsprelude.m4() ++ fd.hsprelude.m5()

# HsPrelude part (see Types), in pieces: bend's
# compiler takes no longer literal
def fd.hsprelude.i1() -> String:
  "# Haskell's Int and Integer as an integer: Pos{n} is n, Neg{n} is -n (n at\n# least 1), so each integer is one term.  (Int's 64-bit wrap-around is not\n# modelled: an Int that would overflow is out of this translation's reach.)\ntype HsInt is Data:\n  HsInt.Pos{n: Nat}\n  HsInt.Neg{n: Nat}\n\ndef HsInt.of(n: Nat) -> HsInt:\n  HsInt.Pos{n}\n\n# -n for a Nat n\ndef HsInt.neg.of(n: Nat) -> HsInt:\n  match n:\n    case Zero{}:\n      HsInt.Pos{Zero{}}\n    case Succ{p}:\n      HsInt.Neg{Succ{p}}\n\ndef HsInt.negate(a: HsInt) -> HsInt:\n  match a:\n    case HsInt.Pos{n}:\n      HsInt.neg.of(n)\n    case HsInt.Neg{n}:\n      HsInt.Pos{n}\n\n# a - b for Nats, as an integer\ndef HsInt.nsub(a: Nat, b: Nat) -> HsInt:\n  match a b:\n    case Zero{} m:\n      HsInt.neg.of(m)\n    case n Zero{}:\n      HsInt.Pos{n}\n    case Succ{p} Succ{q}:\n      HsInt.nsub(p, q)\n\ndef HsInt.add(a: HsInt, b: HsInt) -> HsInt:\n  match a b:\n    case HsInt.Pos{m} HsInt.Pos{n}:\n      HsInt.Pos{Nat.add(m, n)}\n    case HsInt.Neg{m} HsInt.Neg{n}:\n      HsInt.Neg{Nat.add(m, n)}\n    case HsInt.Pos{m} HsInt.Neg{n}:\n      HsInt.nsub(m, n)\n    case HsInt.Neg{m} HsInt.Pos{n}:\n      HsInt.nsub(n, m)\n\ndef HsInt.sub(a: HsInt, b: HsInt) -> HsInt:\n  HsInt.add(a, HsInt.negate(b))\n\ndef HsInt.mul.sign(neg: Bool, n: Nat) -> HsInt:\n  match neg:\n    case True{}:\n      HsInt.neg.of(n)\n    case False{}:\n      HsInt.Pos{n}\n\ndef HsInt.mul(a: HsInt, b: HsInt) -> HsInt:\n  match a b:\n    case HsInt.Pos{m} HsInt.Pos{n}:\n      HsInt.Pos{Nat.mul(m, n)}\n    case HsInt.Neg{m} HsInt.Neg{n}:\n      HsInt.Pos{Nat.mul(m, n)}\n    case HsInt.Pos{m} HsInt.Neg{n}:\n      HsInt.neg.of(Nat.mul(m, n))\n    case HsInt.Neg{m} HsInt.Pos{n}:\n      HsInt.neg.of(Nat.mul(m, n))\n\ndef HsInt.abs(a: HsInt) -> HsInt:\n  match a:\n    case HsInt.Pos{n}:\n      HsInt.Pos{n}\n    case HsInt.Neg{n}:\n      HsInt.Pos{n}\n\ndef HsInt.signum(a: HsInt) -> HsInt:\n  match a:\n    case HsInt.Pos{Zero{}}:\n      HsInt.Pos{Zero{}}\n    case HsInt.Pos{Succ{p}}:\n      HsInt.Pos{1n}\n    case HsInt.Neg{n}:\n      HsInt.Neg{1n}\n\ndef HsInt.cmp(a: HsInt, b: HsInt) -> Cmp:\n  match a b:\n    case HsInt.Pos{m} HsInt.Pos{n}:\n      Nat.cmp(m, n)\n    case HsInt.Neg{m} HsInt.Neg{n}:\n      Nat.cmp(n, m)\n    case HsInt.Pos{m} HsInt.Neg{n}:\n      GT{}\n    case HsInt.Neg{m} HsInt.Pos{n}:\n      LT{}\n\ndef HsInt.is_eq(a: HsInt, b: HsInt) -> Bool:\n  Cmp.is_eq(HsInt.cmp(a, b))\n\ndef HsInt.is_ne(a: HsInt, b: HsInt) -> Bool:\n  Bool.not(Cmp.is_eq(HsInt.cmp(a, b)))\n\ndef HsInt.is_lt(a: HsInt, b: HsInt) -> Bool:\n  Cmp.is_lt(HsInt.cmp(a, b))\n\ndef HsInt.is_le(a: HsInt, b: HsInt) -> Bool:\n  Cmp.is_le(HsInt.cmp(a, b))\n\ndef HsInt.is_gt(a: HsInt, b: HsInt) -> Bool:\n  Cmp.is_gt(HsInt.cmp(a, b))\n\ndef HsInt.is_ge(a: HsInt, b: HsInt) -> Bool:\n  Cmp.is_ge(HsInt.cmp(a, b))\n\ndef HsInt.max(+a: HsInt, +b: HsInt) -> HsInt:\n  Bool.pick(HsInt, Cmp.is_ge(HsInt.cmp(a, b)), a, b)\n\ndef HsInt.min(+a: HsInt, +b: HsInt) -> HsInt:\n  Bool.pick(HsInt, Cmp.is_le(HsInt.cmp(a, b)), a, b)\n\n"

def fd.hsprelude.i2() -> String:
  "def HsInt.mag(a: HsInt) -> Nat:\n  match a:\n    case HsInt.Pos{n}:\n      n\n    case HsInt.Neg{n}:\n      n\n\ndef HsInt.isneg(a: HsInt) -> Bool:\n  match a:\n    case HsInt.Pos{n}:\n      False{}\n    case HsInt.Neg{n}:\n      True{}\n\n# quot and rem truncate toward zero; div and mod round toward minus\n# infinity (Haskell's)\ndef HsInt.quot(+a: HsInt, +b: HsInt) -> HsInt:\n  HsInt.mul.sign(Bool.xor(HsInt.isneg(a), HsInt.isneg(b)), Nat.div(HsInt.mag(a), HsInt.mag(b)))\n\ndef HsInt.rem(+a: HsInt, +b: HsInt) -> HsInt:\n  HsInt.mul.sign(HsInt.isneg(a), Nat.mod(HsInt.mag(a), HsInt.mag(b)))\n\ndef HsInt.div(+a: HsInt, +b: HsInt) -> HsInt:\n  +q = HsInt.quot(a, b)\n  +r = HsInt.rem(a, b)\n  Bool.pick(HsInt, Bool.and(Bool.not(HsInt.is_eq(r, HsInt.Pos{0n})), Bool.xor(HsInt.isneg(a), HsInt.isneg(b))), HsInt.sub(q, HsInt.Pos{1n}), q)\n\ndef HsInt.mod(+a: HsInt, +b: HsInt) -> HsInt:\n  +r = HsInt.rem(a, b)\n  Bool.pick(HsInt, Bool.and(Bool.not(HsInt.is_eq(r, HsInt.Pos{0n})), Bool.xor(HsInt.isneg(r), HsInt.isneg(b))), HsInt.add(r, b), r)\n\ndef HsInt.pow.go(+a: HsInt, n: Nat) -> HsInt:\n  match n:\n    case Zero{}:\n      HsInt.Pos{1n}\n    case Succ{p}:\n      HsInt.mul(a, HsInt.pow.go(a, p))\n\n# a ^ e (e at least 0)\ndef HsInt.pow(+a: HsInt, e: HsInt) -> HsInt:\n  HsInt.pow.go(a, HsInt.mag(e))\n\ndef HsInt.succ(a: HsInt) -> HsInt:\n  HsInt.add(a, HsInt.Pos{1n})\n\ndef HsInt.pred(a: HsInt) -> HsInt:\n  HsInt.sub(a, HsInt.Pos{1n})\n\n# show: the digits, after a minus when negative\ndef HsInt.show(a: HsInt) -> List<&2, Char>:\n  match a:\n    case HsInt.Pos{n}:\n      String.to_list(Nat.show(n))\n    case HsInt.Neg{n}:\n      '-' <> String.to_list(Nat.show(n))\n\ndef HsInt.count(a: HsInt) -> Nat:\n  match a:\n    case HsInt.Pos{n}:\n      n\n    case HsInt.Neg{n}:\n      0n\n\n# [a .. b]\ndef HsInt.range.go(n: Nat, +a: HsInt) -> List<&2, HsInt>:\n  match n:\n    case Zero{}:\n      Nil{}\n    case Succ{p}:\n      a <> HsInt.range.go(p, HsInt.succ(a))\n\ndef HsInt.range(+a: HsInt, +b: HsInt) -> List<&2, HsInt>:\n  HsInt.range.go(HsInt.count(HsInt.sub(HsInt.succ(b), a)), a)\n\n\n"

def fd.hsprelude.ints() -> String:
  fd.hsprelude.i1() ++ fd.hsprelude.i2()

# HsPrelude part (see Types), in pieces: bend's
# compiler takes no longer literal
def fd.hsprelude.d1() -> String:
  "# crypton's Digest SHA256: its 32 bytes (each a U32 below 256); hash is\n# SHA-256 (FIPS 180-4) of a ByteString, a list of such bytes\ntype HsDigest is Data:\n  HsDigest.D{bytes: List<&2, U32>}\n\ndef HsSha.rotr(+x: U32, +n: Nat) -> U32:\n  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))\n\ndef HsSha.ch(+x: U32, y: U32, z: U32) -> U32:\n  U32.xor(U32.and(x, y), U32.and(U32.not(x), z))\n\ndef HsSha.maj(+x: U32, +y: U32, +z: U32) -> U32:\n  U32.xor(U32.xor(U32.and(x, y), U32.and(x, z)), U32.and(y, z))\n\ndef HsSha.bs0(+x: U32) -> U32:\n  U32.xor(U32.xor(HsSha.rotr(x, 2n), HsSha.rotr(x, 13n)), HsSha.rotr(x, 22n))\n\ndef HsSha.bs1(+x: U32) -> U32:\n  U32.xor(U32.xor(HsSha.rotr(x, 6n), HsSha.rotr(x, 11n)), HsSha.rotr(x, 25n))\n\ndef HsSha.ss0(+x: U32) -> U32:\n  U32.xor(U32.xor(HsSha.rotr(x, 7n), HsSha.rotr(x, 18n)), U32.shrn(x, 3n))\n\ndef HsSha.ss1(+x: U32) -> U32:\n  U32.xor(U32.xor(HsSha.rotr(x, 17n), HsSha.rotr(x, 19n)), U32.shrn(x, 10n))\n\ndef HsSha.k() -> List<&2, U32>:\n  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221, 3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580, 3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]\n\ndef HsSha.h0() -> List<&2, U32>:\n  [1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225]\n\ndef HsSha.nth(xs: List<&2, U32>, n: Nat) -> U32:\n  match xs n:\n    case x <> t Zero{}:\n      x\n    case x <> t Succ{k}:\n      HsSha.nth(t, k)\n    case Nil{} _:\n      0\n\n# the message padded: 0x80, zeros to 56 mod 64, the length in bits (8 bytes)\ndef HsSha.zeros(n: Nat) -> List<&2, U32>:\n  match n:\n    case Zero{}:\n      Nil{}\n    case Succ{k}:\n      0 <> HsSha.zeros(k)\n\ndef HsSha.be8.go(n: Nat, +v: Nat, acc: List<&2, U32>) -> List<&2, U32>:\n  match n:\n    case Zero{}:\n      acc\n    case Succ{k}:\n      HsSha.be8.go(k, Nat.div(v, 256n), U32.from_nat(Nat.mod(v, 256n)) <> acc)\n\ndef HsSha.pad(+m: List<&2, U32>) -> List<&2, U32>:\n  +l = List.length(&2, U32, m)\n  +r = Nat.mod(l, 64n)\n  +z = Bool.pick(Nat, Nat.is_le(r, 55n), Nat.sub(55n, r), Nat.sub(119n, r))\n  List.append(&2, U32, m, 128 <> List.append(&2, U32, HsSha.zeros(z), HsSha.be8.go(8n, Nat.mul(l, 8n), Nil{})))\n\n# four bytes, big-endian, as a word\ndef HsSha.word(a: U32, b: U32, c: U32, d: U32) -> U32:\n  U32.or(U32.or(U32.shln(a, 24n), U32.shln(b, 16n)), U32.or(U32.shln(c, 8n), d))\n\n"

def fd.hsprelude.d2() -> String:
  "# a 64-byte block's 16 words, and the bytes after it\ntype ShaBlk is Data:\n  ShaBlk{ws: List<&2, U32>, rest: List<&2, U32>}\n\ndef HsSha.words(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> ShaBlk:\n  match n bs:\n    case Succ{k} a <> b <> c <> d <> t:\n      HsSha.words(k, t, HsSha.word(a, b, c, d) <> acc)\n    case _ t:\n      ShaBlk{List.reverse(&2, U32, acc), t}\n\n# the schedule: w16..w63 from the last sixteen\ndef HsSha.sched(n: Nat, +win: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:\n  match n:\n    case Zero{}:\n      List.reverse(&2, U32, acc)\n    case Succ{k}:\n      +w = U32.add(U32.add(HsSha.ss1(HsSha.nth(win, 14n)), HsSha.nth(win, 9n)), U32.add(HsSha.ss0(HsSha.nth(win, 1n)), HsSha.nth(win, 0n)))\n      HsSha.sched(k, List.append(&2, U32, List.tail(&2, U32, win), [w]), w <> acc)\n\ntype ShaSt is Data:\n  ShaSt{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}\n\ndef HsSha.round(s: ShaSt, k: U32, w: U32) -> ShaSt:\n  match s:\n    case ShaSt{+a, +b, +c, d, +e, +f, +g, h}:\n      +t1 = U32.add(U32.add(U32.add(h, HsSha.bs1(e)), U32.add(HsSha.ch(e, f, g), k)), w)\n      +t2 = U32.add(HsSha.bs0(a), HsSha.maj(a, b, c))\n      ShaSt{U32.add(t1, t2), a, b, c, U32.add(d, t1), e, f, g}\n\ndef HsSha.rounds(ks: List<&2, U32>, ws: List<&2, U32>, s: ShaSt) -> ShaSt:\n  match ks ws:\n    case k <> kt w <> wt:\n      HsSha.rounds(kt, wt, HsSha.round(s, k, w))\n    case _ _:\n      s\n\ndef HsSha.st(hs: List<&2, U32>) -> ShaSt:\n  match hs:\n    case a <> b <> c <> d <> e <> f <> g <> h <> _:\n      ShaSt{a, b, c, d, e, f, g, h}\n    case _:\n      ShaSt{0, 0, 0, 0, 0, 0, 0, 0}\n\ndef HsSha.add(hs: List<&2, U32>, s: ShaSt) -> List<&2, U32>:\n  match hs s:\n    case a <> b <> c <> d <> e <> f <> g <> h <> _ ShaSt{a2, b2, c2, d2, e2, f2, g2, h2}:\n      [U32.add(a, a2), U32.add(b, b2), U32.add(c, c2), U32.add(d, d2), U32.add(e, e2), U32.add(f, f2), U32.add(g, g2), U32.add(h, h2)]\n    case _ _:\n      Nil{}\n\ndef HsSha.block(+hs: List<&2, U32>, +ws: List<&2, U32>) -> List<&2, U32>:\n  HsSha.add(hs, HsSha.rounds(HsSha.k(), HsSha.sched(48n, ws, List.reverse(&2, U32, ws)), HsSha.st(hs)))\n\n# the padded message in 64-byte chunks (k of them)\ndef HsSha.chunks(k: Nat, +bs: List<&2, U32>) -> List<&2, List<&2, U32>>:\n  match k:\n    case Zero{}:\n      Nil{}\n    case Succ{p}:\n      List.take(&2, U32, bs, 64n) <> HsSha.chunks(p, List.drop(&2, U32, bs, 64n))\n\ndef HsSha.ws.of(b: ShaBlk) -> List<&2, U32>:\n  match b:\n    case ShaBlk{ws, rest}:\n      ws\n\ndef HsSha.run(cs: List<&2, List<&2, U32>>, hs: List<&2, U32>) -> List<&2, U32>:\n  match cs:\n    case Nil{}:\n      hs\n    case c <> t:\n      HsSha.run(t, HsSha.block(hs, HsSha.ws.of(HsSha.words(16n, c, Nil{}))))\n\n# a word's four bytes, big-endian\ndef HsSha.bytes(ws: List<&2, U32>) -> List<&2, U32>:\n  match ws:\n    case Nil{}:\n      Nil{}\n    case +w <> t:\n      U32.and(U32.shrn(w, 24n), 255) <> U32.and(U32.shrn(w, 16n), 255) <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(w, 255) <> HsSha.bytes(t)\n\n"

def fd.hsprelude.d3() -> String:
  "def HsDigest.hash(+m: List<&2, U32>) -> HsDigest:\n  +p = HsSha.pad(m)\n  HsDigest.D{HsSha.bytes(HsSha.run(HsSha.chunks(Nat.div(List.length(&2, U32, p), 64n), p), HsSha.h0()))}\n\ndef HsDigest.bytes(d: HsDigest) -> List<&2, U32>:\n  match d:\n    case HsDigest.D{bs}:\n      bs\n\ndef HsSha.hexd(+n: U32) -> Char:\n  Char.from_u32(Bool.pick(U32, U32.is_lt(n, 10), U32.add(n, 48), U32.add(n, 87)))\n\ndef HsSha.hex(bs: List<&2, U32>) -> List<&2, Char>:\n  match bs:\n    case Nil{}:\n      Nil{}\n    case +b <> t:\n      HsSha.hexd(U32.shrn(b, 4n)) <> HsSha.hexd(U32.and(b, 15)) <> HsSha.hex(t)\n\n# show: the hex digits (crypton shows a digest as its base-16 text)\ndef HsDigest.hexs(d: HsDigest) -> List<&2, Char>:\n  HsSha.hex(HsDigest.bytes(d))\n\ndef HsDigest.cmp.go(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:\n  match a b:\n    case Nil{} Nil{}:\n      EQ{}\n    case Nil{} _:\n      LT{}\n    case _ Nil{}:\n      GT{}\n    case +x <> s +y <> t:\n      HsCmp.on(Cmp, U32.cmp(x, y), _ => LT{}, _ => HsDigest.cmp.go(s, t), _ => GT{})\n\n# Ord at a digest: its bytes, lexicographically (crypton's)\ndef HsDigest.cmp(a: HsDigest, b: HsDigest) -> Cmp:\n  HsDigest.cmp.go(HsDigest.bytes(a), HsDigest.bytes(b))\n\ndef HsDigest.is_eq(a: HsDigest, b: HsDigest) -> Bool:\n  Cmp.is_eq(HsDigest.cmp(a, b))\n\n# utf8-string's encode: a String as its UTF-8 bytes\ndef HsUtf8.char(+c: U32) -> List<&2, U32>:\n  +b = U32.and(c, 63)\n  +b6 = U32.and(U32.shrn(c, 6n), 63)\n  +b12 = U32.and(U32.shrn(c, 12n), 63)\n  Bool.pick(List<&2, U32>, U32.is_lt(c, 128), [c], Bool.pick(List<&2, U32>, U32.is_lt(c, 2048), [U32.or(192, U32.shrn(c, 6n)), U32.or(128, b)], Bool.pick(List<&2, U32>, U32.is_lt(c, 65536), [U32.or(224, U32.shrn(c, 12n)), U32.or(128, b6), U32.or(128, b)], [U32.or(240, U32.shrn(c, 18n)), U32.or(128, b12), U32.or(128, b6), U32.or(128, b)])))\n\ndef HsUtf8.encode(s: List<&2, Char>) -> List<&2, U32>:\n  match s:\n    case Nil{}:\n      Nil{}\n    case c <> t:\n      List.append(&2, U32, HsUtf8.char(Char.to_u32(c)), HsUtf8.encode(t))\n\n\n"

def fd.hsprelude.digests() -> String:
  fd.hsprelude.d1() ++ fd.hsprelude.d2() ++ fd.hsprelude.d3()

# HsPrelude part (see Types), in pieces: bend's
# compiler takes no longer literal
def fd.hsprelude.l1() -> String:
  "# Haskell's list, Maybe, Either and pair functions (Data.List, Data.Maybe,\n# Data.Either, Data.Tuple) on Base's List, Maybe, Either and pairs, with\n# Haskell's answers on finite lists. == at an element is a template ~eq,\n# compare ~cmp; Int counts are Nat here (the fold gives HsInt's count).\n\n# zip [n ..] xs and zip xs [n ..]: Haskell's endless [n ..] ends with xs\n\n# whether some y of ys has eq y x (nubBy's order: the earlier element first)\n\n# lines: the text between newlines, a last line without one kept (cur: the\n\n# line so far, reversed)\n\n# the word or last line so far (reversed), when there is one, before rest\n\n# words: the runs of non-space\n\n# sortBy: stable, as Haskell's (an element goes before the later equal ones)\n\n# groupBy: h heads the group, cur its later elements (reversed)\n\n# Data.Bifunctor's first, second and bimap at Either and pairs\n\ndef HsList.fst(~A: Data, ~B: Data, p: Sigma<&2, &2, A, _ => B>) -> A:\n  match p:\n    case Tuple{a, b}:\n      a\n\ndef HsList.snd(~A: Data, ~B: Data, p: Sigma<&2, &2, A, _ => B>) -> B:\n  match p:\n    case Tuple{a, b}:\n      b\n\ndef HsList.uncurry(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, p: Sigma<&2, &2, A, _ => B>) -> C:\n  match p:\n    case Tuple{a, b}:\n      f(a)(b)\n\ndef HsList.swap(~A: Data, ~B: Data, p: Sigma<&2, &2, A, _ => B>) -> Sigma<&2, &2, B, _ => A>:\n  match p:\n    case Tuple{a, b}:\n      Tuple{b, a}\n\ndef HsList.zip(~A: Data, ~B: Data, xs: List<&2, A>, ys: List<&2, B>) -> List<&2, Sigma<&2, &2, A, _ => B>>:\n  match xs ys:\n    case x <> xt y <> yt:\n      Tuple{x, y} <> HsList.zip(~A, ~B, xt, yt)\n    case _ _:\n      Nil{}\n\ndef HsList.zip3(~A: Data, ~B: Data, ~C: Data, xs: List<&2, A>, ys: List<&2, B>, zs: List<&2, C>) -> List<&2, Sigma<&2, &2, A, _ => Sigma<&2, &2, B, _ => C>>>:\n  match xs ys zs:\n    case x <> xt y <> yt z <> zt:\n      Tuple{x, Tuple{y, z}} <> HsList.zip3(~A, ~B, ~C, xt, yt, zt)\n    case _ _ _:\n      Nil{}\n\ndef HsList.zipWith(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, xs: List<&2, A>, ys: List<&2, B>) -> List<&2, C>:\n  match xs ys:\n    case x <> xt y <> yt:\n      f(x)(y) <> HsList.zipWith(~A, ~B, ~C, ~f, xt, yt)\n    case _ _:\n      Nil{}\n\ndef HsList.zipWith3(~A: Data, ~B: Data, ~C: Data, ~D: Data, ~f: A -> B -> C -> D, xs: List<&2, A>, ys: List<&2, B>, zs: List<&2, C>) -> List<&2, D>:\n  match xs ys zs:\n    case x <> xt y <> yt z <> zt:\n      f(x)(y)(z) <> HsList.zipWith3(~A, ~B, ~C, ~D, ~f, xt, yt, zt)\n    case _ _ _:\n      Nil{}\n\ndef HsList.zipFrom.go(~K: Data, ~A: Data, ~sc: K -> K, xs: List<&2, A>, +n: K) -> List<&2, Sigma<&2, &2, K, _ => A>>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      Tuple{n, x} <> HsList.zipFrom.go(~K, ~A, ~sc, t, sc(n))\n\ndef HsList.zipFrom(~K: Data, ~A: Data, ~sc: K -> K, n: K, xs: List<&2, A>) -> List<&2, Sigma<&2, &2, K, _ => A>>:\n  HsList.zipFrom.go(~K, ~A, ~sc, xs, n)\n\n"

def fd.hsprelude.l2() -> String:
  "def HsList.zipR(~A: Data, ~K: Data, ~sc: K -> K, xs: List<&2, A>, +n: K) -> List<&2, Sigma<&2, &2, A, _ => K>>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      Tuple{x, n} <> HsList.zipR(~A, ~K, ~sc, t, sc(n))\n\ndef HsList.zipWithFrom.go(~K: Data, ~B: Data, ~C: Data, ~sc: K -> K, ~f: K -> B -> C, xs: List<&2, B>, +n: K) -> List<&2, C>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      f(n)(x) <> HsList.zipWithFrom.go(~K, ~B, ~C, ~sc, ~f, t, sc(n))\n\ndef HsList.zipWithFrom(~K: Data, ~B: Data, ~C: Data, ~sc: K -> K, ~f: K -> B -> C, n: K, xs: List<&2, B>) -> List<&2, C>:\n  HsList.zipWithFrom.go(~K, ~B, ~C, ~sc, ~f, xs, n)\n\ndef HsList.zipWithR(~A: Data, ~K: Data, ~C: Data, ~sc: K -> K, ~f: A -> K -> C, xs: List<&2, A>, +n: K) -> List<&2, C>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      f(x)(n) <> HsList.zipWithR(~A, ~K, ~C, ~sc, ~f, t, sc(n))\n\ndef HsList.unzip.cons(~A: Data, ~B: Data, a: A, b: B, r: Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>:\n  match r:\n    case Tuple{xa, xb}:\n      Tuple{a <> xa, b <> xb}\n\ndef HsList.unzip(~A: Data, ~B: Data, ps: List<&2, Sigma<&2, &2, A, _ => B>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>:\n  match ps:\n    case Nil{}:\n      Tuple{Nil{}, Nil{}}\n    case Tuple{a, b} <> t:\n      HsList.unzip.cons(~A, ~B, a, b, HsList.unzip(~A, ~B, t))\n\ndef HsList.lookup(~K: Data, ~V: Data, ~eq: K -> K -> Bool, +k: K, xs: List<&2, Sigma<&2, &2, K, _ => V>>) -> Maybe<&2, V>:\n  match xs:\n    case Nil{}:\n      None{}\n    case Tuple{+k2, v} <> t:\n      HsBool.if(Maybe<&2, V>, eq(k)(k2), _ => Some{v}, _ => HsList.lookup(~K, ~V, ~eq, k, t))\n\ndef HsList.takeWhile(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case +x <> t:\n      HsBool.if(List<&2, A>, p(x), _ => x <> HsList.takeWhile(~A, ~p, t), _ => Nil{})\n\ndef HsList.dropWhile(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case +x <> +t:\n      HsBool.if(List<&2, A>, p(x), _ => HsList.dropWhile(~A, ~p, t), _ => x <> t)\n\ndef HsList.span.cons(~A: Data, x: A, r: Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:\n  match r:\n    case Tuple{a, b}:\n      Tuple{x <> a, b}\n\ndef HsList.span(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:\n  match xs:\n    case Nil{}:\n      Tuple{Nil{}, Nil{}}\n    case +x <> +t:\n      HsBool.if(Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, p(x), _ => HsList.span.cons(~A, x, HsList.span(~A, ~p, t)), _ => Tuple{Nil{}, x <> t})\n\ndef HsList.break(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:\n  HsList.span(~A, ~(y => Bool.not(p(y))), xs)\n\n"

def fd.hsprelude.l3() -> String:
  "def HsList.partition.put(~A: Data, x: A, keep: Bool, r: Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:\n  match keep r:\n    case True{} Tuple{a, b}:\n      Tuple{x <> a, b}\n    case False{} Tuple{a, b}:\n      Tuple{a, x <> b}\n\ndef HsList.partition(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>:\n  match xs:\n    case Nil{}:\n      Tuple{Nil{}, Nil{}}\n    case +x <> t:\n      HsList.partition.put(~A, x, p(x), HsList.partition(~A, ~p, t))\n\ndef HsList.find(~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Maybe<&2, A>:\n  match xs:\n    case Nil{}:\n      None{}\n    case +x <> t:\n      HsBool.if(Maybe<&2, A>, p(x), _ => Some{x}, _ => HsList.find(~A, ~p, t))\n\ndef HsList.notElem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Bool:\n  match xs:\n    case Nil{}:\n      True{}\n    case y <> t:\n      HsBool.if(Bool, eq(x)(y), _ => False{}, _ => HsList.notElem(~A, ~eq, x, t))\n\ndef HsList.elem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Bool:\n  Bool.not(HsList.notElem(~A, ~eq, x, xs))\n\ndef HsList.elemBy(~A: Data, ~eq: A -> A -> Bool, +x: A, ys: List<&2, A>) -> Bool:\n  match ys:\n    case Nil{}:\n      False{}\n    case y <> t:\n      HsBool.if(Bool, eq(y)(x), _ => True{}, _ => HsList.elemBy(~A, ~eq, x, t))\n\ndef HsList.nubBy.go(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +seen: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case +x <> +t:\n      HsBool.if(List<&2, A>, HsList.elemBy(~A, ~eq, x, seen), _ => HsList.nubBy.go(~A, ~eq, t, seen), _ => x <> HsList.nubBy.go(~A, ~eq, t, x <> seen))\n\ndef HsList.nubBy(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:\n  HsList.nubBy.go(~A, ~eq, xs, Nil{})\n\ndef HsList.nub(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:\n  HsList.nubBy.go(~A, ~eq, xs, Nil{})\n\ndef HsList.isPrefixOf(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:\n  match xs ys:\n    case Nil{} _:\n      True{}\n    case _ Nil{}:\n      False{}\n    case x <> xt y <> yt:\n      HsBool.if(Bool, eq(x)(y), _ => HsList.isPrefixOf(~A, ~eq, xt, yt), _ => False{})\n\ndef HsList.isSuffixOf(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:\n  HsList.isPrefixOf(~A, ~eq, List.reverse(&2, A, xs), List.reverse(&2, A, ys))\n\ndef HsList.isInfixOf(~A: Data, ~eq: A -> A -> Bool, +xs: List<&2, A>, ys: List<&2, A>) -> Bool:\n  match ys:\n    case Nil{}:\n      HsList.isPrefixOf(~A, ~eq, xs, Nil{})\n    case +y <> +t:\n      HsBool.if(Bool, HsList.isPrefixOf(~A, ~eq, xs, y <> t), _ => True{}, _ => HsList.isInfixOf(~A, ~eq, xs, t))\n\ndef HsList.stripPrefix(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Maybe<&2, List<&2, A>>:\n  match xs ys:\n    case Nil{} r:\n      Some{r}\n    case _ Nil{}:\n      None{}\n    case x <> xt y <> yt:\n      HsBool.if(Maybe<&2, List<&2, A>>, eq(x)(y), _ => HsList.stripPrefix(~A, ~eq, xt, yt), _ => None{})\n\n"

def fd.hsprelude.l4() -> String:
  "def HsList.intersperse.go(~A: Data, +s: A, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      s <> x <> HsList.intersperse.go(~A, s, t)\n\ndef HsList.intersperse(~A: Data, +s: A, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      x <> HsList.intersperse.go(~A, s, t)\n\ndef HsList.intercalate(~A: Data, +s: List<&2, A>, xss: List<&2, List<&2, A>>) -> List<&2, A>:\n  List.concat(&2, A, HsList.intersperse(~List<&2, A>, s, xss))\n\ndef HsList.unlines(xs: List<&2, List<&2, Char>>) -> List<&2, Char>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case l <> t:\n      List.append(&2, Char, l, '\\n' <> HsList.unlines(t))\n\ndef HsList.unwords(xs: List<&2, List<&2, Char>>) -> List<&2, Char>:\n  HsList.intercalate(~Char, [' '], xs)\n\ndef HsList.flush(cur: List<&2, Char>, rest: List<&2, List<&2, Char>>) -> List<&2, List<&2, Char>>:\n  match cur:\n    case Nil{}:\n      rest\n    case c <> t:\n      List.reverse(&2, Char, c <> t) <> rest\n\ndef HsList.lines.go(s: List<&2, Char>, +cur: List<&2, Char>) -> List<&2, List<&2, Char>>:\n  match s:\n    case Nil{}:\n      HsList.flush(cur, Nil{})\n    case +c <> +t:\n      HsBool.if(List<&2, List<&2, Char>>, Char.is_eq(c, '\\n'), _ => List.reverse(&2, Char, cur) <> HsList.lines.go(t, Nil{}), _ => HsList.lines.go(t, c <> cur))\n\ndef HsList.lines(s: List<&2, Char>) -> List<&2, List<&2, Char>>:\n  HsList.lines.go(s, Nil{})\n\ndef HsList.isSpace(c: Char) -> Bool:\n  Char.is_space(c)\n\ndef HsList.words.go(s: List<&2, Char>, +cur: List<&2, Char>) -> List<&2, List<&2, Char>>:\n  match s:\n    case Nil{}:\n      HsList.flush(cur, Nil{})\n    case +c <> +t:\n      HsBool.if(List<&2, List<&2, Char>>, Char.is_space(c), _ => HsList.flush(cur, HsList.words.go(t, Nil{})), _ => HsList.words.go(t, c <> cur))\n\ndef HsList.words(s: List<&2, Char>) -> List<&2, List<&2, Char>>:\n  HsList.words.go(s, Nil{})\n\ndef HsList.insertBy(~A: Data, ~cmp: A -> A -> Cmp, +x: A, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      [x]\n    case +y <> +t:\n      HsCmp.on(List<&2, A>, cmp(x)(y), _ => x <> y <> t, _ => x <> y <> t, _ => y <> HsList.insertBy(~A, ~cmp, x, t))\n\ndef HsList.sortBy(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      HsList.insertBy(~A, ~cmp, x, HsList.sortBy(~A, ~cmp, t))\n\ndef HsList.sort(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>) -> List<&2, A>:\n  HsList.sortBy(~A, ~cmp, xs)\n\ndef HsList.sortOn(~B: Data, ~A: Data, ~cmp: B -> B -> Cmp, ~f: A -> B, xs: List<&2, A>) -> List<&2, A>:\n  HsList.sortBy(~A, ~(x => y => cmp(f(x))(f(y))), xs)\n\n"

def fd.hsprelude.l5() -> String:
  "def HsList.groupBy.go(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +h: A, +cur: List<&2, A>) -> List<&2, List<&2, A>>:\n  match xs:\n    case Nil{}:\n      [h <> List.reverse(&2, A, cur)]\n    case +y <> +t:\n      HsBool.if(List<&2, List<&2, A>>, eq(h)(y), _ => HsList.groupBy.go(~A, ~eq, t, h, y <> cur), _ => (h <> List.reverse(&2, A, cur)) <> HsList.groupBy.go(~A, ~eq, t, y, Nil{}))\n\ndef HsList.groupBy(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>) -> List<&2, List<&2, A>>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      HsList.groupBy.go(~A, ~eq, t, x, Nil{})\n\ndef HsList.group(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>) -> List<&2, List<&2, A>>:\n  HsList.groupBy(~A, ~eq, xs)\n\ndef HsList.tails(~A: Data, xs: List<&2, A>) -> List<&2, List<&2, A>>:\n  match xs:\n    case Nil{}:\n      [Nil{}]\n    case +x <> +t:\n      (x <> t) <> HsList.tails(~A, t)\n\ndef HsList.consAll(~A: Data, +x: A, xss: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:\n  match xss:\n    case Nil{}:\n      Nil{}\n    case ys <> t:\n      (x <> ys) <> HsList.consAll(~A, x, t)\n\ndef HsList.inits(~A: Data, xs: List<&2, A>) -> List<&2, List<&2, A>>:\n  match xs:\n    case Nil{}:\n      [Nil{}]\n    case +x <> t:\n      Nil{} <> HsList.consAll(~A, x, HsList.inits(~A, t))\n\ndef HsList.mapMaybe.put(~B: Data, m: Maybe<&2, B>, r: List<&2, B>) -> List<&2, B>:\n  match m:\n    case None{}:\n      r\n    case Some{y}:\n      y <> r\n\ndef HsList.mapMaybe(~A: Data, ~B: Data, ~f: A -> Maybe<&2, B>, xs: List<&2, A>) -> List<&2, B>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case x <> t:\n      HsList.mapMaybe.put(~B, f(x), HsList.mapMaybe(~A, ~B, ~f, t))\n\ndef HsList.catMaybes(~A: Data, xs: List<&2, Maybe<&2, A>>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case None{} <> t:\n      HsList.catMaybes(~A, t)\n    case Some{y} <> t:\n      y <> HsList.catMaybes(~A, t)\n\ndef HsList.isJust(~A: Data, m: Maybe<&2, A>) -> Bool:\n  match m:\n    case None{}:\n      False{}\n    case Some{x}:\n      True{}\n\ndef HsList.isNothing(~A: Data, m: Maybe<&2, A>) -> Bool:\n  match m:\n    case None{}:\n      True{}\n    case Some{x}:\n      False{}\n\ndef HsList.listToMaybe(~A: Data, xs: List<&2, A>) -> Maybe<&2, A>:\n  match xs:\n    case Nil{}:\n      None{}\n    case x <> t:\n      Some{x}\n\ndef HsList.maybeToList(~A: Data, m: Maybe<&2, A>) -> List<&2, A>:\n  match m:\n    case None{}:\n      Nil{}\n    case Some{x}:\n      [x]\n\ndef HsList.lefts(~A: Data, ~B: Data, xs: List<&2, Either<&2, &2, A, B>>) -> List<&2, A>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case Inl{a} <> t:\n      a <> HsList.lefts(~A, ~B, t)\n    case Inr{b} <> t:\n      HsList.lefts(~A, ~B, t)\n\ndef HsList.rights(~A: Data, ~B: Data, xs: List<&2, Either<&2, &2, A, B>>) -> List<&2, B>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case Inl{a} <> t:\n      HsList.rights(~A, ~B, t)\n    case Inr{b} <> t:\n      b <> HsList.rights(~A, ~B, t)\n\n"

def fd.hsprelude.l6() -> String:
  "def HsList.partitionEithers.put(~A: Data, ~B: Data, e: Either<&2, &2, A, B>, p: Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>:\n  match e p:\n    case Inl{a} Tuple{l, r}:\n      Tuple{a <> l, r}\n    case Inr{b} Tuple{l, r}:\n      Tuple{l, b <> r}\n\ndef HsList.partitionEithers(~A: Data, ~B: Data, xs: List<&2, Either<&2, &2, A, B>>) -> Sigma<&2, &2, List<&2, A>, _ => List<&2, B>>:\n  match xs:\n    case Nil{}:\n      Tuple{Nil{}, Nil{}}\n    case e <> t:\n      HsList.partitionEithers.put(~A, ~B, e, HsList.partitionEithers(~A, ~B, t))\n\ndef HsList.isLeft(~A: Data, ~B: Data, e: Either<&2, &2, A, B>) -> Bool:\n  match e:\n    case Inl{a}:\n      True{}\n    case Inr{b}:\n      False{}\n\ndef HsList.isRight(~A: Data, ~B: Data, e: Either<&2, &2, A, B>) -> Bool:\n  match e:\n    case Inl{a}:\n      False{}\n    case Inr{b}:\n      True{}\n\ndef HsList.fromLeft(~A: Data, ~B: Data, d: A, e: Either<&2, &2, A, B>) -> A:\n  match e:\n    case Inl{a}:\n      a\n    case Inr{b}:\n      d\n\ndef HsList.fromRight(~A: Data, ~B: Data, d: B, e: Either<&2, &2, A, B>) -> B:\n  match e:\n    case Inl{a}:\n      d\n    case Inr{b}:\n      b\n\ndef HsList.first.either(~A: Data, ~B: Data, ~C: Data, f: A -> B, e: Either<&2, &2, A, C>) -> Either<&2, &2, B, C>:\n  match e:\n    case Inl{a}:\n      Inl{f(a)}\n    case Inr{c}:\n      Inr{c}\n\ndef HsList.second.either(~B: Data, ~C: Data, ~A: Data, f: B -> C, e: Either<&2, &2, A, B>) -> Either<&2, &2, A, C>:\n  match e:\n    case Inl{a}:\n      Inl{a}\n    case Inr{b}:\n      Inr{f(b)}\n\ndef HsList.bimap.either(~A: Data, ~B: Data, ~C: Data, ~D: Data, f: A -> B, g: C -> D, e: Either<&2, &2, A, C>) -> Either<&2, &2, B, D>:\n  match e:\n    case Inl{a}:\n      Inl{f(a)}\n    case Inr{c}:\n      Inr{g(c)}\n\ndef HsList.first.pair(~A: Data, ~B: Data, ~C: Data, f: A -> B, p: Sigma<&2, &2, A, _ => C>) -> Sigma<&2, &2, B, _ => C>:\n  match p:\n    case Tuple{a, c}:\n      Tuple{f(a), c}\n\ndef HsList.second.pair(~B: Data, ~C: Data, ~A: Data, f: B -> C, p: Sigma<&2, &2, A, _ => B>) -> Sigma<&2, &2, A, _ => C>:\n  match p:\n    case Tuple{a, b}:\n      Tuple{a, f(b)}\n\ndef HsList.bimap.pair(~A: Data, ~B: Data, ~C: Data, ~D: Data, f: A -> B, g: C -> D, p: Sigma<&2, &2, A, _ => C>) -> Sigma<&2, &2, B, _ => D>:\n  match p:\n    case Tuple{a, c}:\n      Tuple{f(a), g(c)}\n\n# Data.Foldable's toList at a list (the fold gives a Set's or a Map's as one)\n\ndef HsList.toList(~A: Data, xs: List<&2, A>) -> List<&2, A>:\n  xs\n\n# Data.Sequence's Seq a is a list here (front first), ViewL a too (EmptyL\n# Nil, x :< s a cons): empty, |>, <| and viewl\ndef HsList.nil(~A: Data) -> List<&2, A>:\n  Nil{}\n\ndef HsList.snoc(~A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:\n  List.append(&2, A, xs, [x])\n\ndef HsList.cons(~A: Data, x: A, xs: List<&2, A>) -> List<&2, A>:\n  x <> xs\n\n"

def fd.hsprelude.l7() -> String:
  "# foldr and foldl at a list, an element the function may copy (Base's take\n# it once)\ndef HsList.foldr(~A: Data, ~B: Type, ~f: A -> B -> B, xs: List<&2, A>, z: B) -> B:\n  match xs:\n    case Nil{}:\n      z\n    case +h <> t:\n      f(h, HsList.foldr(~A, ~B, ~f, t, z))\n\ndef HsList.foldl(~A: Data, ~B: Type, ~f: B -> A -> B, xs: List<&2, A>, acc: B) -> B:\n  match xs:\n    case Nil{}:\n      acc\n    case +h <> t:\n      HsList.foldl(~A, ~B, ~f, t, f(acc, h))\n\n# Haskell's Show at base's types (GHC.Show), ShowS a String -> String:\n# showString, showChar, showParen, showSpace, showCommaSpace, showsPrec at\n# Int (HsInt), Char, String, Bool, (), lists and Maybe, with GHC's escapes\n\n# showsPrec at Int: a negative number in parentheses above precedence 6\n\n# GHC's asciiTab: the names of the control characters\n\n# protectEsc: \\& before what would read as part of the escape\n\n# GHC's showLitChar c, s the text after it\n\n# showLitString: a string's characters, \" escaped\n\n# showList__: [x, y] given showsPrec 0 at the element\n\n# Maybe's showsPrec, given showsPrec at the element\n\ndef HsShow.string(s: List<&2, Char>, r: List<&2, Char>) -> List<&2, Char>:\n  List.append(&2, Char, s, r)\n\ndef HsShow.char(c: Char, r: List<&2, Char>) -> List<&2, Char>:\n  c <> r\n\ndef HsShow.paren(b: Bool, p: List<&2, Char> -> List<&2, Char>, r: List<&2, Char>) -> List<&2, Char>:\n  match b:\n    case True{}:\n      '(' <> p(')' <> r)\n    case False{}:\n      p(r)\n\ndef HsShow.space(r: List<&2, Char>) -> List<&2, Char>:\n  ' ' <> r\n\ndef HsShow.commaSpace(r: List<&2, Char>) -> List<&2, Char>:\n  ',' <> ' ' <> r\n\ndef HsShow.digits(n: Nat) -> List<&2, Char>:\n  String.to_list(Nat.show(n))\n\ndef HsShow.int(d: HsInt, n: HsInt, r: List<&2, Char>) -> List<&2, Char>:\n  match n:\n    case HsInt.Pos{k}:\n      List.append(&2, Char, HsShow.digits(k), r)\n    case HsInt.Neg{k}:\n      HsShow.paren(HsInt.is_gt(d, HsInt.Pos{6n}), s => '-' <> List.append(&2, Char, HsShow.digits(k), s), r)\n\ndef HsShow.nat(d: Nat, n: Nat, r: List<&2, Char>) -> List<&2, Char>:\n  List.append(&2, Char, HsShow.digits(n), r)\n\ndef HsShow.bool(b: Bool, r: List<&2, Char>) -> List<&2, Char>:\n  match b:\n    case True{}:\n      List.append(&2, Char, String.to_list(\"True\"), r)\n    case False{}:\n      List.append(&2, Char, String.to_list(\"False\"), r)\n\ndef HsShow.unit(u: Unit, r: List<&2, Char>) -> List<&2, Char>:\n  '(' <> ')' <> r\n\n"

def fd.hsprelude.l8() -> String:
  "def HsShow.asciiTab() -> List<&2, List<&2, Char>>:\n  [String.to_list(\"NUL\"), String.to_list(\"SOH\"), String.to_list(\"STX\"), String.to_list(\"ETX\"), String.to_list(\"EOT\"), String.to_list(\"ENQ\"), String.to_list(\"ACK\"), String.to_list(\"BEL\"), String.to_list(\"BS\"), String.to_list(\"HT\"), String.to_list(\"LF\"), String.to_list(\"VT\"), String.to_list(\"FF\"), String.to_list(\"CR\"), String.to_list(\"SO\"), String.to_list(\"SI\"), String.to_list(\"DLE\"), String.to_list(\"DC1\"), String.to_list(\"DC2\"), String.to_list(\"DC3\"), String.to_list(\"DC4\"), String.to_list(\"NAK\"), String.to_list(\"SYN\"), String.to_list(\"ETB\"), String.to_list(\"CAN\"), String.to_list(\"EM\"), String.to_list(\"SUB\"), String.to_list(\"ESC\"), String.to_list(\"FS\"), String.to_list(\"GS\"), String.to_list(\"RS\"), String.to_list(\"US\")]\n\ndef HsShow.protect(digit: Bool, s: List<&2, Char>) -> List<&2, Char>:\n  match s:\n    case Nil{}:\n      Nil{}\n    case +c <> +t:\n      HsBool.if(List<&2, Char>, Bool.pick(Bool, digit, Char.is_digit(c), Char.is_eq(c, 'H')), _ => '\\\\' <> '&' <> c <> t, _ => c <> t)\n\ndef HsShow.esc(+e: List<&2, Char>, s: List<&2, Char>) -> List<&2, Char>:\n  '\\\\' <> List.append(&2, Char, e, s)\n\ndef HsShow.litCtl(+n: Nat, +s: List<&2, Char>) -> List<&2, Char>:\n  HsBool.if(List<&2, Char>, Nat.is_eq(n, 7n), _ => HsShow.esc(['a'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 8n), _ => HsShow.esc(['b'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 12n), _ => HsShow.esc(['f'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 10n), _ => HsShow.esc(['n'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 13n), _ => HsShow.esc(['r'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 9n), _ => HsShow.esc(['t'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 11n), _ => HsShow.esc(['v'], s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 14n), _ => HsShow.esc(String.to_list(\"SO\"), HsShow.protect(False{}, s)), _ => HsShow.esc(Maybe.default(&2, List<&2, Char>, List.get(&2, List<&2, Char>, HsShow.asciiTab(), n), Nil{}), s)))))))))\n\ndef HsShow.litChar(+c: Char, +s: List<&2, Char>) -> List<&2, Char>:\n  +n = U32.to_nat(Char.to_u32(c))\n  HsBool.if(List<&2, Char>, Nat.is_gt(n, 127n), _ => '\\\\' <> List.append(&2, Char, HsShow.digits(n), HsShow.protect(True{}, s)), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 127n), _ => HsShow.esc(String.to_list(\"DEL\"), s), _ => HsBool.if(List<&2, Char>, Nat.is_eq(n, 92n), _ => '\\\\' <> '\\\\' <> s, _ => HsBool.if(List<&2, Char>, Nat.is_ge(n, 32n), _ => c <> s, _ => HsShow.litCtl(n, s)))))\n\ndef HsShow.litString(cs: List<&2, Char>, +r: List<&2, Char>) -> List<&2, Char>:\n  match cs:\n    case Nil{}:\n      r\n    case +c <> +t:\n      HsBool.if(List<&2, Char>, Char.is_eq(c, '\"'), _ => '\\\\' <> '\"' <> HsShow.litString(t, r), _ => HsShow.litChar(c, HsShow.litString(t, r)))\n\ndef HsShow.str(cs: List<&2, Char>, r: List<&2, Char>) -> List<&2, Char>:\n  '\"' <> HsShow.litString(cs, '\"' <> r)\n\n"

def fd.hsprelude.l9() -> String:
  "def HsShow.charq(+c: Char, +r: List<&2, Char>) -> List<&2, Char>:\n  HsBool.if(List<&2, Char>, Char.is_eq(c, '\\''), _ => List.append(&2, Char, ['\\'', '\\\\', '\\'', '\\''], r), _ => '\\'' <> HsShow.litChar(c, '\\'' <> r))\n\ndef HsShow.list.rest(~A: Data, ~sh: A -> List<&2, Char> -> List<&2, Char>, xs: List<&2, A>, r: List<&2, Char>) -> List<&2, Char>:\n  match xs:\n    case Nil{}:\n      ']' <> r\n    case x <> t:\n      ',' <> sh(x)(HsShow.list.rest(~A, ~sh, t, r))\n\ndef HsShow.list(~A: Data, ~sh: A -> List<&2, Char> -> List<&2, Char>, xs: List<&2, A>, r: List<&2, Char>) -> List<&2, Char>:\n  match xs:\n    case Nil{}:\n      '[' <> ']' <> r\n    case x <> t:\n      '[' <> sh(x)(HsShow.list.rest(~A, ~sh, t, r))\n\ndef HsShow.maybe(~A: Data, ~sh: HsInt -> A -> List<&2, Char> -> List<&2, Char>, d: HsInt, m: Maybe<&2, A>, r: List<&2, Char>) -> List<&2, Char>:\n  match m:\n    case None{}:\n      List.append(&2, Char, String.to_list(\"Nothing\"), r)\n    case Some{x}:\n      HsShow.paren(HsInt.is_ge(d, HsInt.Pos{11n}), s => List.append(&2, Char, String.to_list(\"Just \"), sh(HsInt.Pos{11n})(x)(s)), r)\n\n# base's default show and showList, given the instance's showsPrec\ndef HsShow.via(~A: Data, ~sp: HsInt -> A -> List<&2, Char> -> List<&2, Char>, x: A) -> List<&2, Char>:\n  sp(HsInt.Pos{0n})(x)(Nil{})\n\ndef HsShow.listVia(~A: Data, ~sp: HsInt -> A -> List<&2, Char> -> List<&2, Char>, xs: List<&2, A>, r: List<&2, Char>) -> List<&2, Char>:\n  HsShow.list(~A, ~(y => s => sp(HsInt.Pos{0n})(y)(s)), xs, r)\n\n\n"

def fd.hsprelude.lists() -> String:
  fd.hsprelude.l1() ++ fd.hsprelude.l2() ++ fd.hsprelude.l3() ++ fd.hsprelude.l4() ++ fd.hsprelude.l5() ++ fd.hsprelude.l6() ++ fd.hsprelude.l7() ++ fd.hsprelude.l8() ++ fd.hsprelude.l9()

def fd.hsprelude.write(+out: String) -> IO(Unit):
  S.write(out ++ "/HsPrelude.bend", S.b(fd.hsprelude() ++ "\n" ++ fd.hsprelude.maps() ++ fd.hsprelude.ints() ++ fd.hsprelude.digests() ++ fd.hsprelude.lists() ++ PR.pre.HsChar() ++ PR.pre.HsPc() ++ PR.pre.HsRational() ++ PR.pre.HsMapMore() ++ PR.pre.HsPartial() ++ PR.pre.HsOrd() ++ PR.pre.HsMonad() ++ PR.pre.HsShowMore()))

# the files a module's text may name: HsPrelude's and the package's
# earlier modules'
def fd.ims(+px: Px) -> List<&2, List<&2, U32>>:
  S.b("HsPrelude") <> fd.px.files(px)

# Maybe's and Either's monad and functions Base lacks (Base has Maybe.bind,
# Maybe.map and Maybe.default)
def fd.pre.either.bind() -> String:
  "# Either's >>= (a Left stops the rest)\ndef hs.either.bind(-E: Data, -A: Data, -B: Data, m: Either<&2, &2, E, A>, f: A -> Either<&2, &2, E, B>) -> Either<&2, &2, E, B>:\n  match m:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      f(a)\n\n"

def fd.pre.either.map() -> String:
  "# Either's fmap\ndef hs.either.map(-E: Data, -A: Data, -B: Data, f: A -> B, m: Either<&2, &2, E, A>) -> Either<&2, &2, E, B>:\n  match m:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      Inr{f(a)}\n\n"

def fd.pre.maybe.alt() -> String:
  "# Maybe's <|> (Alternative): the first Just, the second a thunk\ndef hs.maybe.alt(-A: Data, x: Maybe<&2, A>, y: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:\n  match x:\n    case None{}:\n      y(Unit{})\n    case Some{a}:\n      Some{a}\n\n"

def fd.pre.maybe() -> String:
  "# Haskell's maybe (B a Type: a monad's action, a function, is one)\ndef hs.maybe(-A: Data, -B: Type, d: B, f: A -> B, m: Maybe<&2, A>) -> B:\n  match m:\n    case None{}:\n      d\n    case Some{x}:\n      f(x)\n\n"

def fd.pre.either() -> String:
  "# Haskell's either (C a Type: a function is one)\ndef hs.either(-A: Data, -B: Data, -C: Type, f: A -> C, g: B -> C, e: Either<&2, &2, A, B>) -> C:\n  match e:\n    case Inl{a}:\n      f(a)\n    case Inr{b}:\n      g(b)\n\n"

def fd.pre.state() -> String:
  "# State s a (Control.Monad.Trans.State): S -> A & S, a function of the\n# state to a result and the next state; mtl's MonadState methods at it\ndef hs.state.bind.go(-S: Data, -A: Type, -B: Type, p: Sigma<&1, &1, A, _ => S>, f: A -> S -> Sigma<&1, &1, B, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (a, s) = p\n  f(a)(s)\n\ndef hs.state.bind(-S: Data, -A: Type, -B: Type, m: S -> Sigma<&1, &1, A, _ => S>, f: A -> S -> Sigma<&1, &1, B, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.bind.go(S, A, B, m(s), f)\n\ndef hs.state.pure(-S: Data, -A: Type, a: A) -> S -> Sigma<&1, &1, A, _ => S>:\n  s => (a, s)\n\ndef hs.state.map.go(-S: Data, -A: Type, -B: Type, f: A -> B, p: Sigma<&1, &1, A, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (a, s) = p\n  (f(a), s)\n\ndef hs.state.map(-S: Data, -A: Type, -B: Type, f: A -> B, m: S -> Sigma<&1, &1, A, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.map.go(S, A, B, f, m(s))\n\ndef hs.state.ap.go(-S: Data, -A: Type, -B: Type, p: Sigma<&1, &1, (A -> B), _ => S>, m: S -> Sigma<&1, &1, A, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (f, s) = p\n  hs.state.map.go(S, A, B, f, m(s))\n\ndef hs.state.ap(-S: Data, -A: Type, -B: Type, mf: S -> Sigma<&1, &1, (A -> B), _ => S>, m: S -> Sigma<&1, &1, A, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.ap.go(S, A, B, mf(s), m)\n\ndef hs.state.dup(-S: Data, +s: S) -> Sigma<&1, &1, S, _ => S>:\n  (s, s)\n\ndef hs.state.get(-S: Data) -> S -> Sigma<&1, &1, S, _ => S>:\n  s => hs.state.dup(S, s)\n\ndef hs.state.put(-S: Data, s: S) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  _ => (Unit{}, s)\n\ndef hs.state.modify(-S: Data, f: S -> S) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  s => (Unit{}, f(s))\n\ndef hs.state.gets.go(-S: Data, -A: Type, f: S -> A, +s: S) -> Sigma<&1, &1, A, _ => S>:\n  (f(s), s)\n\ndef hs.state.gets(-S: Data, -A: Type, f: S -> A) -> S -> Sigma<&1, &1, A, _ => S>:\n  s => hs.state.gets.go(S, A, f, s)\n\ndef hs.state.fst(-S: Data, -A: Type, p: Sigma<&1, &1, A, _ => S>) -> A:\n  (a, s) = p\n  a\n\ndef hs.state.snd(-S: Data, -A: Type, p: Sigma<&1, &1, A, _ => S>) -> S:\n  (a, s) = p\n  s\n\ndef hs.state.re(-S: Data, -A: Data, p: Sigma<&1, &1, A, _ => S>) -> Sigma<&2, &2, A, _ => S>:\n  (a, s) = p\n  (a, s)\n\ndef hs.state.eval(-S: Data, -A: Type, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> A:\n  hs.state.fst(S, A, m(s))\n\ndef hs.state.exec(-S: Data, -A: Type, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> S:\n  hs.state.snd(S, A, m(s))\n\ndef hs.state.run(-S: Data, -A: Data, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> Sigma<&2, &2, A, _ => S>:\n  hs.state.re(S, A, m(s))\n\n# mapM_ / forM_, mapM / forM / traverse and foldM at a list\ndef hs.state.mapm_(~S: Data, ~A: Data, ~B: Type, ~f: A -> S -> Sigma<&1, &1, B, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.state.pure(S, Unit, Unit{})\n    case h <> t:\n      hs.state.bind(S, B, Unit, f(h), _ => hs.state.mapm_(~S, ~A, ~B, ~f, t))\n\ndef hs.state.mapm(~S: Data, ~A: Data, ~B: Data, ~f: A -> S -> Sigma<&1, &1, B, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, List<&2, B>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.state.pure(S, List<&2, B>, Nil{})\n    case h <> t:\n      hs.state.bind(S, B, List<&2, B>, f(h), b => hs.state.map(S, List<&2, B>, List<&2, B>, bs => b <> bs, hs.state.mapm(~S, ~A, ~B, ~f, t)))\n\ndef hs.state.foldm(~S: Data, ~A: Data, ~B: Type, ~f: B -> A -> S -> Sigma<&1, &1, B, _ => S>, xs: List<&2, A>, z: B) -> S -> Sigma<&1, &1, B, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.state.pure(S, B, z)\n    case h <> t:\n      hs.state.bind(S, B, B, f(z)(h), y => hs.state.foldm(~S, ~A, ~B, ~f, t, y))\n\n# sequence (sequenceA) at a list of actions (closures: List<&1, ..>): mapM id\ndef hs.state.seq(~S: Data, ~A: Data, xs: List<&1, S -> Sigma<&1, &1, A, _ => S>>) -> S -> Sigma<&1, &1, List<&2, A>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.state.pure(S, List<&2, A>, Nil{})\n    case h <> t:\n      hs.state.bind(S, A, List<&2, A>, h, b => hs.state.map(S, List<&2, A>, List<&2, A>, bs => b <> bs, hs.state.seq(~S, ~A, t)))\n\n"

# ExceptT over State (see Types): hs.exs.*, mtl's MonadState and
# MonadError methods at it, and mapM_/mapM/foldM
def fd.pre.exs() -> String:
  "# ExceptT e (State s) a (Control.Monad.Trans.Except over\n# Control.Monad.Trans.State): S -> Either E A & S, a State whose result is an\n# Either (ExceptT's newtype: m (Either e a)); mtl's MonadState and\n# MonadError methods at it\ndef hs.exs.bind.go(-E: Data, -S: Data, -A: Data, -B: Data, r: Either<&2, &2, E, A>, f: A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>, s: S) -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  match r:\n    case Inl{e}:\n      (Inl{e}, s)\n    case Inr{a}:\n      f(a)(s)\n\ndef hs.exs.bind.p(-E: Data, -S: Data, -A: Data, -B: Data, p: Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>, f: A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>) -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  (r, s) = p\n  hs.exs.bind.go(E, S, A, B, r, f, s)\n\ndef hs.exs.bind(-E: Data, -S: Data, -A: Data, -B: Data, m: S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>, f: A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>) -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  s => hs.exs.bind.p(E, S, A, B, m(s), f)\n\ndef hs.exs.pure(-E: Data, -S: Data, -A: Data, a: A) -> S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>:\n  s => (Inr{a}, s)\n\ndef hs.exs.throw(-E: Data, -S: Data, -A: Data, e: E) -> S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>:\n  s => (Inl{e}, s)\n\ndef hs.exs.map.r(-E: Data, -A: Data, -B: Data, f: A -> B, r: Either<&2, &2, E, A>) -> Either<&2, &2, E, B>:\n  match r:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      Inr{f(a)}\n\ndef hs.exs.map.go(-E: Data, -S: Data, -A: Data, -B: Data, f: A -> B, p: Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>) -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  (r, s) = p\n  (hs.exs.map.r(E, A, B, f, r), s)\n\ndef hs.exs.map(-E: Data, -S: Data, -A: Data, -B: Data, f: A -> B, m: S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>) -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  s => hs.exs.map.go(E, S, A, B, f, m(s))\n\ndef hs.exs.dup(-E: Data, -S: Data, +s: S) -> Sigma<&1, &1, Either<&2, &2, E, S>, _ => S>:\n  (Inr{s}, s)\n\ndef hs.exs.get(-E: Data, -S: Data) -> S -> Sigma<&1, &1, Either<&2, &2, E, S>, _ => S>:\n  s => hs.exs.dup(E, S, s)\n\ndef hs.exs.put(-E: Data, -S: Data, s: S) -> S -> Sigma<&1, &1, Either<&2, &2, E, Unit>, _ => S>:\n  _ => (Inr{Unit{}}, s)\n\ndef hs.exs.modify(-E: Data, -S: Data, f: S -> S) -> S -> Sigma<&1, &1, Either<&2, &2, E, Unit>, _ => S>:\n  s => (Inr{Unit{}}, f(s))\n\ndef hs.exs.gets.go(-E: Data, -S: Data, -A: Data, f: S -> A, +s: S) -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>:\n  (Inr{f(s)}, s)\n\ndef hs.exs.gets(-E: Data, -S: Data, -A: Data, f: S -> A) -> S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>:\n  s => hs.exs.gets.go(E, S, A, f, s)\n\n# mapM_ / forM_, mapM / forM / traverse and foldM at a list\ndef hs.exs.mapm_(~E: Data, ~S: Data, ~A: Data, ~B: Data, ~f: A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, Either<&2, &2, E, Unit>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.exs.pure(E, S, Unit, Unit{})\n    case h <> t:\n      hs.exs.bind(E, S, B, Unit, f(h), _ => hs.exs.mapm_(~E, ~S, ~A, ~B, ~f, t))\n\ndef hs.exs.mapm(~E: Data, ~S: Data, ~A: Data, ~B: Data, ~f: A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, Either<&2, &2, E, List<&2, B>>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.exs.pure(E, S, List<&2, B>, Nil{})\n    case h <> t:\n      hs.exs.bind(E, S, B, List<&2, B>, f(h), b => hs.exs.map(E, S, List<&2, B>, List<&2, B>, bs => b <> bs, hs.exs.mapm(~E, ~S, ~A, ~B, ~f, t)))\n\ndef hs.exs.foldm(~E: Data, ~S: Data, ~A: Data, ~B: Data, ~f: B -> A -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>, xs: List<&2, A>, z: B) -> S -> Sigma<&1, &1, Either<&2, &2, E, B>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.exs.pure(E, S, B, z)\n    case h <> t:\n      hs.exs.bind(E, S, B, B, f(z)(h), y => hs.exs.foldm(~E, ~S, ~A, ~B, ~f, t, y))\n\n# sequence (sequenceA) at a list of actions (closures: List<&1, ..>): mapM id\ndef hs.exs.seq(~E: Data, ~S: Data, ~A: Data, xs: List<&1, S -> Sigma<&1, &1, Either<&2, &2, E, A>, _ => S>>) -> S -> Sigma<&1, &1, Either<&2, &2, E, List<&2, A>>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.exs.pure(E, S, List<&2, A>, Nil{})\n    case h <> t:\n      hs.exs.bind(E, S, A, List<&2, A>, h, b => hs.exs.map(E, S, List<&2, A>, List<&2, A>, bs => b <> bs, hs.exs.seq(~E, ~S, ~A, t)))\n\n"

# filterM and zipWithM_ at State and at ExceptT over State (see fd.mlist.at)
def fd.pre.statem() -> String:
  "# filterM and zipWithM_ at a list (State)\ndef hs.state.keep(-A: Data, k: Bool, x: A, ys: List<&2, A>) -> List<&2, A>:\n  match k:\n    case True{}:\n      x <> ys\n    case False{}:\n      ys\n\ndef hs.state.filterm(~S: Data, ~A: Data, ~p: A -> S -> Sigma<&1, &1, Bool, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, List<&2, A>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.state.pure(S, List<&2, A>, Nil{})\n    case +h <> t:\n      hs.state.bind(S, Bool, List<&2, A>, p(h), k => hs.state.map(S, List<&2, A>, List<&2, A>, ys => hs.state.keep(A, k, h, ys), hs.state.filterm(~S, ~A, ~p, t)))\n\ndef hs.state.zipwithm_(~S: Data, ~A: Data, ~B: Data, ~C: Type, ~f: A -> B -> S -> Sigma<&1, &1, C, _ => S>, xs: List<&2, A>, ys: List<&2, B>) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  match xs ys:\n    case x <> xt y <> yt:\n      hs.state.bind(S, C, Unit, f(x)(y), _ => hs.state.zipwithm_(~S, ~A, ~B, ~C, ~f, xt, yt))\n    case _ _:\n      hs.state.pure(S, Unit, Unit{})\n\n"

def fd.pre.exsm() -> String:
  "# filterM and zipWithM_ at a list (ExceptT over State)\ndef hs.exs.keep(-A: Data, k: Bool, x: A, ys: List<&2, A>) -> List<&2, A>:\n  match k:\n    case True{}:\n      x <> ys\n    case False{}:\n      ys\n\ndef hs.exs.filterm(~E: Data, ~S: Data, ~A: Data, ~p: A -> S -> Sigma<&1, &1, Either<&2, &2, E, Bool>, _ => S>, xs: List<&2, A>) -> S -> Sigma<&1, &1, Either<&2, &2, E, List<&2, A>>, _ => S>:\n  match xs:\n    case Nil{}:\n      hs.exs.pure(E, S, List<&2, A>, Nil{})\n    case +h <> t:\n      hs.exs.bind(E, S, Bool, List<&2, A>, p(h), k => hs.exs.map(E, S, List<&2, A>, List<&2, A>, ys => hs.exs.keep(A, k, h, ys), hs.exs.filterm(~E, ~S, ~A, ~p, t)))\n\ndef hs.exs.zipwithm_(~E: Data, ~S: Data, ~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> S -> Sigma<&1, &1, Either<&2, &2, E, C>, _ => S>, xs: List<&2, A>, ys: List<&2, B>) -> S -> Sigma<&1, &1, Either<&2, &2, E, Unit>, _ => S>:\n  match xs ys:\n    case x <> xt y <> yt:\n      hs.exs.bind(E, S, C, Unit, f(x)(y), _ => hs.exs.zipwithm_(~E, ~S, ~A, ~B, ~C, ~f, xt, yt))\n    case _ _:\n      hs.exs.pure(E, S, Unit, Unit{})\n\n"

def fd.pre.eq.list() -> String:
  "# Haskell's == at lists, given == at the elements\ndef hs.eq.list(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:\n  match xs ys:\n    case Nil{} Nil{}:\n      True{}\n    case x <> xt y <> yt:\n      Bool.and(eq(x, y), hs.eq.list(~A, ~eq, xt, yt))\n    case _ _:\n      False{}\n\n"

def fd.pre.eq.maybe() -> String:
  "# Haskell's == at Maybe\ndef hs.eq.maybe(~A: Data, ~eq: A -> A -> Bool, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:\n  match a b:\n    case None{} None{}:\n      True{}\n    case Some{x} Some{y}:\n      eq(x, y)\n    case _ _:\n      False{}\n\n"

def fd.pre.eq.either() -> String:
  "# Haskell's == at Either\ndef hs.eq.either(~A: Data, ~B: Data, ~ea: A -> A -> Bool, ~eb: B -> B -> Bool, a: Either<&2, &2, A, B>, b: Either<&2, &2, A, B>) -> Bool:\n  match a b:\n    case Inl{x} Inl{y}:\n      ea(x, y)\n    case Inr{x} Inr{y}:\n      eb(x, y)\n    case _ _:\n      False{}\n\n"

def fd.pre.eq.pair() -> String:
  "# Haskell's == at pairs\ndef hs.eq.pair(~A: Data, ~B: Data, ~ea: A -> A -> Bool, ~eb: B -> B -> Bool, p: Sigma<&2, &2, A, _ => B>, q: Sigma<&2, &2, A, _ => B>) -> Bool:\n  (a, b) = p\n  (c, d) = q\n  Bool.and(ea(a, c), eb(b, d))\n\n"

def fd.pre.eq.unit() -> String:
  "# Haskell's == at ()\ndef hs.eq.unit(a: Unit, b: Unit) -> Bool:\n  match a b:\n    case Unit{} Unit{}:\n      True{}\n\n"

def fd.pre.eq.cmp() -> String:
  "# Haskell's == at Ordering\ndef hs.eq.cmp(a: Cmp, b: Cmp) -> Bool:\n  match a b:\n    case LT{} LT{}:\n      True{}\n    case EQ{} EQ{}:\n      True{}\n    case GT{} GT{}:\n      True{}\n    case _ _:\n      False{}\n\n"

# whether the items name any of ns
def fd.uses.any(+its: List<&2, T.BItem>, ns: List<String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> t:
      Bool.or(fd.uses.name(its, S.b(n)), fd.uses.any(its, t))

# ReaderT over Identity (see Types): hs.rd.*, mtl's MonadReader methods
def fd.pre.rd() -> String:
  "# Reader r a (ReaderT r Identity a, Control.Monad.Trans.Reader): R -> A, a\n# function of the environment (ReaderT's newtype: r -> m a); mtl's\n# MonadReader methods at it\ndef hs.rd.bind.go(-R: Data, -A: Type, -B: Type, m: R -> A, f: A -> R -> B, +r: R) -> B:\n  f(m(r))(r)\n\ndef hs.rd.bind(-R: Data, -A: Type, -B: Type, m: R -> A, f: A -> R -> B) -> R -> B:\n  r => hs.rd.bind.go(R, A, B, m, f, r)\n\ndef hs.rd.pure(-R: Data, -A: Type, a: A) -> R -> A:\n  _ => a\n\ndef hs.rd.map(-R: Data, -A: Type, -B: Type, f: A -> B, m: R -> A) -> R -> B:\n  r => f(m(r))\n\ndef hs.rd.ask(-R: Data) -> R -> R:\n  r => r\n\ndef hs.rd.local(-R: Data, -A: Type, f: R -> R, m: R -> A) -> R -> A:\n  r => m(f(r))\n\ndef hs.rd.asks(-R: Data, -A: Type, f: R -> A) -> R -> A:\n  r => f(r)\n\n"

# ReaderT over Either (see Types): hs.rde.*, mtl's MonadReader and
# MonadError methods, lift
def fd.pre.rde() -> String:
  "# ReaderT r (Either e) a (Control.Monad.Trans.Reader over Either):\n# R -> Either E A, a Reader whose result is an Either (>>= stops at a\n# Left); mtl's MonadReader and MonadError methods at it, and lift\ndef hs.rde.bind.go(-R: Data, -E: Data, -A: Data, -B: Data, x: Either<&2, &2, E, A>, f: A -> R -> Either<&2, &2, E, B>, r: R) -> Either<&2, &2, E, B>:\n  match x:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      f(a)(r)\n\ndef hs.rde.bind.r(-R: Data, -E: Data, -A: Data, -B: Data, m: R -> Either<&2, &2, E, A>, f: A -> R -> Either<&2, &2, E, B>, +r: R) -> Either<&2, &2, E, B>:\n  hs.rde.bind.go(R, E, A, B, m(r), f, r)\n\ndef hs.rde.bind(-R: Data, -E: Data, -A: Data, -B: Data, m: R -> Either<&2, &2, E, A>, f: A -> R -> Either<&2, &2, E, B>) -> R -> Either<&2, &2, E, B>:\n  r => hs.rde.bind.r(R, E, A, B, m, f, r)\n\ndef hs.rde.pure(-R: Data, -E: Data, -A: Data, a: A) -> R -> Either<&2, &2, E, A>:\n  _ => Inr{a}\n\ndef hs.rde.throw(-R: Data, -E: Data, -A: Data, e: E) -> R -> Either<&2, &2, E, A>:\n  _ => Inl{e}\n\ndef hs.rde.lift(-R: Data, -E: Data, -A: Data, x: Either<&2, &2, E, A>) -> R -> Either<&2, &2, E, A>:\n  _ => x\n\ndef hs.rde.map.e(-E: Data, -A: Data, -B: Data, f: A -> B, x: Either<&2, &2, E, A>) -> Either<&2, &2, E, B>:\n  match x:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      Inr{f(a)}\n\ndef hs.rde.map(-R: Data, -E: Data, -A: Data, -B: Data, f: A -> B, m: R -> Either<&2, &2, E, A>) -> R -> Either<&2, &2, E, B>:\n  r => hs.rde.map.e(E, A, B, f, m(r))\n\ndef hs.rde.ask(-R: Data, -E: Data) -> R -> Either<&2, &2, E, R>:\n  r => Inr{r}\n\ndef hs.rde.local(-R: Data, -E: Data, -A: Data, f: R -> R, m: R -> Either<&2, &2, E, A>) -> R -> Either<&2, &2, E, A>:\n  r => m(f(r))\n\ndef hs.rde.asks(-R: Data, -E: Data, -A: Data, f: R -> A) -> R -> Either<&2, &2, E, A>:\n  r => Inr{f(r)}\n\n"

# WriterT over Identity (see Types): hs.wr.*
def fd.pre.wr() -> String:
  "# Writer w a (WriterT w Identity a, Control.Monad.Trans.Writer): A & W, a\n# result and its log (WriterT's newtype: m (a, w)). Each def takes w's\n# mempty and <> after W (the fold writes them at w's type): pure logs\n# mempty, >>= joins the two logs with <>\ndef hs.wr.join(-W: Data, -B: Data, app: W -> W -> W, w: W, y: Sigma<&2, &2, B, _ => W>) -> Sigma<&2, &2, B, _ => W>:\n  match y:\n    case Tuple{b, v}:\n      Tuple{b, app(w)(v)}\n\ndef hs.wr.bind(-W: Data, mt: W, app: W -> W -> W, -A: Data, -B: Data, x: Sigma<&2, &2, A, _ => W>, f: A -> Sigma<&2, &2, B, _ => W>) -> Sigma<&2, &2, B, _ => W>:\n  match x:\n    case Tuple{a, w}:\n      hs.wr.join(W, B, app, w, f(a))\n\ndef hs.wr.pure(-W: Data, mt: W, app: W -> W -> W, -A: Data, a: A) -> Sigma<&2, &2, A, _ => W>:\n  Tuple{a, mt}\n\ndef hs.wr.map(-W: Data, mt: W, app: W -> W -> W, -A: Data, -B: Data, f: A -> B, x: Sigma<&2, &2, A, _ => W>) -> Sigma<&2, &2, B, _ => W>:\n  match x:\n    case Tuple{a, w}:\n      Tuple{f(a), w}\n\n"

# WriterT over Either (see Types): hs.wre.*
def fd.pre.wre() -> String:
  "# WriterT w (Either e) a (Control.Monad.Trans.Writer over Either):\n# Either E (A & W), a Writer whose run is an Either (>>= stops at a\n# Left). Each def takes w's mempty and <> after W and E (the fold writes\n# them at w's type): pure logs mempty, >>= joins the two logs with <>\ndef hs.wre.join(-W: Data, -E: Data, -B: Data, app: W -> W -> W, w: W, y: Either<&2, &2, E, Sigma<&2, &2, B, _ => W>>) -> Either<&2, &2, E, Sigma<&2, &2, B, _ => W>>:\n  match y:\n    case Inl{e}:\n      Inl{e}\n    case Inr{Tuple{b, v}}:\n      Inr{Tuple{b, app(w)(v)}}\n\ndef hs.wre.bind(-W: Data, -E: Data, mt: W, app: W -> W -> W, -A: Data, -B: Data, x: Either<&2, &2, E, Sigma<&2, &2, A, _ => W>>, f: A -> Either<&2, &2, E, Sigma<&2, &2, B, _ => W>>) -> Either<&2, &2, E, Sigma<&2, &2, B, _ => W>>:\n  match x:\n    case Inl{e}:\n      Inl{e}\n    case Inr{Tuple{a, w}}:\n      hs.wre.join(W, E, B, app, w, f(a))\n\ndef hs.wre.pure(-W: Data, -E: Data, mt: W, app: W -> W -> W, -A: Data, a: A) -> Either<&2, &2, E, Sigma<&2, &2, A, _ => W>>:\n  Inr{Tuple{a, mt}}\n\ndef hs.wre.map(-W: Data, -E: Data, mt: W, app: W -> W -> W, -A: Data, -B: Data, f: A -> B, x: Either<&2, &2, E, Sigma<&2, &2, A, _ => W>>) -> Either<&2, &2, E, Sigma<&2, &2, B, _ => W>>:\n  match x:\n    case Inl{e}:\n      Inl{e}\n    case Inr{Tuple{a, w}}:\n      Inr{Tuple{f(a), w}}\n\n"

def fd.pre.one(+its: List<&2, T.BItem>, n: String, text: String) -> List<&2, U32>:
  fd.bpick(fd.uses.name(its, S.b(n)), S.b(text), Nil{})

def fd.prelude(+its: List<&2, T.BItem>) -> List<&2, U32>:
  List.concat(&2, U32, [fd.pre.one(its, "Bool.if", fd.pre.if()), fd.pre.one(its, "hs.map", fd.pre.map()), fd.pre.one(its, "hs.either.bind", fd.pre.either.bind()), fd.pre.one(its, "hs.either.map", fd.pre.either.map()), fd.pre.one(its, "hs.maybe", fd.pre.maybe()), fd.pre.one(its, "hs.maybe.alt", fd.pre.maybe.alt()), fd.pre.one(its, "hs.either", fd.pre.either()), fd.pre.one(its, "hs.eq.list", fd.pre.eq.list()), fd.pre.one(its, "hs.eq.maybe", fd.pre.eq.maybe()), fd.pre.one(its, "hs.eq.either", fd.pre.eq.either()), fd.pre.one(its, "hs.eq.pair", fd.pre.eq.pair()), fd.pre.one(its, "hs.eq.unit", fd.pre.eq.unit()), fd.pre.one(its, "hs.eq.cmp", fd.pre.eq.cmp()), fd.bpick(fd.uses.any(its, ["hs.state.bind", "hs.state.pure", "hs.state.map", "hs.state.ap", "hs.state.get", "hs.state.put", "hs.state.modify", "hs.state.gets", "hs.state.eval", "hs.state.exec", "hs.state.run", "hs.state.mapm_", "hs.state.mapm", "hs.state.foldm", "hs.state.filterm", "hs.state.zipwithm_"]), S.b(fd.pre.state()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.state.filterm", "hs.state.zipwithm_"]), S.b(fd.pre.statem()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.exs.bind", "hs.exs.pure", "hs.exs.throw", "hs.exs.map", "hs.exs.get", "hs.exs.put", "hs.exs.modify", "hs.exs.gets", "hs.exs.mapm_", "hs.exs.mapm", "hs.exs.foldm", "hs.exs.filterm", "hs.exs.zipwithm_"]), S.b(fd.pre.exs()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.exs.filterm", "hs.exs.zipwithm_"]), S.b(fd.pre.exsm()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.rd.bind", "hs.rd.pure", "hs.rd.map", "hs.rd.ask", "hs.rd.local", "hs.rd.asks"]), S.b(fd.pre.rd()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.rde.bind", "hs.rde.pure", "hs.rde.throw", "hs.rde.lift", "hs.rde.map", "hs.rde.ask", "hs.rde.local", "hs.rde.asks"]), S.b(fd.pre.rde()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.wr.bind", "hs.wr.pure", "hs.wr.map"]), S.b(fd.pre.wr()), Nil{}), fd.bpick(fd.uses.any(its, ["hs.wre.bind", "hs.wre.pure", "hs.wre.map"]), S.b(fd.pre.wre()), Nil{})])

# The file -------------------------------------------------------------------------

def fd.header(+file: List<&2, U32>, +m: List<&2, U32>) -> List<&2, List<&2, U32>>:
  [fd.cat(S.b("Haskell module "), m), fd.cat(S.b("from "), file), S.b("Written by cata (fixed rules, no model); every def checks with bend --check-only.")]

# the file's text: header, import Base, the prelude, the items in order
def fd.import.if(use: Bool, +a: List<&2, U32>, acc: List<&2, T.BImport>) -> List<&2, T.BImport>:
  match use:
    case True{}:
      T.BImport{fd.cat3(S.b("./"), a, S.b(".bend")), a} <> acc
    case False{}:
      acc

# the package's files (by alias) that the text names, ALIAS.x, as imports
def fd.imports(ims: List<&2, List<&2, U32>>, +text: List<&2, U32>) -> List<&2, T.BImport>:
  match ims:
    case +a <> t:
      fd.import.if(S.infix(text, fd.cat(a, S.b("."))), a, fd.imports(t, text))
    case Nil{}:
      Nil{}

def fd.text.ims(ims: List<&2, List<&2, U32>>, +ord: List<&2, T.BItem>) -> List<&2, T.BImport>:
  match ims:
    case Nil{}:
      Nil{}
    case +a <> t:
      fd.imports(a <> t, P.tpr.file(T.BFile{Nil{}, Nil{}, ord}))

# the file: its header, the earlier modules of its package it names (ims:
# their aliases), its items in order
def fd.text(+file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>) -> List<&2, U32>:
  +ord = O.tor.order(its)
  P.tpr.file(T.BFile{fd.header(file, m), fd.text.ims(ims, ord), ord})

def fd.splice.at(hit: Bool, h: List<&2, U32>, t: List<&2, List<&2, U32>>, pre: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      h <> Nil{} <> List.append(&2, List<&2, U32>, S.split(pre, 10), t)
    case False{}:
      h <> t

def fd.next.import(ls: List<&2, List<&2, U32>>) -> Bool:
  match ls:
    case h <> t:
      S.prefix(h, S.b("import "))
    case Nil{}:
      False{}

# the prelude goes after the last import
def fd.splice.go(ls: List<&2, List<&2, U32>>, +pre: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ls:
    case +h <> +t:
      fd.splice.at(Bool.and(S.prefix(h, S.b("import ")), Bool.not(fd.next.import(t))), h, fd.splice.go(t, pre), pre)
    case Nil{}:
      Nil{}

# the prelude goes right after `import Base`
def fd.splice(text: List<&2, U32>, pre: List<&2, U32>) -> List<&2, U32>:
  S.join(fd.splice.go(S.split(text, 10), pre), 10)

def fd.render(+file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>) -> List<&2, U32>:
  fd.splice(fd.text(file, m, ims, its), fd.prelude(its))

# Parsers, eta-expanded --------------------------------------------------------

# A def whose answer is a parser (HsPcSt -> HsPcRep<A>, see Types) takes the
# state as a last parameter, pc_s0, and answers the reply: its body applied
# to it at each end (a case's, after a let), a call of another such def
# there given it as its last argument. Each other call of one, with all its
# arguments but the state, is the lambda pc_s => X(.., pc_s). So a parser's
# def answers Data and its uses are calls, and the parsers that call each
# other (a grammar's) are a group like any other (the fold's .mu): no
# closure is made until a parser is run, and none is run twice.
type Etn is Data:
  Etn{n: List<&2, U32>, k: Nat}

def fd.eta.isst(a: T.Bt) -> Bool:
  match a:
    case T.BtTyApp{+n, T.BtANil{}}:
      fd.is(n, "HsPrelude.HsPcSt")
    case T.BtVar{+n}:
      fd.is(n, "HsPrelude.HsPcSt")
    case _:
      False{}

def fd.eta.isp(r: T.Bt) -> Bool:
  match r:
    case T.BtPi{m, x, d, a, b}:
      fd.eta.isst(a)
    case _:
      False{}

def fd.eta.cod(r: T.Bt) -> T.Bt:
  match r:
    case T.BtPi{m, x, d, a, b}:
      b
    case u:
      u

def fd.eta.names(its: List<&2, T.BItem>) -> List<&2, Etn>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{+n, +ps, +r, b, d} <> t:
      +rest = fd.eta.names(t)
      Bool.pick(List<&2, Etn>, fd.eta.isp(r), Etn{n, List.length(&2, T.BParam, ps)} <> rest, rest)
    case h <> t:
      fd.eta.names(t)

# x's arity, if it is one of es
def fd.eta.find(es: List<&2, Etn>, +x: List<&2, U32>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case Etn{+n, k} <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(n, x), Some{k}, fd.eta.find(t, x))

def fd.eta.full(m: Maybe<&2, Nat>, +a: T.Bt) -> Bool:
  match m:
    case Some{k}:
      Nat.is_eq(T.tba.args.len(a), k)
    case None{}:
      False{}

def fd.eta.st(+s: String) -> T.Bt:
  T.BtVar{S.b(s)}

# a call of x with its arguments a (rewritten): the lambda when it lacks the
# state
def fd.eta.call(full: Bool, +x: List<&2, U32>, a: T.Bt) -> T.Bt:
  match full:
    case True{}:
      T.BtLam{T.BmLive{}, S.b("pc_s"), T.BtApp{T.BtVar{x}, T.tba.args(List.append(&2, T.Bt, fd.spine(a), [fd.eta.st("pc_s")]))}}
    case False{}:
      T.BtApp{T.BtVar{x}, a}

def fd.eta.rw(t: T.Bt, +es: List<&2, Etn>) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+x}, +a}:
      fd.eta.call(fd.eta.full(fd.eta.find(es, x), a), x, fd.eta.rw(a, es))
    case T.BtApp{h, a}:
      T.BtApp{fd.eta.rw(h, es), fd.eta.rw(a, es)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.eta.rw(a, es)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.eta.rw(b, es)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.eta.rw(a, es)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, fd.eta.rw(a, es), fd.eta.rw(b, es)}
    case T.BtSucc{a}:
      T.BtSucc{fd.eta.rw(a, es)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.eta.rw(a, es), ty}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.eta.rw(cs, es)}
    case T.BtExpr{e}:
      T.BtExpr{fd.eta.rw(e, es)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.eta.rw(e, es), p, fd.eta.rw(b, es)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, fd.eta.rw(v, es), fd.eta.rw(b, es)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.eta.rw(b, es), fd.eta.rw(rest, es)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.eta.rw(a, es), fd.eta.rw(rest, es)}
    case u:
      u

# e applied to the state pc_s0: a call of such a def given it last
def fd.eta.app.if(full: Bool, +x: List<&2, U32>, a: T.Bt) -> T.Bt:
  match full:
    case True{}:
      T.BtApp{T.BtVar{x}, T.tba.args(List.append(&2, T.Bt, fd.spine(a), [fd.eta.st("pc_s0")]))}
    case False{}:
      T.tba.call(T.BtApp{T.BtVar{x}, a}, [fd.eta.st("pc_s0")])

def fd.eta.app(e: T.Bt, +es: List<&2, Etn>) -> T.Bt:
  match e:
    case T.BtApp{T.BtVar{+x}, +a}:
      fd.eta.app.if(fd.eta.full(fd.eta.find(es, x), a), x, a)
    case u:
      T.tba.call(u, [fd.eta.st("pc_s0")])

# a body applied to the state at each of its ends
def fd.eta.tail(b: T.Bt, +es: List<&2, Etn>) -> T.Bt:
  match b:
    case T.BtExpr{e}:
      T.BtExpr{fd.eta.app(e, es)}
    case T.BtLet{x, v, r}:
      T.BtLet{x, v, fd.eta.tail(r, es)}
    case T.BtRw{e, p, r}:
      T.BtRw{e, p, fd.eta.tail(r, es)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.eta.tail(cs, es)}
    case T.BtCase{p, r, rest}:
      T.BtCase{p, fd.eta.tail(r, es), fd.eta.tail(rest, es)}
    case T.BtCEnd{}:
      T.BtCEnd{}
    case u:
      fd.eta.app(u, es)

def fd.eta.def(isp: Bool, +n: List<&2, U32>, ps: List<&2, T.BParam>, +r: T.Bt, b: T.Bt, d: List<&2, List<&2, U32>>, +es: List<&2, Etn>) -> T.BItem:
  match isp:
    case True{}:
      T.BiDef{n, List.append(&2, T.BParam, ps, [T.BParam{T.BmLive{}, S.b("pc_s0"), fd.ty0("HsPrelude.HsPcSt")}]), fd.eta.cod(r), fd.eta.rw(fd.eta.tail(b, es), es), d}
    case False{}:
      T.BiDef{n, ps, r, fd.eta.rw(b, es), d}

def fd.eta.items(its: List<&2, T.BItem>, +es: List<&2, Etn>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{+n, ps, +r, b, d} <> t:
      fd.eta.def(fd.eta.isp(r), n, ps, r, b, d, es) <> fd.eta.items(t, es)
    case h <> t:
      h <> fd.eta.items(t, es)

def fd.eta.all(+its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  fd.eta.items(its, fd.eta.names(its))

# The gate ---------------------------------------------------------------------------

# Bend allows no mutual recursion, so a walk that branches on what it reads
# takes the branch as a parameter, computed by its caller from the next
# element (as Survey's sv.modname.go does).

# a character's class, for reading Bend's error: a digit, a space, >, other
type Kc is Data:
  KcDigit{}
  KcSpace{}
  KcGt{}
  KcOther{}
  KcEnd{}

def fd.kc(xs: List<&2, U32>) -> Kc:
  match xs:
    case +c <> t:
      Bool.pick(Kc, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), KcDigit{}, Bool.pick(Kc, U32.is_eq(c, 32), KcSpace{}, Bool.pick(Kc, U32.is_eq(c, 62), KcGt{}, KcOther{})))
    case Nil{}:
      KcEnd{}

def fd.isbar(xs: List<&2, U32>) -> Bool:
  match xs:
    case c <> t:
      U32.is_eq(c, 124)
    case Nil{}:
      False{}

# the N of a line ` N>| ..`, the line Bend marks in its error
def fd.marked(xs: List<&2, U32>, k: Kc, seen: Bool, +acc: Nat) -> Maybe<&2, Nat>:
  match xs k seen:
    case +c <> +t KcDigit{} _:
      fd.marked(t, fd.kc(t), True{}, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))))
    case c <> +t KcSpace{} False{}:
      fd.marked(t, fd.kc(t), False{}, acc)
    case c <> +t KcGt{} True{}:
      Bool.pick(Maybe<&2, Nat>, fd.isbar(t), Some{acc}, None{})
    case _ _ _:
      None{}

def fd.errline(ls: List<&2, List<&2, U32>>) -> Maybe<&2, Nat>:
  match ls:
    case +l <> t:
      Maybe.or(&2, Nat, fd.marked(l, fd.kc(l), False{}, 0n), fd.errline(t))
    case Nil{}:
      None{}

# a name: up to (, <, space or :
def fd.stop(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      Bool.or(Bool.or(U32.is_eq(c, 40), U32.is_eq(c, 60)), Bool.or(U32.is_eq(c, 32), U32.is_eq(c, 58)))
    case Nil{}:
      True{}

def fd.word(xs: List<&2, U32>, stop: Bool) -> List<&2, U32>:
  match xs stop:
    case c <> +t False{}:
      c <> fd.word(t, fd.stop(t))
    case _ _:
      Nil{}

def fd.itemname.of(d: Bool, t: Bool, +l: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match d t:
    case True{} _:
      +r = List.drop(&2, U32, l, 4n)
      Some{fd.word(r, fd.stop(r))}
    case False{} True{}:
      +r = List.drop(&2, U32, l, 5n)
      Some{fd.word(r, fd.stop(r))}
    case False{} False{}:
      None{}

# the item a line starts, if it starts one: `def NAME(` or `type NAME`
def fd.itemname(+l: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  fd.itemname.of(S.prefix(l, S.b("def ")), S.prefix(l, S.b("type ")), l)

# the item whose text holds line n (1-based): the last one started at or
# above it
def fd.owner(n: Nat, ls: List<&2, List<&2, U32>>, cur: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match n ls:
    case 0n _:
      cur
    case 1n+p +l <> t:
      fd.owner(p, t, Maybe.or(&2, List<&2, U32>, fd.itemname(l), cur))
    case _ Nil{}:
      cur

def fd.tabless(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      Bool.pick(U32, U32.is_eq(c, 9), 32, c) <> fd.tabless(t)
    case Nil{}:
      Nil{}

def fd.iserr(ls: List<&2, List<&2, U32>>) -> Bool:
  match ls:
    case +h <> t:
      fd.is(h, "Error:")
    case Nil{}:
      False{}

# at most k characters of a line
def fd.clip(s: List<&2, U32>, k: Nat) -> List<&2, U32>:
  match s k:
    case c <> t 1n+k:
      c <> fd.clip(t, k)
    case _ _:
      Nil{}

# the first line, for output without an "Error:" line
def fd.line1(ls: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ls:
    case h <> t:
      h
    case Nil{}:
      S.b("unknown")

# the two lines after "Error:", Bend's reason and what it saw
def fd.errwhy.go(ls: List<&2, List<&2, U32>>, hit: Bool, raw: List<&2, U32>) -> List<&2, U32>:
  match ls hit:
    case h <> n <> o <> t True{}:
      fd.cat(fd.tabless(n), fd.cat(S.b(" | "), fd.clip(fd.tabless(o), 100n)))
    case h <> +t False{}:
      fd.errwhy.go(t, fd.iserr(t), raw)
    case _ _:
      fd.cat(S.b("raw: "), raw)

def fd.errwhy(+ls: List<&2, List<&2, U32>>) -> List<&2, U32>:
  fd.errwhy.go(ls, fd.iserr(ls), fd.clip(fd.tabless(fd.line1(ls)), 100n))

def fd.item.names(+it: T.BItem) -> List<&2, List<&2, U32>>:
  T.tba.item.names(it, Nil{})

def fd.item.name(it: T.BItem) -> List<&2, U32>:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      n
    case T.BiType{n, ps, k, cs, d}:
      n
    case T.BiComment{d}:
      Nil{}

# whether an item mentions one of the names gone
# the def a lifted def was taken out of (its doc says so), or none
def fd.liftof.doc(d: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match d:
    case +h <> t:
      fd.bpick(S.prefix(h, S.b("generated: lifted out of ")), List.drop(&2, U32, h, 25n), Nil{})
    case Nil{}:
      Nil{}

def fd.liftof(it: T.BItem) -> List<&2, U32>:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      fd.liftof.doc(d)
    case _:
      Nil{}

def fd.hits(+it: T.BItem, gone: List<&2, List<&2, U32>>) -> Bool:
  match gone:
    case +g <> t:
      Bool.or(T.tba.item.uses(it, g), fd.hits(it, t))
    case Nil{}:
      False{}

# the first gone name the item uses (none: empty)
def fd.hit.name(+it: T.BItem, gone: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match gone:
    case +g <> t:
      fd.bpick(T.tba.item.uses(it, g), g, fd.hit.name(it, t))
    case Nil{}:
      Nil{}

# A drop: the item's name and why.
type Dr is Data:
  Dr{n: List<&2, U32>, why: List<&2, U32>}

type Split is Data:
  Split{keep: List<&2, T.BItem>, out: List<&2, Dr>}

def fd.split.if(hit: Bool, +it: T.BItem, +why: List<&2, U32>, +gone: List<&2, List<&2, U32>>, s: Split) -> Split:
  match hit s:
    case True{} Split{k, o}:
      +n = fd.hit.name(it, gone)
      Split{k, Dr{fd.item.name(it), fd.bpick(Bool.or(List.is_empty(&2, U32, n), Bool.not(fd.is(why, "dep"))), why, fd.cat(why, 58 <> n))} <> o}
    case False{} Split{k, o}:
      Split{it <> k, o}

# the items that mention a name gone go too, and the defs lifted out of one
# (see Lifting); a bare dep names the first gone name an item uses
def fd.split(its: List<&2, T.BItem>, +gone: List<&2, List<&2, U32>>, +why: List<&2, U32>) -> Split:
  match its:
    case +h <> t:
      fd.split.if(Bool.or(fd.hits(h, gone), S.mem(fd.liftof(h), gone)), h, why, gone, fd.split(t, gone, why))
    case Nil{}:
      Split{Nil{}, Nil{}}

def fd.dr.names(ds: List<&2, Dr>) -> List<&2, List<&2, U32>>:
  match ds:
    case Dr{n, w} <> t:
      n <> fd.dr.names(t)
    case Nil{}:
      Nil{}

# drop what depends on what went, again until nothing more goes (fuel:
# the items there are); s is the last round's split
def fd.closure(fuel: Nat, s: Split, +why: List<&2, U32>, acc: List<&2, Dr>) -> Split:
  match fuel s:
    case _ Split{k, Nil{}}:
      Split{k, acc}
    case 0n Split{k, o}:
      Split{k, List.append(&2, Dr, o, acc)}
    case 1n+p Split{k, +o}:
      fd.closure(p, fd.split(k, fd.dr.names(o), why), why, List.append(&2, Dr, o, acc))

def fd.without.put(drop: Bool, h: T.BItem, rest: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

def fd.without(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, T.BItem>:
  match its:
    case +h <> t:
      fd.without.put(S.eq(fd.item.name(h), n), h, fd.without(t, n))
    case Nil{}:
      Nil{}

def fd.ctor.names(cs: List<&2, T.BCtor>) -> List<&2, List<&2, U32>>:
  match cs:
    case T.BCtor{c, fs} <> t:
      c <> fd.ctor.names(t)
    case Nil{}:
      Nil{}

# what an item defines, for what uses it: a def's name, a type's and its
# constructors' (not their binders: T.tba.item.names gives a def's
# parameters and a type's fields, so a def named like one of those was
# taken for a user)
def fd.item.defs(it: T.BItem) -> List<&2, List<&2, U32>>:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      n <> Nil{}
    case T.BiType{n, ps, k, cs, d}:
      n <> fd.ctor.names(cs)
    case T.BiComment{d}:
      Nil{}

# the names of the item named n: its own, and its constructors if a type
def fd.namesof(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match its:
    case +h <> t:
      fd.bpicks(S.eq(fd.item.name(h), n), fd.item.defs(h), fd.namesof(t, n))
    case Nil{}:
      n <> Nil{}

def fd.gate.all(its: List<&2, T.BItem>, +why: List<&2, U32>) -> List<&2, Dr>:
  match its:
    case h <> t:
      Dr{fd.item.name(h), why} <> fd.gate.all(t, why)
    case Nil{}:
      Nil{}

# Where the gate is: the items still in, the drops so far, whether done.
type Gs is Data:
  Gs{its: List<&2, T.BItem>, out: List<&2, Dr>, done: Bool}

def Split.keep(s: Split) -> List<&2, T.BItem>:
  match s:
    case Split{k, o}:
      k

def Split.out(s: Split) -> List<&2, Dr>:
  match s:
    case Split{k, o}:
      o

# an out item's name: a lifted def's is a Bend name already (a Haskell
# name with a dot in it is an operator's)
def fd.has.dot(xs: List<&2, U32>) -> Bool:
  match xs:
    case c <> t:
      Bool.or(U32.is_eq(c, 46), fd.has.dot(t))
    case Nil{}:
      False{}

def fd.oname(+n: List<&2, U32>) -> List<&2, U32>:
  fd.bpick(Bool.and(fd.name.lead(n), fd.has.dot(n)), n, fd.vname(n))

# the item an error is in gone, with every item that uses it
def fd.gate.drop(who: Maybe<&2, List<&2, U32>>, +its: List<&2, T.BItem>, out: List<&2, Dr>, +why: List<&2, U32>) -> Gs:
  match who:
    case None{}:
      Gs{Nil{}, List.append(&2, Dr, fd.gate.all(its, why), out), True{}}
    case Some{+n}:
      +dep = fd.bpick(Bool.and(fd.name.lead(n), fd.has.dot(n)), why, fd.cat(S.b("dep:"), n))
      +s = fd.closure(List.length(&2, T.BItem, its), fd.split(fd.without(its, n), fd.namesof(its, n), dep), dep, Dr{n, why} <> out)
      Gs{Split.keep(s), Split.out(s), List.is_empty(&2, T.BItem, Split.keep(s))}

def fd.gate.who(l: Maybe<&2, Nat>, text: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match l:
    case Some{n}:
      fd.owner(n, S.split(text, 10), None{})
    case None{}:
      None{}

# a check error inside a template's instance (Location: NAME~K): its lines
# are Base's or HsPrelude's, not the file's; the line of the file's K-th
# call of NAME (1-based) is the item's
def fd.tpl.loc(ls: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ls:
    case +l <> t:
      Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(S.prefix(l, S.b("Location: ")), S.infix(l, [126])), Some{List.drop(&2, U32, l, 10n)}, fd.tpl.loc(t))
    case Nil{}:
      None{}

# NAME of NAME~K
def fd.tpl.name(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      Bool.pick(List<&2, U32>, U32.is_eq(c, 126), Nil{}, c <> fd.tpl.name(t))
    case Nil{}:
      Nil{}

# K of NAME~K
def fd.tpl.k(xs: List<&2, U32>, +acc: Nat, seen: Bool) -> Nat:
  match xs seen:
    case +c <> t False{}:
      fd.tpl.k(t, acc, U32.is_eq(c, 126))
    case +c <> t True{}:
      Bool.pick(Nat, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), fd.tpl.k(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))), True{}), acc)
    case Nil{} _:
      acc

# the line (1-based, from i) of the k-th line of ls that holds call
def fd.tpl.line(ls: List<&2, List<&2, U32>>, +call: List<&2, U32>, +i: Nat, +k: Nat) -> Maybe<&2, Nat>:
  match ls:
    case +l <> t:
      +hit = S.infix(l, call)
      Bool.pick(Maybe<&2, Nat>, Bool.and(hit, Nat.is_eq(k, 0n)), Some{i}, fd.tpl.line(t, call, Nat.add(i, 1n), Bool.pick(Nat, hit, Nat.sub(k, 1n), k)))
    case Nil{}:
      None{}

# whether an item of its is named n
def fd.gate.has(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case h <> t:
      Bool.or(S.eq(fd.item.name(h), n), fd.gate.has(t, n))
    case Nil{}:
      False{}

# the template's caller when it is an item, else the item of the error's line
def fd.gate.pick(c: Maybe<&2, List<&2, U32>>, +its: List<&2, T.BItem>, d: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match c:
    case Some{+n}:
      Bool.pick(Maybe<&2, List<&2, U32>>, fd.gate.has(its, n), Some{n}, d)
    case None{}:
      d

def fd.gate.who2(tl: Maybe<&2, List<&2, U32>>, ls: List<&2, List<&2, U32>>, +text: List<&2, U32>, +its: List<&2, T.BItem>) -> Maybe<&2, List<&2, U32>>:
  match tl:
    case Some{+s}:
      fd.gate.pick(fd.gate.who(fd.tpl.line(S.split(text, 10), fd.cat(fd.tpl.name(s), [40]), 1n, fd.tpl.k(s, 0n, False{})), text), its, fd.gate.who(fd.errline(ls), text))
    case None{}:
      fd.gate.who(fd.errline(ls), text)

# Fuel -----------------------------------------------------------------------------
#
# Recursion Bend refuses, written as telomare's bend branch writes it (no
# @unsafe): a def whose self-call Bend does not see shrink ("a decreasing
# self-call") is f.fu, with a Nat after its type and template parameters,
# one less at each self-call, U32.to_nat(4294967295) from f (a depth no run
# reaches), and at 0 a default of the result's type (Desugar.bend's go and
# fuel()).

# U32.to_nat(4294967295): the depth a fuelled def starts with
def fd.fu.max() -> T.Bt:
  fd.callS("U32.to_nat", [T.BtVar{S.b("4294967295")}])

# Defaults: a value of a type, for the fuel's end.  Base's types and
# HsPrelude's have theirs; a pair, an Either, Fix and Cofree are
# constructors of their parts; the module's own types, a constructor with
# no fields first, then one whose fields do not name the type, then any
# (its fields' defaults in turn).  A type variable, or a type of another
# module, has none: the def is out (fold:fuel-default-at-type).  One def
# answers every question (Bend allows no mutual recursion): a question is a
# Dq, an answer a Da, a step that needs no recursion a Dn.
type Dq is Data:
  DqTy{ty: T.Bt}
  DqRun{n: Dn}
  DqCs{cs: List<&2, T.BCtor>, next: List<&2, List<&2, T.BCtor>>, ps: List<&2, T.BParam>, args: T.Bt}
  DqPick{r: Da, c: List<&2, U32>, cs: List<&2, T.BCtor>, next: List<&2, List<&2, T.BCtor>>, ps: List<&2, T.BParam>, args: T.Bt}
  DqFs{fs: List<&2, T.BField>, ps: List<&2, T.BParam>, args: T.Bt}
  DqCons{r: Da, fs: List<&2, T.BField>, ps: List<&2, T.BParam>, args: T.Bt}

type Dn is Data:
  DnDone{a: Da}
  DnAsk{q: Dq}
  DnLam{ty: T.Bt}

type Da is Data:
  DaOne{m: Maybe<&2, T.Bt>}
  DaMany{m: Maybe<&2, List<&2, T.Bt>>}

type DfB is Data:
  DfB{n: String, v: String}

type Dk is Data:
  DkSigma{}
  DkEither{}
  DkFix{}
  DkCofree{}
  DkCofreeF{}
  DkOwn{}

def fd.dv.bases() -> List<&2, DfB>:
  [DfB{"Nat", "0n"}, DfB{"U32", "0"}, DfB{"Char", "' '"}, DfB{"Bool", "False{}"}, DfB{"Unit", "Unit{}"}, DfB{"F32", "0.0"}, DfB{"Cmp", "EQ{}"}, DfB{"List", "[]"}, DfB{"Maybe", "None{}"}, DfB{"HsPrelude.HsInt", "HsPrelude.HsInt.Pos{0n}"}, DfB{"HsPrelude.HsRational", "HsPrelude.HsRational{HsPrelude.HsInt.Pos{0n}, 1n}"}, DfB{"HsPrelude.HsMap", "HsPrelude.HsMap.Tip{}"}, DfB{"HsPrelude.HsSet", "HsPrelude.HsSet.Tip{}"}, DfB{"HsPrelude.HsPcRep", "HsPrelude.HsPcRep{False{}, HsPrelude.HsPcRes.Bad{HsPrelude.HsPcError.Fancy{0n, []}, HsPrelude.HsPcSt{[], 0n, 1n, 1n, []}}}"}, DfB{"HsPrelude.HsPcPos", "HsPrelude.HsPcPos{[], 1n, 1n}"}]

def fd.dv.base(xs: List<&2, DfB>, +n: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match xs:
    case Nil{}:
      None{}
    case DfB{k, v} <> t:
      Bool.pick(Maybe<&2, T.Bt>, S.eq(S.b(k), n), Some{T.BtVar{S.b(v)}}, fd.dv.base(t, n))

# a type function applied, reduced: (r => B)(X) is B with X for r
def fd.dv.beta(t: T.Bt) -> T.Bt:
  match t:
    case T.BtApp{T.BtLam{m, x, b}, T.BtArgs{a, T.BtANil{}}}:
      T.tba.subst(b, x, a)
    case u:
      u

# a type's parameters given: ps[i] is args[i] in ty
def fd.dv.sub(ps: List<&2, T.BParam>, args: T.Bt, ty: T.Bt) -> T.Bt:
  match ps args:
    case T.BParam{m, x, k} <> pt T.BtArgs{a, rest}:
      fd.dv.sub(pt, rest, T.tba.subst(ty, x, a))
    case _ _:
      ty

def fd.dv.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> fd.dv.list(t)
    case _:
      Nil{}

def fd.dv.f(x: String, ty: T.Bt) -> T.BField:
  T.BField{S.b(x), ty}

def fd.dv.isty(it: T.BItem) -> Bool:
  match it:
    case T.BiType{n, ps, k, cs, d}:
      True{}
    case _:
      False{}

def fd.dv.find(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Maybe<&2, T.BItem>:
  match its:
    case Nil{}:
      None{}
    case +h <> t:
      Bool.pick(Maybe<&2, T.BItem>, Bool.and(fd.dv.isty(h), S.eq(fd.item.name(h), n)), Some{h}, fd.dv.find(t, n))

def fd.dv.keep(b: Bool, c: T.BCtor, rest: List<&2, T.BCtor>) -> List<&2, T.BCtor>:
  match b:
    case True{}:
      c <> rest
    case False{}:
      rest

def fd.dv.nullary(cs: List<&2, T.BCtor>) -> List<&2, T.BCtor>:
  match cs:
    case Nil{}:
      Nil{}
    case T.BCtor{c, +fs} <> t:
      fd.dv.keep(List.is_empty(&2, T.BField, fs), T.BCtor{c, fs}, fd.dv.nullary(t))

# whether a field's type names n
def fd.dv.names(fs: List<&2, T.BField>, +n: List<&2, U32>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case T.BField{x, ty} <> t:
      Bool.or(S.mem(n, T.tba.refs(ty, Nil{})), fd.dv.names(t, n))

def fd.dv.flat(+n: List<&2, U32>, cs: List<&2, T.BCtor>) -> List<&2, T.BCtor>:
  match cs:
    case Nil{}:
      Nil{}
    case T.BCtor{c, +fs} <> t:
      fd.dv.keep(Bool.not(fd.dv.names(fs, n)), T.BCtor{c, fs}, fd.dv.flat(n, t))

def fd.dv.one(cs: List<&2, T.BCtor>) -> Dn:
  DnAsk{DqCs{cs, Nil{}, Nil{}, T.BtANil{}}}

def fd.dv.none() -> Dn:
  DnDone{DaOne{None{}}}

def fd.dv.own(m: Maybe<&2, T.BItem>, args: T.Bt) -> Dn:
  match m:
    case Some{T.BiType{+n, ps, k, +cs, d}}:
      DnAsk{DqCs{fd.dv.nullary(cs), [fd.dv.flat(n, cs), cs], ps, args}}
    case _:
      fd.dv.none()

def fd.dv.kind(+n: List<&2, U32>) -> Dk:
  Bool.pick(Dk, fd.is(n, "Sigma"), DkSigma{}, Bool.pick(Dk, fd.is(n, "Either"), DkEither{}, Bool.pick(Dk, fd.is(n, "HsPrelude.Fix"), DkFix{}, Bool.pick(Dk, fd.is(n, "HsPrelude.Cofree"), DkCofree{}, Bool.pick(Dk, fd.is(n, "HsPrelude.CofreeF"), DkCofreeF{}, DkOwn{})))))

def fd.dv.app2(k: Dk, +n: List<&2, U32>, xs: List<&2, T.Bt>, +tys: List<&2, T.BItem>) -> Dn:
  match k xs:
    case DkSigma{} q1 <> q2 <> a <> T.BtLam{m, x, b} <> Nil{}:
      fd.dv.one([T.BCtor{S.b("Tuple"), [fd.dv.f("a", a), fd.dv.f("b", b)]}])
    case DkEither{} q1 <> q2 <> a <> b <> Nil{}:
      fd.dv.one([T.BCtor{S.b("Inl"), [fd.dv.f("a", a)]}, T.BCtor{S.b("Inr"), [fd.dv.f("b", b)]}])
    case DkFix{} +f <> Nil{}:
      fd.dv.one([T.BCtor{S.b("HsPrelude.Fix.Fix"), [fd.dv.f("a", fd.dv.beta(T.BtApp{f, T.tba.args([T.BtTyApp{n, T.tba.args([f])}])}))]}])
    case DkCofree{} +f <> +a <> Nil{}:
      fd.dv.one([T.BCtor{S.b("HsPrelude.Cofree.Cofree"), [fd.dv.f("a", a), fd.dv.f("b", fd.dv.beta(T.BtApp{f, T.tba.args([T.BtTyApp{n, T.tba.args([f, a])}])}))]}])
    case DkCofreeF{} f <> a <> b <> Nil{}:
      fd.dv.one([T.BCtor{S.b("HsPrelude.CofreeF.CofreeF"), [fd.dv.f("a", a), fd.dv.f("b", fd.dv.beta(T.BtApp{f, T.tba.args([b])}))]}])
    case DkOwn{} ys:
      fd.dv.own(fd.dv.find(tys, n), T.tba.args(ys))
    case _ _:
      fd.dv.none()

def fd.dv.app(b: Maybe<&2, T.Bt>, +n: List<&2, U32>, args: T.Bt, +tys: List<&2, T.BItem>) -> Dn:
  match b:
    case Some{v}:
      DnDone{DaOne{Some{v}}}
    case None{}:
      fd.dv.app2(fd.dv.kind(n), n, fd.dv.list(args), tys)

def fd.dv.ty(ty: T.Bt, +tys: List<&2, T.BItem>) -> Dn:
  match ty:
    case T.BtTyApp{+n, args}:
      fd.dv.app(fd.dv.base(fd.dv.bases(), n), n, args, tys)
    case T.BtVar{+n}:
      fd.dv.app(fd.dv.base(fd.dv.bases(), n), n, T.BtANil{}, tys)
    case T.BtPi{m, x, d, a, b}:
      DnLam{b}
    case _:
      fd.dv.none()

def fd.dv.lam(a: Da) -> Da:
  match a:
    case DaOne{m}:
      match m:
        case Some{v}:
          DaOne{Some{T.BtLam{T.BmLive{}, S.b("_"), v}}}
        case None{}:
          DaOne{None{}}
    case DaMany{m}:
      DaOne{None{}}

def fd.dv.cons(v: T.Bt, a: Da) -> Da:
  match a:
    case DaMany{m}:
      match m:
        case Some{xs}:
          DaMany{Some{v <> xs}}
        case None{}:
          DaMany{None{}}
    case DaOne{m}:
      DaMany{None{}}

def fd.dv.go(fuel: Nat, q: Dq, +tys: List<&2, T.BItem>) -> Da:
  match fuel:
    case 0n:
      DaOne{None{}}
    case 1n+(+p):
      match q:
        case DqTy{ty}:
          fd.dv.go(p, DqRun{fd.dv.ty(fd.dv.beta(ty), tys)}, tys)
        case DqRun{n}:
          match n:
            case DnDone{a}:
              a
            case DnAsk{q2}:
              fd.dv.go(p, q2, tys)
            case DnLam{ty}:
              fd.dv.lam(fd.dv.go(p, DqTy{ty}, tys))
        case DqCs{cs, next, +ps, +args}:
          match cs:
            case Nil{}:
              match next:
                case Nil{}:
                  DaOne{None{}}
                case h <> t:
                  fd.dv.go(p, DqCs{h, t, ps, args}, tys)
            case T.BCtor{c, fs} <> t:
              fd.dv.go(p, DqPick{fd.dv.go(p, DqFs{fs, ps, args}, tys), c, t, next, ps, args}, tys)
        case DqPick{r, c, cs, next, ps, args}:
          match r:
            case DaMany{m}:
              match m:
                case Some{xs}:
                  DaOne{Some{T.BtCon{c, T.tba.args(xs)}}}
                case None{}:
                  fd.dv.go(p, DqCs{cs, next, ps, args}, tys)
            case DaOne{m}:
              fd.dv.go(p, DqCs{cs, next, ps, args}, tys)
        case DqFs{fs, +ps, +args}:
          match fs:
            case Nil{}:
              DaMany{Some{Nil{}}}
            case T.BField{x, ty} <> t:
              fd.dv.go(p, DqCons{fd.dv.go(p, DqTy{fd.dv.sub(ps, args, ty)}, tys), t, ps, args}, tys)
        case DqCons{r, fs, ps, args}:
          match r:
            case DaOne{m}:
              match m:
                case Some{v}:
                  fd.dv.cons(v, fd.dv.go(p, DqFs{fs, ps, args}, tys))
                case None{}:
                  DaMany{None{}}
            case DaMany{m}:
              DaMany{None{}}

def fd.dv.out(a: Da) -> T.Bt:
  match a:
    case DaOne{m}:
      match m:
        case Some{v}:
          v
        case None{}:
          fd.todo("fold:fuel-default-at-type")
    case DaMany{m}:
      fd.todo("fold:fuel-default-at-type")

# a default of type ty (the module's items tys give its own types)
def fd.dv(ty: T.Bt, +tys: List<&2, T.BItem>) -> T.Bt:
  fd.dv.out(fd.dv.go(120n, DqTy{ty}, tys))

# The fuelled def --------------------------------------------------------------

# how many type and template parameters lead
def fd.fu.lead(ps: List<&2, T.BParam>) -> Nat:
  match ps:
    case T.BParam{T.BmErased{}, x, ty} <> t:
      1n+fd.fu.lead(t)
    case T.BParam{T.BmTpl{}, x, ty} <> t:
      1n+fd.fu.lead(t)
    case _:
      0n

# the parameters with fuel_ after the first k
def fd.fu.ps(k: Nat, ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match k ps:
    case 1n+j h <> t:
      h <> fd.fu.ps(j, t)
    case _ rest:
      T.BParam{T.BmLive{}, S.b("fuel_"), fd.ty0("Nat")} <> rest

# an argument spine with f after the first k
def fd.fu.args(k: Nat, a: T.Bt, f: T.Bt) -> T.Bt:
  match k a:
    case 1n+j T.BtArgs{h, t}:
      T.BtArgs{h, fd.fu.args(j, t, f)}
    case _ rest:
      T.BtArgs{f, rest}

# the parameters as the arguments of a call
def fd.fu.pargs(ps: List<&2, T.BParam>) -> T.Bt:
  match ps:
    case T.BParam{T.BmErased{}, x, ty} <> t:
      T.BtArgs{T.BtDead{T.BtVar{x}}, fd.fu.pargs(t)}
    case T.BParam{T.BmTpl{}, x, ty} <> t:
      T.BtArgs{T.BtTplArg{T.BtVar{x}}, fd.fu.pargs(t)}
    case T.BParam{m, x, ty} <> t:
      T.BtArgs{T.BtVar{x}, fd.fu.pargs(t)}
    case Nil{}:
      T.BtANil{}

# the place of x in ms
def fd.fu.idx(ms: List<&2, List<&2, U32>>, +x: List<&2, U32>, +i: Nat) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      None{}
    case +h <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(h, x), Some{i}, fd.fu.idx(t, x, 1n+i))

def fd.mu.inc(+g: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  fd.cat(g, fd.cat(S.b(".In.I"), fd.nshow(i)))

def fd.mu.outp(+g: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  fd.cat(g, fd.cat(S.b(".out"), fd.nshow(i)))

# a call of member i of the defs being fuelled: in a group (mu), the
# group's def at member i's constructor, its answer taken out unless the
# members share it (same); alone, its .fu with the fuel after the first k
def fd.fu.app(idx: Maybe<&2, Nat>, x: List<&2, U32>, a: T.Bt, +mu: Bool, +g: List<&2, U32>, +k: Nat, +f: T.Bt, +same: Bool) -> T.Bt:
  match idx mu same:
    case None{} _ _:
      T.BtApp{T.BtVar{x}, a}
    case Some{i} False{} _:
      T.BtApp{T.BtVar{fd.cat(g, S.b(".fu"))}, fd.fu.args(k, a, f)}
    case Some{+i} True{} True{}:
      T.BtApp{T.BtVar{g}, T.tba.args([f, T.BtCon{fd.mu.inc(g, i), a}])}
    case Some{+i} True{} False{}:
      T.BtApp{T.BtVar{fd.mu.outp(g, i)}, T.tba.args([T.BtApp{T.BtVar{g}, T.tba.args([f, T.BtCon{fd.mu.inc(g, i), a}])}])}

# t with each call of a member of ms made as fd.fu.app makes it
def fd.fu.rw(t: T.Bt, +ms: List<&2, List<&2, U32>>, +mu: Bool, +g: List<&2, U32>, +k: Nat, +f: T.Bt, +same: Bool) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+x}, a}:
      fd.fu.app(fd.fu.idx(ms, x, 0n), x, fd.fu.rw(a, ms, mu, g, k, f, same), mu, g, k, f, same)
    case T.BtApp{h, a}:
      T.BtApp{fd.fu.rw(h, ms, mu, g, k, f, same), fd.fu.rw(a, ms, mu, g, k, f, same)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.fu.rw(a, ms, mu, g, k, f, same)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.fu.rw(b, ms, mu, g, k, f, same)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.fu.rw(a, ms, mu, g, k, f, same)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, fd.fu.rw(a, ms, mu, g, k, f, same), fd.fu.rw(b, ms, mu, g, k, f, same)}
    case T.BtSucc{a}:
      T.BtSucc{fd.fu.rw(a, ms, mu, g, k, f, same)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.fu.rw(a, ms, mu, g, k, f, same), ty}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.fu.rw(cs, ms, mu, g, k, f, same)}
    case T.BtExpr{e}:
      T.BtExpr{fd.fu.rw(e, ms, mu, g, k, f, same)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.fu.rw(e, ms, mu, g, k, f, same), p, fd.fu.rw(b, ms, mu, g, k, f, same)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, fd.fu.rw(v, ms, mu, g, k, f, same), fd.fu.rw(b, ms, mu, g, k, f, same)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.fu.rw(b, ms, mu, g, k, f, same), fd.fu.rw(rest, ms, mu, g, k, f, same)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.fu.rw(a, ms, mu, g, k, f, same), fd.fu.rw(rest, ms, mu, g, k, f, same)}
    case u:
      u

# the pattern 1n+fuel_p, 1n+(+fuel_p) when the body uses it twice (written
# as text: ToBend's printer writes a copied successor's variable 1n++x)
def fd.fu.pv(m: T.BMode) -> T.Bt:
  match m:
    case T.BmCopy{}:
      T.BtSucc{T.BtVar{S.b("(+fuel_p)")}}
    case _:
      T.BtSucc{T.BtPv{T.BmLive{}, S.b("fuel_p")}}

# match fuel_: 0n is the default, 1n+fuel_p the body (its self-calls given
# fuel_p)
def fd.fu.body(+k: Nat, +n: List<&2, U32>, +r: T.Bt, b: T.Bt, +tys: List<&2, T.BItem>) -> T.Bt:
  +b2 = fd.fu.rw(b, [n], False{}, n, k, T.BtVar{S.b("fuel_p")}, False{})
  T.BtMatch{T.tba.args([T.BtVar{S.b("fuel_")}]), T.BtCase{T.tba.args([T.BtNat{S.b("0")}]), T.BtExpr{fd.dv(r, tys)}, T.BtCase{T.tba.args([fd.fu.pv(fd.mode(fd.uses(b2, S.b("fuel_p"))))]), b2, T.BtCEnd{}}}}

# a def Bend refuses for its self-call: f.fu with the fuel, and f
def fd.fu.def(it: T.BItem, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match it:
    case T.BiDef{+n, +ps, +r, b, d}:
      +k = fd.fu.lead(ps)
      [T.BiDef{fd.cat(n, S.b(".fu")), fd.fu.ps(k, ps), r, fd.fu.body(k, n, r, b, tys), S.b("generated: fuel: Bend sees no argument of the self-call shrink, so a Nat counts the depth down") <> d}, T.BiDef{n, ps, r, T.BtExpr{T.BtApp{T.BtVar{fd.cat(n, S.b(".fu"))}, fd.fu.args(k, fd.fu.pargs(ps), fd.fu.max())}}, [S.b("fuel: 2^32 - 1, a depth no run reaches")]}]
    case other:
      [other]

def fd.fu.one(hit: Bool, h: T.BItem, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match hit:
    case True{}:
      fd.fu.def(h, tys)
    case False{}:
      [h]

# its with the def named n fuelled
def fd.fu.swap(its: List<&2, T.BItem>, +n: List<&2, U32>, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case +h <> t:
      List.append(&2, T.BItem, fd.fu.one(S.eq(fd.item.name(h), n), h, tys), fd.fu.swap(t, n, tys))

# whether a def of its is named n
def fd.fu.isdef(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case Nil{}:
      False{}
    case +h <> t:
      Bool.or(Bool.and(Bool.not(fd.dv.isty(h)), S.eq(fd.item.name(h), n)), fd.fu.isdef(t, n))

# the result type of the def named n
def fd.fu.ret(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Maybe<&2, T.Bt>:
  match its:
    case Nil{}:
      None{}
    case T.BiDef{+k, ps, r, b, d} <> t:
      Bool.pick(Maybe<&2, T.Bt>, S.eq(k, n), Some{r}, fd.fu.ret(t, n))
    case h <> t:
      fd.fu.ret(t, n)

# whether a default of the type is to hand (else the def is dropped as
# before: a ?TODO in the file names no def to blame)
def fd.fu.dvok(m: Maybe<&2, T.Bt>, +tys: List<&2, T.BItem>) -> Bool:
  match m:
    case Some{r}:
      List.is_empty(&2, List<&2, U32>, T.tba.todos(fd.dv(r, tys), Nil{}))
    case None{}:
      False{}

# whether the error is a self-call Bend does not see shrink, in a def not
# fuelled yet
def fd.fu.can(who: Maybe<&2, List<&2, U32>>, +why: List<&2, U32>, +its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> Bool:
  match who:
    case Some{+n}:
      Bool.and(Bool.and(Bool.and(S.infix(why, S.b("a decreasing self-call")), fd.fu.isdef(its, n)), Bool.not(fd.fu.isdef(its, fd.cat(n, S.b(".fu"))))), fd.fu.dvok(fd.fu.ret(its, n), List.append(&2, T.BItem, its, dt)))
    case None{}:
      False{}

def fd.fu.name(who: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match who:
    case Some{n}:
      n
    case None{}:
      Nil{}

# the gate's repair: fuel for a self-call Bend refuses, else the drop
def fd.gate.fix(can: Bool, who: Maybe<&2, List<&2, U32>>, +its: List<&2, T.BItem>, o: List<&2, Dr>, +why: List<&2, U32>, +dt: List<&2, T.BItem>) -> Gs:
  match can:
    case True{}:
      Gs{fd.fu.swap(its, fd.fu.name(who), List.append(&2, T.BItem, its, dt)), o, False{}}
    case False{}:
      fd.gate.drop(who, its, o, why)


# A group of defs that call each other (a cycle of calls, which Bend
# refuses) is one def g = HEAD.mu, as telomare's bend branch writes its
# mutual walks (Desugar.bend's go over ON, Levels.bend's occ): its
# parameters the fuel and a sum g.In with a constructor per member holding
# the member's arguments; its answer the members' answer when they share
# it, else a sum g.Out with a constructor per member's answer (g.outK takes
# it out, a default at the others); each member a call of g at its own
# constructor.  Only groups whose members take no type or template
# parameter and fold whole (no ?TODO) are merged; the others are left for
# the gate, as before.

def fd.mu.isdef(it: T.BItem) -> Bool:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      True{}
    case _:
      False{}

def fd.mu.opt(m: Maybe<&2, T.BItem>) -> List<&2, T.BItem>:
  match m:
    case Some{x}:
      [x]
    case None{}:
      Nil{}

# the module's defs, each with the module's defs it names
type Mcg is Data:
  Mcg{n: List<&2, U32>, cs: List<&2, List<&2, U32>>}

# what each def reaches by its calls
type Mrch is Data:
  Mrch{n: List<&2, U32>, r: Map<&2, Bool>}

def fd.mu.names(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case Nil{}:
      Nil{}
    case +h <> t:
      T.tba.keep(Bool.not(fd.mu.isdef(h)), fd.item.name(h), fd.mu.names(t))

def fd.mu.keep(xs: List<&2, List<&2, U32>>, +ns: Map<&2, Bool>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      T.tba.keep(Bool.not(T.tba.has.got(Map.has(&2, Bool, ns, S.str(x)))), x, fd.mu.keep(t, ns))

def fd.mu.cgput(b: Bool, c: Mcg, rest: List<&2, Mcg>) -> List<&2, Mcg>:
  match b:
    case True{}:
      c <> rest
    case False{}:
      rest

def fd.mu.cg(its: List<&2, T.BItem>, +ns: Map<&2, Bool>) -> List<&2, Mcg>:
  match its:
    case Nil{}:
      Nil{}
    case +h <> t:
      fd.mu.cgput(fd.mu.isdef(h), Mcg{fd.item.name(h), fd.mu.keep(T.tba.item.refs(h), ns)}, fd.mu.cg(t, ns))

def fd.mu.calls(cg: List<&2, Mcg>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match cg:
    case Nil{}:
      Nil{}
    case Mcg{+k, +cs} <> t:
      Bool.pick(List<&2, List<&2, U32>>, S.eq(k, n), cs, fd.mu.calls(t, n))

def fd.mu.visit(seen: Bool, +h: List<&2, U32>, t: List<&2, List<&2, U32>>, s: Map<&2, Bool>, +cg: List<&2, Mcg>) -> List<&2, List<&2, U32>> & Map<&2, Bool>:
  match seen:
    case True{}:
      (t, s)
    case False{}:
      (List.append(&2, List<&2, U32>, fd.mu.calls(cg, h), t), Map.set(&2, Bool, s, S.str(h), True{}))

def fd.mu.step(r: Map<&2, Bool> & Bool, +h: List<&2, U32>, t: List<&2, List<&2, U32>>, +cg: List<&2, Mcg>) -> List<&2, List<&2, U32>> & Map<&2, Bool>:
  match r:
    case Tuple{s1, b}:
      fd.mu.visit(b, h, t, s1, cg)

# the defs reached from the todo list (a walk; seen, the map)
def fd.mu.reach(fuel: Nat, st: List<&2, List<&2, U32>> & Map<&2, Bool>, +cg: List<&2, Mcg>) -> Map<&2, Bool>:
  match fuel:
    case 0n:
      match st:
        case Tuple{todo, s}:
          s
    case 1n+p:
      match st:
        case Tuple{todo, s}:
          match todo:
            case +h <> t:
              fd.mu.reach(p, fd.mu.step(Map.has(&2, Bool, s, S.str(h)), h, t, cg), cg)
            case Nil{}:
              s

def fd.mu.edges(cg: List<&2, Mcg>) -> Nat:
  match cg:
    case Nil{}:
      1n
    case Mcg{k, cs} <> t:
      Nat.add(1n+List.length(&2, List<&2, U32>, cs), fd.mu.edges(t))

def fd.mu.rchs(ns: List<&2, List<&2, U32>>, +cg: List<&2, Mcg>, +fuel: Nat) -> List<&2, Mrch>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> t:
      Mrch{n, fd.mu.reach(fuel, (fd.mu.calls(cg, n), Map.new(&2, Bool)), cg)} <> fd.mu.rchs(t, cg, fuel)

# whether a reaches b
def fd.mu.reaches(rs: List<&2, Mrch>, +a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Mrch{+k, +r} <> t:
      Bool.pick(Bool, S.eq(k, a), T.tba.has.got(Map.has(&2, Bool, r, S.str(b))), fd.mu.reaches(t, a, b))

# the defs of n's cycle: those n reaches that reach n
def fd.mu.group(ns: List<&2, List<&2, U32>>, +rs: List<&2, Mrch>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case +m <> t:
      T.tba.keep(Bool.not(Bool.and(fd.mu.reaches(rs, n, m), fd.mu.reaches(rs, m, n))), m, fd.mu.group(t, rs, n))

def fd.mu.put(fresh: Bool, g: List<&2, List<&2, U32>>, gs: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match fresh:
    case True{}:
      g <> gs
    case False{}:
      gs

def fd.mu.inany(gs: List<&2, List<&2, List<&2, U32>>>, +n: List<&2, U32>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case +g <> t:
      Bool.or(S.mem(n, g), fd.mu.inany(t, n))

# the cycles of two defs or more, each once
def fd.mu.groups(ns: List<&2, List<&2, U32>>, +all: List<&2, List<&2, U32>>, +rs: List<&2, Mrch>, +acc: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, List<&2, U32>>>:
  match ns:
    case Nil{}:
      acc
    case +n <> t:
      +g = fd.mu.group(all, rs, n)
      fd.mu.groups(t, all, rs, fd.mu.put(Bool.and(Nat.is_gt(List.length(&2, List<&2, U32>, g), 1n), Bool.not(fd.mu.inany(acc, n))), g, acc))

# the def named n
def fd.mu.get(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Maybe<&2, T.BItem>:
  match its:
    case Nil{}:
      None{}
    case +h <> t:
      Bool.pick(Maybe<&2, T.BItem>, Bool.and(fd.mu.isdef(h), S.eq(fd.item.name(h), n)), Some{h}, fd.mu.get(t, n))

def fd.mu.gets(ns: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      List.append(&2, T.BItem, fd.mu.opt(fd.mu.get(its, n)), fd.mu.gets(t, its))

def fd.mu.anytpl(ps: List<&2, T.BParam>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case T.BParam{T.BmErased{}, x, ty} <> t:
      True{}
    case T.BParam{T.BmTpl{}, x, ty} <> t:
      True{}
    case h <> t:
      fd.mu.anytpl(t)

# whether a member can be merged: no type or template parameter, no ?TODO
def fd.mu.ok1(it: T.BItem) -> Bool:
  match it:
    case T.BiDef{n, +ps, r, +b, d}:
      Bool.and(Nat.is_eq(fd.fu.lead(ps), 0n), Bool.and(Bool.not(fd.mu.anytpl(ps)), List.is_empty(&2, List<&2, U32>, T.tba.todos(b, Nil{}))))
    case _:
      False{}

def fd.mu.ok(ds: List<&2, T.BItem>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(fd.mu.ok1(h), fd.mu.ok(t))

def fd.mu.ret(it: T.BItem) -> T.Bt:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      r
    case _:
      fd.todo("fold:mutual")

def fd.mu.rtext(+it: T.BItem) -> List<&2, U32>:
  P.tpr.t(fd.mu.ret(it), P.TpLoose{}, 0n, Nil{})

# whether the members share their answer's type
def fd.mu.same(ds: List<&2, T.BItem>, +r0: List<&2, U32>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(S.eq(fd.mu.rtext(h), r0), fd.mu.same(t, r0))

def fd.mu.fields(ps: List<&2, T.BParam>) -> List<&2, T.BField>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      T.BField{x, ty} <> fd.mu.fields(t)

def fd.mu.inctors(ds: List<&2, T.BItem>, +g: List<&2, U32>, +i: Nat) -> List<&2, T.BCtor>:
  match ds:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, b, d} <> t:
      T.BCtor{fd.mu.inc(g, i), fd.mu.fields(ps)} <> fd.mu.inctors(t, g, 1n+i)
    case h <> t:
      fd.mu.inctors(t, g, 1n+i)

def fd.mu.oc(+g: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  fd.cat(g, fd.cat(S.b(".Out.O"), fd.nshow(i)))

def fd.mu.outctors(ds: List<&2, T.BItem>, +g: List<&2, U32>, +i: Nat) -> List<&2, T.BCtor>:
  match ds:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BCtor{fd.mu.oc(g, i), [T.BField{S.b("value"), fd.mu.ret(h)}]} <> fd.mu.outctors(t, g, 1n+i)

# a body's answers as c of them
def fd.mu.wrap(b: T.Bt, +c: List<&2, U32>) -> T.Bt:
  match b:
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.mu.wrap(cs, c)}
    case T.BtCase{p, e, rest}:
      T.BtCase{p, fd.mu.wrap(e, c), fd.mu.wrap(rest, c)}
    case T.BtLet{x, v, e}:
      T.BtLet{x, v, fd.mu.wrap(e, c)}
    case T.BtRw{e, p, e2}:
      T.BtRw{e, p, fd.mu.wrap(e2, c)}
    case T.BtExpr{e}:
      T.BtExpr{T.BtCon{c, T.tba.args([e])}}
    case T.BtCEnd{}:
      T.BtCEnd{}
    case e:
      T.BtCon{c, T.tba.args([e])}

def fd.mu.pvs(ps: List<&2, T.BParam>, +b: T.Bt) -> List<&2, T.Bt>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, +x, ty} <> t:
      T.BtPv{fd.mode(fd.uses(b, x)), x} <> fd.mu.pvs(t, b)

def fd.mu.wrap.if(same: Bool, b: T.Bt, +c: List<&2, U32>) -> T.Bt:
  match same:
    case True{}:
      b
    case False{}:
      fd.mu.wrap(b, c)

# g's cases: member i's constructor, its body (calls of members made calls
# of g), its answer as g.Out's when the members do not share theirs
def fd.mu.cases(ds: List<&2, T.BItem>, +ns: List<&2, List<&2, U32>>, +g: List<&2, U32>, +same: Bool, +i: Nat) -> T.Bt:
  match ds:
    case Nil{}:
      T.BtCEnd{}
    case T.BiDef{n, +ps, r, b, d} <> t:
      +b2 = fd.mu.wrap.if(same, fd.fu.rw(b, ns, True{}, g, 0n, T.BtVar{S.b("fuel_p")}, same), fd.mu.oc(g, i))
      T.BtCase{T.tba.args([T.BtCon{fd.mu.inc(g, i), T.tba.args(fd.mu.pvs(ps, b2))}]), b2, fd.mu.cases(t, ns, g, same, 1n+i)}
    case h <> t:
      fd.mu.cases(t, ns, g, same, 1n+i)

def fd.mu.doc(+ns: List<&2, List<&2, U32>>) -> List<&2, U32>:
  fd.cat(S.b("generated: fuel: the mutual recursion of "), S.join(ns, 32))

def fd.mu.wrap.call(same: Bool, call: T.Bt, +o: List<&2, U32>) -> T.Bt:
  match same:
    case True{}:
      call
    case False{}:
      T.BtApp{T.BtVar{o}, T.tba.args([call])}

# A member whose answer is a function (a def written point-free, as
# freeD = cata alg is) takes its argument as a parameter of its own in the
# group, as many as its answer's arrows (up to 4): g.Out's fields are data,
# and a function is not. Its body is applied to the new variable mu_aK (a
# lambda's variable renamed to it), its calls in the group are given the
# arguments they are applied to (else eta-expanded, mu_eK => ...), and its
# def outside the group is the lambda again.

type Mab is Data:
  Mab{n: List<&2, U32>, k: Nat}

type Mabi is Data:
  Mabi{it: T.BItem, k: Nat}

def fd.mu.ab.v(+k: Nat) -> List<&2, U32>:
  fd.cat(S.b("mu_a"), fd.nshow(k))

# e applied to the variable v
def fd.mu.ab.ap(e: T.Bt, +v: List<&2, U32>) -> T.Bt:
  match e:
    case T.BtLam{m, +y, b}:
      T.tba.subst(b, y, T.BtVar{v})
    case u:
      T.BtApp{u, T.tba.args([T.BtVar{v}])}

# a body's answers applied to v
def fd.mu.ab.app(b: T.Bt, +v: List<&2, U32>) -> T.Bt:
  match b:
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.mu.ab.app(cs, v)}
    case T.BtCase{p, e, rest}:
      T.BtCase{p, fd.mu.ab.app(e, v), fd.mu.ab.app(rest, v)}
    case T.BtLet{x, val, e}:
      T.BtLet{x, val, fd.mu.ab.app(e, v)}
    case T.BtRw{e, p, e2}:
      T.BtRw{e, p, fd.mu.ab.app(e2, v)}
    case T.BtExpr{e}:
      T.BtExpr{fd.mu.ab.ap(e, v)}
    case T.BtCEnd{}:
      T.BtCEnd{}
    case e:
      fd.mu.ab.ap(e, v)

# it with one more parameter, when its answer is a function
def fd.mu.ab1(it: T.BItem, +k: Nat) -> Maybe<&2, T.BItem>:
  match it:
    case T.BiDef{n, ps, T.BtPi{pm, px, False{}, a, b}, body, d}:
      +v = fd.mu.ab.v(k)
      +b2 = fd.mu.ab.app(body, v)
      Some{T.BiDef{n, List.append(&2, T.BParam, ps, [T.BParam{fd.mode(fd.uses(b2, v)), v, a}]), b, b2, d}}
    case _:
      None{}

def fd.mu.ab.go(fuel: Nat, m: Maybe<&2, T.BItem>, it: T.BItem, +k: Nat) -> Mabi:
  match fuel m:
    case 1n+f Some{+j}:
      fd.mu.ab.go(f, fd.mu.ab1(j, 1n+k), j, 1n+k)
    case _ _:
      Mabi{it, k}

def fd.mu.abs(ds: List<&2, T.BItem>) -> List<&2, Mabi>:
  match ds:
    case Nil{}:
      Nil{}
    case +h <> t:
      fd.mu.ab.go(4n, fd.mu.ab1(h, 0n), h, 0n) <> fd.mu.abs(t)

def fd.mu.abks(xs: List<&2, Mabi>) -> List<&2, Mab>:
  match xs:
    case Nil{}:
      Nil{}
    case Mabi{it, k} <> t:
      Mab{fd.item.name(it), k} <> fd.mu.abks(t)

def fd.mu.abits(xs: List<&2, Mabi>) -> List<&2, T.BItem>:
  match xs:
    case Nil{}:
      Nil{}
    case Mabi{it, k} <> t:
      it <> fd.mu.abits(t)

def fd.mu.abk(ks: List<&2, Mab>, +x: List<&2, U32>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case Mab{+n, +k} <> t:
      Bool.pick(Nat, S.eq(n, x), k, fd.mu.abk(t, x))

def fd.mu.etas(k: Nat, +i: Nat) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      fd.cat(S.b("mu_e"), fd.nshow(i)) <> fd.mu.etas(p, 1n+i)

def fd.mu.vars(xs: List<&2, List<&2, U32>>) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BtVar{h} <> fd.mu.vars(t)

def fd.mu.lamv(xs: List<&2, List<&2, U32>>, b: T.Bt) -> T.Bt:
  match xs:
    case Nil{}:
      b
    case h <> t:
      T.BtLam{T.BmLive{}, h, fd.mu.lamv(t, b)}

def fd.mu.lams(ps: List<&2, T.BParam>, b: T.Bt) -> T.Bt:
  match ps:
    case Nil{}:
      b
    case T.BParam{m, x, ty} <> t:
      T.BtLam{m, x, fd.mu.lams(t, b)}

# x(a) of a member that takes k more: eta-expanded
def fd.mu.sat1(k: Nat, +x: List<&2, U32>, a: T.Bt) -> T.Bt:
  match k:
    case 0n:
      T.BtApp{T.BtVar{x}, a}
    case 1n+(+p):
      +vs = fd.mu.etas(1n+p, 0n)
      fd.mu.lamv(vs, T.BtApp{T.BtVar{x}, T.tba.args(List.append(&2, T.Bt, fd.dv.list(a), fd.mu.vars(vs)))})

def fd.mu.more(f: T.Bt, xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case Nil{}:
      f
    case h <> t:
      T.BtApp{f, T.tba.args(h <> t)}

def fd.mu.sat2b(ge: Bool, +k: Nat, +x: List<&2, U32>, a: T.Bt, b: T.Bt, +bs: List<&2, T.Bt>) -> T.Bt:
  match ge:
    case True{}:
      fd.mu.more(T.BtApp{T.BtVar{x}, T.tba.args(List.append(&2, T.Bt, fd.dv.list(a), List.take(&2, T.Bt, bs, k)))}, List.drop(&2, T.Bt, bs, k))
    case False{}:
      T.BtApp{fd.mu.sat1(k, x, a), b}

# x(a)(b) of a member that takes k more: given them from b
def fd.mu.sat2(k: Nat, +x: List<&2, U32>, a: T.Bt, +b: T.Bt) -> T.Bt:
  match k:
    case 0n:
      T.BtApp{T.BtApp{T.BtVar{x}, a}, b}
    case 1n+(+p):
      +bs = fd.dv.list(b)
      fd.mu.sat2b(Nat.is_ge(List.length(&2, T.Bt, bs), 1n+p), 1n+p, x, a, b, bs)

# t with the calls of members that take more given them
def fd.mu.sat(t: T.Bt, +ks: List<&2, Mab>) -> T.Bt:
  match t:
    case T.BtApp{T.BtApp{T.BtVar{+x}, a}, b}:
      fd.mu.sat2(fd.mu.abk(ks, x), x, fd.mu.sat(a, ks), fd.mu.sat(b, ks))
    case T.BtApp{T.BtVar{+x}, a}:
      fd.mu.sat1(fd.mu.abk(ks, x), x, fd.mu.sat(a, ks))
    case T.BtApp{h, a}:
      T.BtApp{fd.mu.sat(h, ks), fd.mu.sat(a, ks)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.mu.sat(a, ks)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.mu.sat(b, ks)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.mu.sat(a, ks)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, fd.mu.sat(a, ks), fd.mu.sat(b, ks)}
    case T.BtSucc{a}:
      T.BtSucc{fd.mu.sat(a, ks)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.mu.sat(a, ks), ty}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.mu.sat(cs, ks)}
    case T.BtExpr{e}:
      T.BtExpr{fd.mu.sat(e, ks)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.mu.sat(e, ks), p, fd.mu.sat(b, ks)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, fd.mu.sat(v, ks), fd.mu.sat(b, ks)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.mu.sat(b, ks), fd.mu.sat(rest, ks)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.mu.sat(a, ks), fd.mu.sat(rest, ks)}
    case u:
      u

def fd.mu.sats(ds: List<&2, T.BItem>, +ks: List<&2, Mab>) -> List<&2, T.BItem>:
  match ds:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, b, d} <> t:
      T.BiDef{n, ps, r, fd.mu.sat(b, ks), d} <> fd.mu.sats(t, ks)
    case h <> t:
      h <> fd.mu.sats(t, ks)

# the members, each a call of g at its constructor
def fd.mu.wrappers(ds: List<&2, T.BItem>, os: List<&2, T.BItem>, +g: List<&2, U32>, +same: Bool, +i: Nat) -> List<&2, T.BItem>:
  match ds os:
    case T.BiDef{n, +ps, r, b, d} <> t T.BiDef{n0, +ps0, r0, b0, d0} <> u:
      +call = {T.BtApp{T.BtVar{g}, T.tba.args([fd.fu.max(), T.BtCon{fd.mu.inc(g, i), fd.fu.pargs(ps)}])} : T.Bt}
      T.BiDef{n0, ps0, r0, T.BtExpr{fd.mu.lams(List.drop(&2, T.BParam, ps, List.length(&2, T.BParam, ps0)), fd.mu.wrap.call(same, call, fd.mu.outp(g, i)))}, [S.b("fuel: a call of the group's def, from 2^32 - 1")]} <> fd.mu.wrappers(t, u, g, same, 1n+i)
    case h <> t o <> u:
      fd.mu.wrappers(t, u, g, same, 1n+i)
    case _ _:
      Nil{}

# g.outK: member K's answer out of g.Out
def fd.mu.outs(ds: List<&2, T.BItem>, +g: List<&2, U32>, +tys: List<&2, T.BItem>, +i: Nat) -> List<&2, T.BItem>:
  match ds:
    case Nil{}:
      Nil{}
    case h <> t:
      +r = fd.mu.ret(h)
      T.BiDef{fd.mu.outp(g, i), [T.BParam{T.BmLive{}, S.b("o"), T.BtVar{fd.cat(g, S.b(".Out"))}}], r, T.BtMatch{T.tba.args([T.BtVar{S.b("o")}]), T.BtCase{T.tba.args([T.BtCon{fd.mu.oc(g, i), T.tba.args([T.BtPv{T.BmLive{}, S.b("v")}])}]), T.BtExpr{T.BtVar{S.b("v")}}, T.BtCase{T.tba.args([T.BtWild{}]), T.BtExpr{fd.dv(r, tys)}, T.BtCEnd{}}}}, [S.b("generated: fuel: a member's answer")]} <> fd.mu.outs(t, g, tys, 1n+i)

def fd.mu.head(ns: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ns:
    case h <> t:
      h
    case Nil{}:
      Nil{}

def fd.mu.first(ds: List<&2, T.BItem>) -> List<&2, U32>:
  match ds:
    case h <> t:
      fd.mu.rtext(h)
    case Nil{}:
      Nil{}

def fd.mu.r0(ds: List<&2, T.BItem>) -> T.Bt:
  match ds:
    case h <> t:
      fd.mu.ret(h)
    case Nil{}:
      fd.todo("fold:mutual")

# the group's items: g.In, g.Out and g.outK (when the answers differ), g,
# the members
def fd.mu.items(+ds: List<&2, T.BItem>, os: List<&2, T.BItem>, +ns: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +g = fd.cat(fd.mu.head(ns), S.b(".mu"))
  +same = fd.mu.same(ds, fd.mu.first(ds))
  +tin = {T.BiType{fd.cat(g, S.b(".In")), Nil{}, fd.v("Data"), fd.mu.inctors(ds, g, 0n), [S.b("generated: fuel: the group's arguments")]} : T.BItem}
  +tout = {T.BiType{fd.cat(g, S.b(".Out")), Nil{}, fd.v("Data"), fd.mu.outctors(ds, g, 0n), [S.b("generated: fuel: the group's answers")]} : T.BItem}
  +tys = {tout <> List.append(&2, T.BItem, its, dt) : List<&2, T.BItem>}
  +r = Bool.pick(T.Bt, same, fd.mu.r0(ds), T.BtVar{fd.cat(g, S.b(".Out"))})
  +body = {T.BtMatch{T.tba.args([T.BtVar{S.b("fuel_")}]), T.BtCase{T.tba.args([T.BtNat{S.b("0")}]), T.BtExpr{fd.dv(r, tys)}, T.BtCase{T.tba.args([fd.fu.pv(T.BmCopy{})]), T.BtMatch{T.tba.args([T.BtVar{S.b("in_")}]), fd.mu.cases(ds, ns, g, same, 0n)}, T.BtCEnd{}}}} : T.Bt}
  +gdef = {T.BiDef{g, [T.BParam{T.BmLive{}, S.b("fuel_"), fd.ty0("Nat")}, T.BParam{T.BmLive{}, S.b("in_"), T.BtVar{fd.cat(g, S.b(".In"))}}], r, body, [fd.mu.doc(ns)]} : T.BItem}
  List.concat(&2, T.BItem, [[tin], Bool.pick(List<&2, T.BItem>, same, Nil{}, tout <> fd.mu.outs(ds, g, tys, 0n)), [gdef], fd.mu.wrappers(ds, os, g, same, 0n)])

def fd.mu.dput(b: Bool, h: T.BItem, rest: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match b:
    case True{}:
      rest
    case False{}:
      h <> rest

# its with a group merged, when it can be: its members replaced
def fd.mu.drop(its: List<&2, T.BItem>, +ns: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case +h <> t:
      fd.mu.dput(Bool.and(fd.mu.isdef(h), S.mem(fd.item.name(h), ns)), h, fd.mu.drop(t, ns))

def fd.mu.one(+ns: List<&2, List<&2, U32>>, +its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +ds0 = fd.mu.gets(ns, its)
  +abs = fd.mu.abs(ds0)
  +ds = fd.mu.sats(fd.mu.abits(abs), fd.mu.abks(abs))
  +new = fd.mu.items(ds, ds0, ns, its, dt)
  Bool.pick(List<&2, T.BItem>, Bool.and(fd.mu.ok(ds), List.is_empty(&2, List<&2, U32>, fd.todos.all(new, Nil{}))), List.append(&2, T.BItem, fd.mu.drop(its, ns), new), its)

def fd.mu.each(gs: List<&2, List<&2, List<&2, U32>>>, its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match gs:
    case Nil{}:
      its
    case g <> t:
      fd.mu.each(t, fd.mu.one(g, its, dt), dt)

# the module's items with each mergeable group merged
def fd.mu.all(+its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +ns = fd.mu.names(its)
  +cg = fd.mu.cg(its, T.tba.set(ns, Map.new(&2, Bool)))
  +rs = fd.mu.rchs(ns, cg, fd.mu.edges(cg))
  fd.mu.each(fd.mu.groups(ns, ns, rs, Nil{}), its, dt)

# Local catas -----------------------------------------------------------------
#
# A cata whose algebra calls back the def it is in, or at a functor with a
# list of the recursive variable, is written as a def of its own at the
# call, D.cH (H a hash of the call's functor, types and algebra). The first:
# D and the algebra's defs are a group, one def with fuel once merged, and
# the algebra, a template argument of G.cata, would then hold the fuel,
# which Bend's templates refuse (they take only closed arguments). The
# second: such a functor has no G.cata (Bend sees no list shrink). D.cH
# matches the value at Fix or Cofree and the layer at the functor's
# constructors and applies the algebra to the layer, each recursive field a
# call of D.cH, each list, Maybe, pair or other functor of them a call of a
# def D.cH.hP mapping it (P its path: constructor, field, part). These call
# each other and D's group, and the group's merge takes them in.

# a cata call made local: its def, the functor, whether at Cofree, the
# functor's other type arguments, Cofree's W, the answer, the algebra
type Lc is Data:
  Lc{n: List<&2, U32>, g: List<&2, U32>, cof: Bool, as: List<&2, T.Bt>, w: T.Bt, r: T.Bt, alg: T.Bt}

# what the rewrite of a def knows: its name, what each def reaches, the
# functors, the types
type Lcx is Data:
  Lcx{d: List<&2, U32>, rs: List<&2, Mrch>, fz: List<&2, Fz>, tys: List<&2, T.BItem>}

# what writing a local cata knows: its name, the def it is out of, whether at
# Cofree, the algebra, the functor's parameters and their arguments in the
# value (src) and in the answer (dst), the functors, the types
type Lm is Data:
  Lm{n: List<&2, U32>, d: List<&2, U32>, cof: Bool, alg: T.Bt, ps: List<&2, T.BParam>, src: T.Bt, dst: T.Bt, fz: List<&2, Fz>, tys: List<&2, T.BItem>}

# a field still to write the mapping defs for: its role, its type (in the
# functor's parameters), its path
type Lw is Data:
  Lw{r: Fr, ty: T.Bt, p: List<&2, U32>}

def fd.lc.fzb(zs: List<&2, Fz>, +b: List<&2, U32>) -> Maybe<&2, Fz>:
  match zs:
    case Nil{}:
      None{}
    case Fz{k, +b2, tvs, cs} <> t:
      Bool.pick(Maybe<&2, Fz>, S.eq(b2, b), Some{Fz{k, b2, tvs, cs}}, fd.lc.fzb(t, b))

def fd.lc.fzk(zs: List<&2, Fz>, +k: List<&2, U32>) -> Maybe<&2, Fz>:
  match zs:
    case Nil{}:
      None{}
    case Fz{+k2, b, tvs, cs} <> t:
      Bool.pick(Maybe<&2, Fz>, S.eq(k2, k), Some{Fz{k2, b, tvs, cs}}, fd.lc.fzk(t, k))

# n without its last k characters
def fd.lc.cut(+n: List<&2, U32>, k: Nat) -> List<&2, U32>:
  List.take(&2, U32, n, Nat.sub(List.length(&2, U32, n), k))

def fd.lc.hash(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case c <> t:
      fd.lc.hash(t, (h * 33 + c : U32))

# whether one of xs is d or reaches it
def fd.lc.back(xs: List<&2, List<&2, U32>>, +rs: List<&2, Mrch>, +d: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> t:
      Bool.or(Bool.or(S.eq(x, d), fd.mu.reaches(rs, x, d)), fd.lc.back(t, rs, d))

def fd.lc.untpls(xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      fd.untpl(h) <> fd.lc.untpls(t)

def fd.lc.some(b: Bool, c: Lc) -> Maybe<&2, Lc>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      None{}

# the call's arguments after the functor's: Cofree's W, the answer, the
# algebra, the value (at Fix no W)
def fd.lc.q4(cof: Bool, ys: List<&2, T.Bt>, +nocata: Bool, +n: List<&2, U32>, +g: List<&2, U32>, +as: List<&2, T.Bt>, +d: List<&2, U32>, +rs: List<&2, Mrch>) -> Maybe<&2, Lc>:
  match cof ys:
    case True{} w <> r <> +alg <> x <> Nil{}:
      fd.lc.some(Bool.or(nocata, fd.lc.back(T.tba.refs(fd.untpl(alg), Nil{}), rs, d)), Lc{n, g, True{}, as, fd.untpl(w), fd.untpl(r), fd.untpl(alg)})
    case False{} r <> +alg <> x <> Nil{}:
      fd.lc.some(Bool.or(nocata, fd.lc.back(T.tba.refs(fd.untpl(alg), Nil{}), rs, d)), Lc{n, g, False{}, as, fd.v("Unit"), fd.untpl(r), fd.untpl(alg)})
    case _ _:
      None{}

def fd.lc.q3(ok: Bool, +nocata: Bool, +cof: Bool, +c: List<&2, U32>, +g: List<&2, U32>, +na: Nat, +xs: List<&2, T.Bt>, +d: List<&2, U32>, +rs: List<&2, Mrch>) -> Maybe<&2, Lc>:
  match ok:
    case False{}:
      None{}
    case True{}:
      +txt = P.tpr.t(T.tba.call(T.BtVar{c}, fd.init(xs)), P.TpLoose{}, 0n, Nil{})
      +n = fd.cat3(d, S.b(".c"), S.b(U32.show(fd.lc.hash(txt, 5381))))
      fd.lc.q4(cof, List.drop(&2, T.Bt, xs, na), nocata, n, g, fd.lc.untpls(List.take(&2, T.Bt, xs, na)), d, rs)

def fd.lc.q2(z: Maybe<&2, Fz>, ty: Maybe<&2, T.BItem>, +cof: Bool, +c: List<&2, U32>, +g: List<&2, U32>, +xs: List<&2, T.Bt>, +d: List<&2, U32>, +rs: List<&2, Mrch>, +fz: List<&2, Fz>) -> Maybe<&2, Lc>:
  match z ty:
    case Some{Fz{+k, b, tvs, +cs}} Some{T.BiType{tn, +ps, kd, tcs, td}}:
      +na = Nat.sub(List.length(&2, T.BParam, ps), 1n)
      fd.lc.q3(Nat.is_eq(List.length(&2, T.Bt, xs), Nat.add(na, Bool.pick(Nat, cof, 4n, 3n))), Bool.not(fd.fz.ok(cs, k, fz)), cof, c, g, na, xs, d, rs)
    case _ _:
      None{}

def fd.lc.q1(hit: Bool, +cof: Bool, +c: List<&2, U32>, a: T.Bt, +d: List<&2, U32>, +rs: List<&2, Mrch>, +fz: List<&2, Fz>, +tys: List<&2, T.BItem>) -> Maybe<&2, Lc>:
  match hit:
    case False{}:
      None{}
    case True{}:
      +g = Bool.pick(List<&2, U32>, cof, fd.lc.cut(c, 12n), fd.lc.cut(c, 5n))
      fd.lc.q2(fd.lc.fzb(fz, g), fd.dv.find(tys, g), cof, c, g, fd.spine(a), d, rs, fz)

# the call c(a) in the def cx is in, as a local cata when it is one to make
def fd.lc.q(+c: List<&2, U32>, a: T.Bt, cx: Lcx) -> Maybe<&2, Lc>:
  match cx:
    case Lcx{+d, +rs, +fz, +tys}:
      +cof = S.suffix(c, S.b(".cata.cofree"))
      fd.lc.q1(Bool.or(cof, S.suffix(c, S.b(".cata"))), cof, c, a, d, rs, fz, tys)

def fd.lc.last(xs: List<&2, T.Bt>) -> T.Bt:
  match xs:
    case Nil{}:
      fd.todo("fold:cata-shape")
    case h <> Nil{}:
      h
    case h <> t:
      fd.lc.last(t)

# a call, its arguments rewritten (ra): of its local cata's def at the value
def fd.lc.rw.at(m: Maybe<&2, Lc>, +x: List<&2, U32>, +ra: T.Bt) -> T.Bt:
  match m:
    case Some{Lc{n, g, cof, as, w, r, alg}}:
      T.tba.call(T.BtVar{n}, [fd.lc.last(fd.spine(ra))])
    case None{}:
      T.BtApp{T.BtVar{x}, ra}

# t with each local cata's call a call of its def
def fd.lc.rw(t: T.Bt, +cx: Lcx) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+x}, +a}:
      fd.lc.rw.at(fd.lc.q(x, a, cx), x, fd.lc.rw(a, cx))
    case T.BtApp{h, a}:
      T.BtApp{fd.lc.rw(h, cx), fd.lc.rw(a, cx)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.lc.rw(a, cx)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.lc.rw(b, cx)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.lc.rw(a, cx)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, fd.lc.rw(a, cx), fd.lc.rw(b, cx)}
    case T.BtSucc{a}:
      T.BtSucc{fd.lc.rw(a, cx)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.lc.rw(a, cx), ty}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.lc.rw(cs, cx)}
    case T.BtExpr{e}:
      T.BtExpr{fd.lc.rw(e, cx)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.lc.rw(e, cx), p, fd.lc.rw(b, cx)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, fd.lc.rw(v, cx), fd.lc.rw(b, cx)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.lc.rw(b, cx), fd.lc.rw(rest, cx)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.lc.rw(a, cx), fd.lc.rw(rest, cx)}
    case u:
      u

def fd.lc.put(m: Maybe<&2, Lc>, acc: List<&2, Lc>) -> List<&2, Lc>:
  match m:
    case Some{c}:
      c <> acc
    case None{}:
      acc

# the local catas t calls, as fd.lc.rw rewrites them
def fd.lc.calls(t: T.Bt, +cx: Lcx, acc: List<&2, Lc>) -> List<&2, Lc>:
  match t:
    case T.BtApp{T.BtVar{+x}, +a}:
      fd.lc.put(fd.lc.q(x, a, cx), fd.lc.calls(a, cx, acc))
    case T.BtApp{h, a}:
      fd.lc.calls(h, cx, fd.lc.calls(a, cx, acc))
    case T.BtTplArg{a}:
      fd.lc.calls(a, cx, acc)
    case T.BtLam{m, x, b}:
      fd.lc.calls(b, cx, acc)
    case T.BtCon{c, a}:
      fd.lc.calls(a, cx, acc)
    case T.BtEq{ty, a, b}:
      fd.lc.calls(a, cx, fd.lc.calls(b, cx, acc))
    case T.BtSucc{a}:
      fd.lc.calls(a, cx, acc)
    case T.BtAnn{a, ty}:
      fd.lc.calls(a, cx, acc)
    case T.BtMatch{xs, cs}:
      fd.lc.calls(cs, cx, acc)
    case T.BtExpr{e}:
      fd.lc.calls(e, cx, acc)
    case T.BtRw{e, p, b}:
      fd.lc.calls(e, cx, fd.lc.calls(b, cx, acc))
    case T.BtLet{x, v, b}:
      fd.lc.calls(v, cx, fd.lc.calls(b, cx, acc))
    case T.BtCase{p, b, rest}:
      fd.lc.calls(b, cx, fd.lc.calls(rest, cx, acc))
    case T.BtArgs{a, rest}:
      fd.lc.calls(a, cx, fd.lc.calls(rest, cx, acc))
    case u:
      acc

def fd.lm.n(m: Lm) -> List<&2, U32>:
  match m:
    case Lm{n, d, cof, alg, ps, src, dst, fz, tys}:
      n

def fd.lm.fz(m: Lm) -> List<&2, Fz>:
  match m:
    case Lm{n, d, cof, alg, ps, src, dst, fz, tys}:
      fz

def fd.lm.tys(m: Lm) -> List<&2, T.BItem>:
  match m:
    case Lm{n, d, cof, alg, ps, src, dst, fz, tys}:
      tys

def fd.lc.path(+p: List<&2, U32>, +j: Nat) -> List<&2, U32>:
  fd.cat3(p, S.b("_"), fd.nshow(j))

def fd.lc.hname(+m: Lm, +p: List<&2, U32>) -> List<&2, U32>:
  fd.cat3(fd.lm.n(m), S.b(".h"), p)

# a field's value: itself (copied), the cata's call (recursive), else its
# mapping def's call
def fd.lc.term(r: Fr, +z: List<&2, U32>, +m: Lm, +p: List<&2, U32>) -> T.Bt:
  match r:
    case FrCopy{}:
      T.BtVar{z}
    case FrRec{}:
      T.tba.call(T.BtVar{fd.lm.n(m)}, [T.BtVar{z}])
    case _:
      T.tba.call(T.BtVar{fd.lc.hname(m, p)}, [T.BtVar{z}])

def fd.lc.terms(rs: List<&2, Fr>, zs: List<&2, List<&2, U32>>, +m: Lm, +p: List<&2, U32>, +j: Nat) -> List<&2, T.Bt>:
  match rs zs:
    case r <> t z <> u:
      fd.lc.term(r, z, m, fd.lc.path(p, j)) <> fd.lc.terms(t, u, m, p, 1n+j)
    case _ _:
      Nil{}

# the algebra at a layer v
def fd.lc.alg(m: Lm, v: T.Bt) -> T.Bt:
  match m:
    case Lm{n, d, True{}, alg, ps, src, dst, fz, tys}:
      T.tba.call(alg, [T.BtCon{S.b("HsPrelude.CofreeF.CofreeF"), T.tba.args([T.BtVar{S.b("w0")}, v])}])
    case Lm{n, d, False{}, alg, ps, src, dst, fz, tys}:
      T.tba.call(alg, [v])

# the cases at the layer: each constructor's fields mapped, the algebra
# applied (top) or the constructor built (a functor inside it)
def fd.lc.cases(cs: List<&2, Fc>, +top: Bool, +m: Lm, +p: List<&2, U32>, +i: Nat) -> T.Bt:
  match cs:
    case Fc{+c, +rs} <> t:
      +zs = fd.cg.ys(List.length(&2, Fr, rs), 1n)
      +v = {T.BtCon{c, T.tba.args(fd.lc.terms(rs, zs, m, fd.lc.path(p, i), 0n))} : T.Bt}
      T.BtCase{T.tba.args([T.BtCon{c, T.tba.args(fd.cg.pvs(zs))}]), T.BtExpr{Bool.pick(T.Bt, top, fd.lc.alg(m, v), v)}, fd.lc.cases(t, top, m, p, 1n+i)}
    case Nil{}:
      T.BtCEnd{}

# the i-th type argument of a type named n
def fd.lc.arg(ty: T.Bt, s: String, i: Nat) -> T.Bt:
  match ty:
    case T.BtTyApp{+n, a}:
      Bool.pick(T.Bt, fd.is(n, s), Maybe.default(&2, T.Bt, List.get(&2, T.Bt, fd.spine(a), i), fd.todo("fold:cata-field-type")), fd.todo("fold:cata-field-type"))
    case _:
      fd.todo("fold:cata-field-type")

# B of Sigma<&2, &2, A, (_ => B)>
def fd.lc.lamb(t: T.Bt) -> T.Bt:
  match t:
    case T.BtLam{m, x, b}:
      b
    case _:
      fd.todo("fold:cata-field-type")

def fd.lc.sig2(ty: T.Bt) -> T.Bt:
  fd.lc.lamb(fd.lc.arg(ty, "Sigma", 3n))

def fd.lc.targs(ty: T.Bt) -> T.Bt:
  match ty:
    case T.BtTyApp{n, a}:
      a
    case _:
      T.BtANil{}

def fd.lc.mk(+m: Lm, +p: List<&2, U32>, +ty: T.Bt, b: T.Bt) -> T.BItem:
  match m:
    case Lm{+n, +d, cof, alg, +ps, +src, +dst, fz, tys}:
      T.BiDef{fd.cat3(n, S.b(".h"), p), [T.BParam{T.BmLive{}, S.b("v"), fd.dv.sub(ps, src, ty)}], fd.dv.sub(ps, dst, ty), b, [fd.cat(S.b("generated: lifted out of "), d)]}

def fd.lc.pv(s: String) -> T.Bt:
  T.BtPv{T.BmLive{}, S.b(s)}

def fd.lc.v(b: T.Bt) -> T.Bt:
  T.BtMatch{T.tba.args([T.BtVar{S.b("v")}]), b}

# the mapping def of a list, a Maybe, a pair
def fd.lc.list(+e: Fr, +m: Lm, +p: List<&2, U32>) -> T.Bt:
  fd.lc.v(T.BtCase{T.tba.args([fd.con0("Nil")]), T.BtExpr{fd.con0("Nil")}, T.BtCase{T.tba.args([T.BtCon{S.b("Con"), T.tba.args([fd.lc.pv("h"), fd.lc.pv("t")])}]), T.BtExpr{T.BtCon{S.b("Con"), T.tba.args([fd.lc.term(e, S.b("h"), m, fd.lc.path(p, 0n)), T.tba.call(T.BtVar{fd.lc.hname(m, p)}, [fd.v("t")])])}}, T.BtCEnd{}}})

def fd.lc.maybe(+e: Fr, +m: Lm, +p: List<&2, U32>) -> T.Bt:
  fd.lc.v(T.BtCase{T.tba.args([fd.con0("None")]), T.BtExpr{fd.con0("None")}, T.BtCase{T.tba.args([T.BtCon{S.b("Some"), T.tba.args([fd.lc.pv("a")])}]), T.BtExpr{T.BtCon{S.b("Some"), T.tba.args([fd.lc.term(e, S.b("a"), m, fd.lc.path(p, 0n))])}}, T.BtCEnd{}}})

def fd.lc.pair(+a: Fr, +b: Fr, +m: Lm, +p: List<&2, U32>) -> T.Bt:
  fd.lc.v(T.BtCase{T.tba.args([T.BtCon{S.b("Tuple"), T.tba.args([fd.lc.pv("a"), fd.lc.pv("b")])}]), T.BtExpr{T.BtCon{S.b("Tuple"), T.tba.args([fd.lc.term(a, S.b("a"), m, fd.lc.path(p, 0n)), fd.lc.term(b, S.b("b"), m, fd.lc.path(p, 1n))])}}, T.BtCEnd{}})

# the fields still to write for, of the constructors cs (their types tcs in
# the parameters hps, given hargs)
def fd.lc.fws(rs: List<&2, Fr>, fs: List<&2, T.BField>, +hps: List<&2, T.BParam>, +hargs: T.Bt, +p: List<&2, U32>, +j: Nat) -> List<&2, Lw>:
  match rs fs:
    case r <> t T.BField{x, ty} <> u:
      Lw{r, fd.dv.sub(hps, hargs, ty), fd.lc.path(p, j)} <> fd.lc.fws(t, u, hps, hargs, p, 1n+j)
    case _ _:
      Nil{}

def fd.lc.cws(cs: List<&2, Fc>, tcs: List<&2, T.BCtor>, +hps: List<&2, T.BParam>, +hargs: T.Bt, +p: List<&2, U32>, +i: Nat) -> List<&2, Lw>:
  match cs tcs:
    case Fc{c, rs} <> t T.BCtor{tc, fs} <> u:
      List.append(&2, Lw, fd.lc.fws(rs, fs, hps, hargs, fd.lc.path(p, i), 0n), fd.lc.cws(t, u, hps, hargs, p, 1n+i))
    case _ _:
      Nil{}

def fd.lc.in.ws(z: Maybe<&2, Fz>, t: Maybe<&2, T.BItem>, +hargs: T.Bt, +p: List<&2, U32>) -> List<&2, Lw>:
  match z t:
    case Some{Fz{k, b, tvs, cs}} Some{T.BiType{tn, hps, kd, tcs, td}}:
      fd.lc.cws(cs, tcs, hps, hargs, p, 0n)
    case _ _:
      Nil{}

def fd.lc.in.body(z: Maybe<&2, Fz>, +m: Lm, +p: List<&2, U32>) -> T.Bt:
  match z:
    case Some{Fz{k, b, tvs, cs}}:
      fd.lc.v(fd.lc.cases(cs, False{}, m, p, 0n))
    case None{}:
      T.BtExpr{fd.todo("fold:cata-functor")}

def fd.lc.fzbn(z: Maybe<&2, Fz>) -> List<&2, U32>:
  match z:
    case Some{Fz{k, b, tvs, cs}}:
      b
    case None{}:
      Nil{}

# the mapping defs of the fields still to write for (one each for a list,
# Maybe, pair or functor inside, its parts' after it)
def fd.lc.work(fuel: Nat, ws: List<&2, Lw>, +m: Lm) -> List<&2, T.BItem>:
  match fuel ws:
    case 0n _:
      Nil{}
    case 1n+f Nil{}:
      Nil{}
    case 1n+f Lw{FrCopy{}, ty, p} <> t:
      fd.lc.work(f, t, m)
    case 1n+f Lw{FrRec{}, ty, p} <> t:
      fd.lc.work(f, t, m)
    case 1n+f Lw{FrList{+e}, +ty, +p} <> t:
      fd.lc.mk(m, p, ty, fd.lc.list(e, m, p)) <> fd.lc.work(f, Lw{e, fd.lc.arg(ty, "List", 1n), fd.lc.path(p, 0n)} <> t, m)
    case 1n+f Lw{FrMaybe{+e}, +ty, +p} <> t:
      fd.lc.mk(m, p, ty, fd.lc.maybe(e, m, p)) <> fd.lc.work(f, Lw{e, fd.lc.arg(ty, "Maybe", 1n), fd.lc.path(p, 0n)} <> t, m)
    case 1n+f Lw{FrPair{+a, +b}, +ty, +p} <> t:
      fd.lc.mk(m, p, ty, fd.lc.pair(a, b, m, p)) <> fd.lc.work(f, Lw{a, fd.lc.arg(ty, "Sigma", 2n), fd.lc.path(p, 0n)} <> Lw{b, fd.lc.sig2(ty), fd.lc.path(p, 1n)} <> t, m)
    case 1n+f Lw{FrIn{+k}, +ty, +p} <> t:
      +z = fd.lc.fzk(fd.lm.fz(m), k)
      fd.lc.mk(m, p, ty, fd.lc.in.body(z, m, p)) <> fd.lc.work(f, List.append(&2, Lw, fd.lc.in.ws(z, fd.dv.find(fd.lm.tys(m), fd.lc.fzbn(z)), fd.lc.targs(ty), p), t), m)
    case 1n+f Lw{r, +ty, +p} <> t:
      fd.lc.mk(m, p, ty, T.BtExpr{fd.todo("fold:cata-field")}) <> fd.lc.work(f, t, m)

def fd.lc.gen(z: Maybe<&2, Fz>, ty: Maybe<&2, T.BItem>, +n: List<&2, U32>, +d: List<&2, U32>, +cof: Bool, +as: List<&2, T.Bt>, +w: T.Bt, +r: T.Bt, alg: T.Bt, +fz: List<&2, Fz>, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match z ty:
    case Some{Fz{k, +g, tvs, +cs}} Some{T.BiType{tn, +ps, kd, tcs, td}}:
      +lam = {T.BtLam{T.BmLive{}, fd.rv(), T.BtTyApp{g, T.tba.args(List.append(&2, T.Bt, as, T.BtVar{fd.rv()} <> Nil{}))}} : T.Bt}
      +xty = Bool.pick(T.Bt, cof, T.BtTyApp{S.b("HsPrelude.Cofree"), T.tba.args([lam, w])}, T.BtTyApp{S.b("HsPrelude.Fix"), T.tba.args([lam])})
      +m = {Lm{n, d, cof, alg, ps, T.tba.args(List.append(&2, T.Bt, as, [xty])), T.tba.args(List.append(&2, T.Bt, as, [r])), fz, tys} : Lm}
      +pat = Bool.pick(T.Bt, cof, T.BtCon{S.b("HsPrelude.Cofree.Cofree"), T.tba.args([fd.lc.pv("w0"), fd.lc.pv("y0")])}, T.BtCon{S.b("HsPrelude.Fix.Fix"), T.tba.args([fd.lc.pv("y0")])})
      +body = {T.BtMatch{T.tba.args([fd.v("x")]), T.BtCase{T.tba.args([pat]), T.BtMatch{T.tba.args([fd.v("y0")]), fd.lc.cases(cs, True{}, m, Nil{}, 0n)}, T.BtCEnd{}}} : T.Bt}
      T.BiDef{n, [T.BParam{T.BmLive{}, S.b("x"), xty}], r, body, [fd.cat(S.b("generated: lifted out of "), d), fd.cat(S.b("generated: the cata at "), g)]} <> fd.lc.work(4096n, fd.lc.cws(cs, tcs, Nil{}, T.BtANil{}, Nil{}, 0n), m)
    case _ _:
      Nil{}

def fd.lc.defs(c: Lc, cx: Lcx) -> List<&2, T.BItem>:
  match c cx:
    case Lc{+n, +g, cof, as, w, r, alg} Lcx{d, rs, +fz, +tys}:
      fd.lc.gen(fd.lc.fzb(fz, g), fd.dv.find(tys, g), n, d, cof, as, w, r, alg, fz, tys)

def fd.lc.gen1(dup: Bool, c: Lc, cx: Lcx, rest: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match dup:
    case True{}:
      rest
    case False{}:
      List.append(&2, T.BItem, fd.lc.defs(c, cx), rest)

# the defs of the local catas, each once
def fd.lc.gens(cs: List<&2, Lc>, +cx: Lcx, +seen: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match cs:
    case Nil{}:
      Nil{}
    case Lc{+n, g, cof, as, w, r, alg} <> t:
      fd.lc.gen1(S.mem(n, seen), Lc{n, g, cof, as, w, r, alg}, cx, fd.lc.gens(t, cx, n <> seen))

def fd.lc.item2(ok: Bool, +n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, +b: T.Bt, d: List<&2, List<&2, U32>>, +cx: Lcx) -> List<&2, T.BItem>:
  match ok:
    case False{}:
      [T.BiDef{n, ps, r, b, d}]
    case True{}:
      T.BiDef{n, ps, r, fd.lc.rw(b, cx), d} <> fd.lc.gens(fd.lc.calls(b, cx, Nil{}), cx, Nil{})

def fd.lc.item(it: T.BItem, +rs: List<&2, Mrch>, +fz: List<&2, Fz>, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match it:
    case T.BiDef{+n, +ps, r, b, d}:
      fd.lc.item2(Bool.and(Nat.is_eq(fd.fu.lead(ps), 0n), Bool.not(fd.mu.anytpl(ps))), n, ps, r, b, d, Lcx{n, rs, fz, tys})
    case other:
      [other]

def fd.lc.items(its: List<&2, T.BItem>, +rs: List<&2, Mrch>, +fz: List<&2, Fz>, +tys: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case h <> t:
      List.append(&2, T.BItem, fd.lc.item(h, rs, fz, tys), fd.lc.items(t, rs, fz, tys))

# the module's items with each local cata written (fz: the functors, own
# and the package's earlier ones; dt: the earlier modules' types)
def fd.lc.all(+its: List<&2, T.BItem>, +fz: List<&2, Fz>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +ns = fd.mu.names(its)
  +cg = fd.mu.cg(its, T.tba.set(ns, Map.new(&2, Bool)))
  +rs = fd.mu.rchs(ns, cg, fd.mu.edges(cg))
  fd.lc.items(its, rs, fz, List.append(&2, T.BItem, its, dt))

# Template copies ---------------------------------------------------------------
#
# A call of a module def at template arguments that name a def reaching
# back to the caller: Machine's transformNoDefer maps its own recursion
# over a layer, `fmap c x`, which the fold writes as the derived Functor's
# copy at a lambda, cfmap(~(eta_0 => c(eta_0)), x), c calling back the def
# the call is in. Once that group is merged (the fold's .mu, below) the
# template argument would hold the group's fuel, which Bend's templates
# refuse (they take only closed arguments). Such a call is a call of a
# copy of the def, D.tH (H a hash of the arguments), its template
# parameters replaced by the arguments: the copy names the group's defs
# itself, so it is one of the group, and the merge takes it in. Only
# arguments whose names are all the module's defs or qualified ones (no
# local of the caller) are copied in, at defs the merge could take (no
# type or template parameter of their own).

# a template copy: its name, the def, its template parameters' count, the
# arguments
type Ti is Data:
  Ti{n: List<&2, U32>, d: List<&2, U32>, k: Nat, as: List<&2, T.Bt>}

# what the rewrite of a def knows: its name, what each def reaches, the
# module's def names, the module's items
type Tix is Data:
  Tix{m: List<&2, U32>, rs: List<&2, Mrch>, ns: List<&2, List<&2, U32>>, its: List<&2, T.BItem>}

# whether a name is qualified (has a dot)
def fd.ti.dot(s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(U32.is_eq(c, 46), fd.ti.dot(t))

# the names t uses that it does not bind, in front of acc
def fd.ti.free(t: T.Bt, +bs: List<&2, List<&2, U32>>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtVar{+x}:
      T.tba.keep(S.mem(x, bs), x, acc)
    case T.BtApp{f, a}:
      fd.ti.free(f, bs, fd.ti.free(a, bs, acc))
    case T.BtTplArg{a}:
      fd.ti.free(a, bs, acc)
    case T.BtLam{m, x, b}:
      fd.ti.free(b, x <> bs, acc)
    case T.BtCon{c, a}:
      fd.ti.free(a, bs, acc)
    case T.BtEq{ty, a, b}:
      fd.ti.free(a, bs, fd.ti.free(b, bs, acc))
    case T.BtSucc{a}:
      fd.ti.free(a, bs, acc)
    case T.BtAnn{a, ty}:
      fd.ti.free(a, bs, acc)
    case T.BtMatch{xs, cs}:
      fd.ti.free(xs, bs, fd.ti.free(cs, bs, acc))
    case T.BtExpr{e}:
      fd.ti.free(e, bs, acc)
    case T.BtRw{e, p, b}:
      fd.ti.free(e, bs, fd.ti.free(b, bs, acc))
    case T.BtLet{x, v, b}:
      fd.ti.free(v, bs, fd.ti.free(b, x <> bs, acc))
    case T.BtCase{+p, b, rest}:
      fd.ti.free(b, List.append(&2, List<&2, U32>, T.tba.pvars(p, Nil{}), bs), fd.ti.free(rest, bs, acc))
    case T.BtArgs{a, rest}:
      fd.ti.free(a, bs, fd.ti.free(rest, bs, acc))
    case _:
      acc

# whether each name is the module's def or qualified
def fd.ti.globals(xs: List<&2, List<&2, U32>>, +ns: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.and(Bool.or(S.mem(x, ns), fd.ti.dot(x)), fd.ti.globals(t, ns))

# whether each of xs is a template argument
def fd.ti.tpls(xs: List<&2, T.Bt>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case T.BtTplArg{a} <> t:
      fd.ti.tpls(t)
    case _ <> t:
      False{}

def fd.ti.refs(xs: List<&2, T.Bt>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      T.tba.refs(h, fd.ti.refs(t, acc))

def fd.ti.frees(xs: List<&2, T.Bt>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      fd.ti.free(h, Nil{}, fd.ti.frees(t, acc))

def fd.ti.q3(ok: Bool, +x: List<&2, U32>, +k: Nat, +as: List<&2, T.Bt>) -> Maybe<&2, Ti>:
  match ok:
    case False{}:
      None{}
    case True{}:
      +txt = P.tpr.t(T.tba.call(T.BtVar{x}, as), P.TpLoose{}, 0n, Nil{})
      Some{Ti{fd.cat3(x, S.b(".t"), S.b(U32.show(fd.lc.hash(txt, 5381)))), x, k, fd.lc.untpls(as)}}

def fd.ti.q2(m: Maybe<&2, T.BItem>, +x: List<&2, U32>, +xs: List<&2, T.Bt>, +cx: Tix) -> Maybe<&2, Ti>:
  match m cx:
    case Some{T.BiDef{n, +ps, r, b, d}} Tix{c, +rs, +ns, its}:
      +k = fd.fu.lead(ps)
      +as = List.take(&2, T.Bt, xs, k)
      +more = Nat.is_gt(List.length(&2, T.BParam, ps), k)
      +back = fd.lc.back(fd.ti.refs(as, Nil{}), rs, c)
      fd.ti.q3(Bool.and(Bool.and(Nat.is_gt(k, 0n), more), Bool.and(Bool.and(Nat.is_gt(List.length(&2, T.Bt, xs), k), fd.ti.tpls(as)), Bool.and(back, fd.ti.globals(fd.ti.frees(as, Nil{}), ns)))), x, k, as)
    case _ _:
      None{}

# a call of x at the arguments a that is to be a template copy's
def fd.ti.q(+x: List<&2, U32>, +a: T.Bt, +cx: Tix) -> Maybe<&2, Ti>:
  match cx:
    case Tix{+c, rs, ns, +its}:
      Bool.pick(Maybe<&2, Ti>, S.eq(x, c), None{}, fd.ti.q2(fd.mu.get(its, x), x, fd.spine(a), Tix{c, rs, ns, its}))

def fd.ti.rw.at(m: Maybe<&2, Ti>, +x: List<&2, U32>, +ra: T.Bt) -> T.Bt:
  match m:
    case Some{Ti{n, d, k, as}}:
      T.tba.call(T.BtVar{n}, List.drop(&2, T.Bt, fd.spine(ra), k))
    case None{}:
      T.BtApp{T.BtVar{x}, ra}

# t with each such call a call of its copy
def fd.ti.rw(t: T.Bt, +cx: Tix) -> T.Bt:
  match t:
    case T.BtApp{T.BtVar{+x}, a}:
      +ra = fd.ti.rw(a, cx)
      fd.ti.rw.at(fd.ti.q(x, ra, cx), x, ra)
    case T.BtApp{h, a}:
      T.BtApp{fd.ti.rw(h, cx), fd.ti.rw(a, cx)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.ti.rw(a, cx)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.ti.rw(b, cx)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.ti.rw(a, cx)}
    case T.BtEq{ty, a, b}:
      T.BtEq{ty, fd.ti.rw(a, cx), fd.ti.rw(b, cx)}
    case T.BtSucc{a}:
      T.BtSucc{fd.ti.rw(a, cx)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.ti.rw(a, cx), ty}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.ti.rw(cs, cx)}
    case T.BtExpr{e}:
      T.BtExpr{fd.ti.rw(e, cx)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.ti.rw(e, cx), p, fd.ti.rw(b, cx)}
    case T.BtLet{x, v, b}:
      T.BtLet{x, fd.ti.rw(v, cx), fd.ti.rw(b, cx)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.ti.rw(b, cx), fd.ti.rw(rest, cx)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.ti.rw(a, cx), fd.ti.rw(rest, cx)}
    case u:
      u

def fd.ti.put(m: Maybe<&2, Ti>, acc: List<&2, Ti>) -> List<&2, Ti>:
  match m:
    case Some{c}:
      c <> acc
    case None{}:
      acc

# the template copies t calls, as fd.ti.rw rewrites them
def fd.ti.calls(t: T.Bt, +cx: Tix, acc: List<&2, Ti>) -> List<&2, Ti>:
  match t:
    case T.BtApp{T.BtVar{+x}, +a}:
      +ra = fd.ti.rw(a, cx)
      fd.ti.put(fd.ti.q(x, ra, cx), fd.ti.calls(a, cx, acc))
    case T.BtApp{h, a}:
      fd.ti.calls(h, cx, fd.ti.calls(a, cx, acc))
    case T.BtTplArg{a}:
      fd.ti.calls(a, cx, acc)
    case T.BtLam{m, x, b}:
      fd.ti.calls(b, cx, acc)
    case T.BtCon{c, a}:
      fd.ti.calls(a, cx, acc)
    case T.BtEq{ty, a, b}:
      fd.ti.calls(a, cx, fd.ti.calls(b, cx, acc))
    case T.BtSucc{a}:
      fd.ti.calls(a, cx, acc)
    case T.BtAnn{a, ty}:
      fd.ti.calls(a, cx, acc)
    case T.BtMatch{xs, cs}:
      fd.ti.calls(cs, cx, acc)
    case T.BtExpr{e}:
      fd.ti.calls(e, cx, acc)
    case T.BtRw{e, p, b}:
      fd.ti.calls(e, cx, fd.ti.calls(b, cx, acc))
    case T.BtLet{x, v, b}:
      fd.ti.calls(v, cx, fd.ti.calls(b, cx, acc))
    case T.BtCase{p, b, rest}:
      fd.ti.calls(b, cx, fd.ti.calls(rest, cx, acc))
    case T.BtArgs{a, rest}:
      fd.ti.calls(a, cx, fd.ti.calls(rest, cx, acc))
    case u:
      acc

# t with x replaced by v (closed: nothing it names is bound on the way)
def fd.ti.sub(t: T.Bt, +x: List<&2, U32>, +v: T.Bt) -> T.Bt:
  match t:
    case T.BtVar{+y}:
      Bool.pick(T.Bt, S.eq(y, x), v, T.BtVar{y})
    case T.BtApp{f, a}:
      T.BtApp{fd.ti.sub(f, x, v), fd.ti.sub(a, x, v)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.ti.sub(a, x, v)}
    case T.BtLam{m, +y, +b}:
      T.BtLam{m, y, Bool.pick(T.Bt, S.eq(y, x), b, fd.ti.sub(b, x, v))}
    case T.BtPi{m, +y, dep, a, +b}:
      T.BtPi{m, y, dep, fd.ti.sub(a, x, v), Bool.pick(T.Bt, S.eq(y, x), b, fd.ti.sub(b, x, v))}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.ti.sub(a, x, v)}
    case T.BtTyApp{n, a}:
      T.BtTyApp{n, fd.ti.sub(a, x, v)}
    case T.BtEq{ty, a, b}:
      T.BtEq{fd.ti.sub(ty, x, v), fd.ti.sub(a, x, v), fd.ti.sub(b, x, v)}
    case T.BtSucc{a}:
      T.BtSucc{fd.ti.sub(a, x, v)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.ti.sub(a, x, v), fd.ti.sub(ty, x, v)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{fd.ti.sub(xs, x, v), fd.ti.sub(cs, x, v)}
    case T.BtExpr{e}:
      T.BtExpr{fd.ti.sub(e, x, v)}
    case T.BtRw{e, p, b}:
      T.BtRw{fd.ti.sub(e, x, v), p, fd.ti.sub(b, x, v)}
    case T.BtLet{+y, a, +b}:
      T.BtLet{y, fd.ti.sub(a, x, v), Bool.pick(T.Bt, S.eq(y, x), b, fd.ti.sub(b, x, v))}
    case T.BtCase{+p, +b, rest}:
      T.BtCase{p, Bool.pick(T.Bt, S.mem(x, T.tba.pvars(p, Nil{})), b, fd.ti.sub(b, x, v)), fd.ti.sub(rest, x, v)}
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.ti.sub(a, x, v), fd.ti.sub(rest, x, v)}
    case u:
      u

# t with each of the parameters replaced by its argument
def fd.ti.subs(ps: List<&2, T.BParam>, as: List<&2, T.Bt>, t: T.Bt) -> T.Bt:
  match ps as:
    case T.BParam{m, x, ty} <> u a <> w:
      fd.ti.subs(u, w, fd.ti.sub(t, x, a))
    case _ _:
      t

def fd.ti.psubs(qs: List<&2, T.BParam>, +ps: List<&2, T.BParam>, +as: List<&2, T.Bt>) -> List<&2, T.BParam>:
  match qs:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      T.BParam{m, x, fd.ti.subs(ps, as, ty)} <> fd.ti.psubs(t, ps, as)

# a copy's def: the def's, its first k parameters replaced by the arguments
def fd.ti.def(m: Maybe<&2, T.BItem>, +n: List<&2, U32>, +k: Nat, +as: List<&2, T.Bt>) -> List<&2, T.BItem>:
  match m:
    case Some{T.BiDef{d, +ps, r, b, doc}}:
      +lead = List.take(&2, T.BParam, ps, k)
      [T.BiDef{n, fd.ti.psubs(List.drop(&2, T.BParam, ps, k), lead, as), fd.ti.subs(lead, as, r), fd.ti.subs(lead, as, b), [fd.cat(S.b("generated: a copy of "), d), S.b("at its template arguments (a group's def in them)")]}]
    case _:
      Nil{}

# the copies to write, each once, none the module has
def fd.ti.gens(cs: List<&2, Ti>, +its: List<&2, T.BItem>, +seen: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match cs:
    case Nil{}:
      Nil{}
    case Ti{+n, +d, +k, +as} <> t:
      +skip = Bool.or(S.mem(n, seen), Maybe.is_some(&2, T.BItem, fd.mu.get(its, n)))
      List.append(&2, T.BItem, Bool.pick(List<&2, T.BItem>, skip, Nil{}, fd.ti.def(fd.mu.get(its, d), n, k, as)), fd.ti.gens(t, its, n <> seen))

# the caller named in what the rewrite knows
def fd.ti.at(cx: Tix, +n: List<&2, U32>) -> Tix:
  match cx:
    case Tix{c, rs, ns, its}:
      Tix{n, rs, ns, its}

# a def the merge could take (no type or template parameter)
def fd.ti.ok(+ps: List<&2, T.BParam>) -> Bool:
  Bool.and(Nat.is_eq(fd.fu.lead(ps), 0n), Bool.not(fd.mu.anytpl(ps)))

def fd.ti.item2(ok: Bool, +n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, b: T.Bt, d: List<&2, List<&2, U32>>, +cx: Tix) -> T.BItem:
  match ok:
    case True{}:
      T.BiDef{n, ps, r, fd.ti.rw(b, fd.ti.at(cx, n)), d}
    case False{}:
      T.BiDef{n, ps, r, b, d}

def fd.ti.item(it: T.BItem, +cx: Tix) -> T.BItem:
  match it:
    case T.BiDef{n, +ps, r, b, d}:
      fd.ti.item2(fd.ti.ok(ps), n, ps, r, b, d, cx)
    case other:
      other

def fd.ti.callsof2(ok: Bool, +n: List<&2, U32>, b: T.Bt, +cx: Tix) -> List<&2, Ti>:
  match ok:
    case True{}:
      fd.ti.calls(b, fd.ti.at(cx, n), Nil{})
    case False{}:
      Nil{}

def fd.ti.callsof(it: T.BItem, +cx: Tix) -> List<&2, Ti>:
  match it:
    case T.BiDef{n, +ps, r, b, d}:
      fd.ti.callsof2(fd.ti.ok(ps), n, b, cx)
    case _:
      Nil{}

def fd.ti.items(its: List<&2, T.BItem>, +cx: Tix) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case h <> t:
      fd.ti.item(h, cx) <> fd.ti.items(t, cx)

def fd.ti.allcalls(its: List<&2, T.BItem>, +cx: Tix) -> List<&2, Ti>:
  match its:
    case Nil{}:
      Nil{}
    case h <> t:
      List.append(&2, Ti, fd.ti.callsof(h, cx), fd.ti.allcalls(t, cx))

# one round: the calls rewritten, the copies written
def fd.ti.round(+its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +ns = fd.mu.names(its)
  +cg = fd.mu.cg(its, T.tba.set(ns, Map.new(&2, Bool)))
  +rs = fd.mu.rchs(ns, cg, fd.mu.edges(cg))
  +cx = {Tix{Nil{}, rs, ns, its} : Tix}
  List.append(&2, T.BItem, fd.ti.items(its, cx), fd.ti.gens(fd.ti.allcalls(its, cx), its, Nil{}))

# the module's items with each such call a copy's (two rounds: a copy's own
# body may call another def so)
def fd.ti.all(+its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  fd.ti.round(fd.ti.round(its))

# a module's items as written, before the gate: local catas written, then
# groups merged (Law.bend's lw.module writes them so too)
# Partial functions -------------------------------------------------------------

# Haskell's partial functions are failure values (PLAN.md, "Partial
# functions"): prelude/HsPartial.bend's answer Either<&2, &2, String, A>,
# and so does every def that calls one or calls such a def (the partial
# defs, found to a fixed point over the module's items): its answer type
# becomes the Either, and in each answer (a body's, a case's, an if's
# thunk's) its partial calls are bound innermost first with
# hs.either.bind, the callee's answer type read off its signature with
# the call's type arguments put in. An answer that is a partial call is
# that call; an if (or a compare's three ways) with a partial branch is an
# if of Eithers, itself a partial call where it is not the answer; a let's
# partial calls are bound before it. A partial call under a lambda (a
# monad's continuation, a function argument) is out for now:
# fold:partial-in-lambda.

# a partial def: its name (as called), parameters and answer (inside the
# Either)
type Pt is Data:
  Pt{n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt}

# a partial call bound before an answer: its variable, answer and call
type Pb is Data:
  Pb{x: List<&2, U32>, a: T.Bt, c: T.Bt}

# what the walk gives: the term (its partial calls variables), the calls
# it binds in order, the next fresh number, whether a partial call is
# where it cannot be bound, whether the term is an Either already (an
# answer's partial call), and that call's answer type
type Pw is Data:
  Pw{t: T.Bt, bs: List<&2, Pb>, n: Nat, bad: Bool, e: Bool, a: T.Bt}

# the walk's modes: an expression (its partial calls bound to variables),
# an answer (a partial call or a partial if left as the Either), a body
# (statements, then an answer), a match's cases, an if's arguments (its
# type first), an if's arguments after its type (thunks' bodies answers)
type Ptm is Data:
  PtWm{}
  PtAm{}
  PtBm{}
  PtCm{}
  PtIm{}
  PtJm{}

def fd.pt.sty() -> T.Bt:
  fd.list(fd.v("Char"))

def fd.pt.ety(r: T.Bt) -> T.Bt:
  fd.either(fd.pt.sty(), r)

def fd.pt.doc() -> String:
  "partial: answers Either<String, A>, GHC's error as Inl{its message} (PLAN.md, Partial functions)"

# an argument as a type: a template's or an erased one's
def fd.pt.un(t: T.Bt) -> T.Bt:
  match t:
    case T.BtTplArg{a}:
      a
    case T.BtDead{a}:
      a
    case a:
      a

def fd.pt.list(a: T.Bt) -> List<&2, T.Bt>:
  match a:
    case T.BtArgs{h, t}:
      h <> fd.pt.list(t)
    case _:
      Nil{}

def fd.pt.nth(xs: List<&2, T.Bt>, n: Nat) -> T.Bt:
  match xs n:
    case h <> t 0n:
      fd.pt.un(h)
    case h <> t 1n+k:
      fd.pt.nth(t, k)
    case Nil{} _:
      T.BtType{}

# prelude/HsPartial.bend's defs and their answer at a call's arguments: 1
# the first type argument, 2 a list of it, 3 the second (Map's value)
type Pp is Data:
  Pp{n: String, k: Nat}

def fd.pt.pres() -> List<&2, Pp>:
  [Pp{"HsPrelude.HsList.error", 1n}, Pp{"HsPrelude.HsList.undefined", 1n}, Pp{"HsPrelude.HsList.head", 1n}, Pp{"HsPrelude.HsList.last", 1n}, Pp{"HsPrelude.HsList.index", 1n}, Pp{"HsPrelude.HsList.fromJust", 1n}, Pp{"HsPrelude.HsList.tail", 2n}, Pp{"HsPrelude.HsList.init", 2n}, Pp{"HsPrelude.HsMap.at", 3n}, Pp{"HsPrelude.HsList.maximum", 1n}, Pp{"HsPrelude.HsList.minimum", 1n}, Pp{"HsPrelude.HsList.maximumBy", 1n}, Pp{"HsPrelude.HsList.minimumBy", 1n}, Pp{"HsPrelude.HsList.foldr1", 1n}, Pp{"HsPrelude.HsList.foldl1", 1n}]

def fd.pt.pre.find(xs: List<&2, Pp>, +f: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Pp{s, k} <> t:
      Bool.pick(Nat, S.eq(S.b(s), f), k, fd.pt.pre.find(t, f))

def fd.pt.pre.ans(k: Nat, +xs: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match k:
    case 0n:
      None{}
    case 1n:
      Some{fd.pt.nth(xs, 0n)}
    case 2n:
      Some{fd.list(fd.pt.nth(xs, 0n))}
    case 3n+j:
      Some{fd.pt.nth(xs, 1n)}

def fd.pt.isty(m: T.BMode) -> Bool:
  match m:
    case T.BmErased{}:
      True{}
    case T.BmTpl{}:
      True{}
    case _:
      False{}

def fd.pt.tv(+x: List<&2, U32>) -> List<&2, U32>:
  fd.cat(S.b("pt_tv_"), x)

# a partial def's answer at a call: its type parameters (erased or
# templates) renamed apart, then the call's type arguments put in
def fd.pt.ren(ps: List<&2, T.BParam>, +r: T.Bt) -> T.Bt:
  match ps:
    case T.BParam{m, +x, ty} <> t:
      fd.pt.ren(t, Bool.pick(T.Bt, fd.pt.isty(m), T.tba.subst(r, x, T.BtVar{fd.pt.tv(x)}), r))
    case Nil{}:
      r

def fd.pt.put(ps: List<&2, T.BParam>, xs: List<&2, T.Bt>, +r: T.Bt) -> T.Bt:
  match ps xs:
    case T.BParam{m, x, ty} <> pt a <> xt:
      fd.pt.put(pt, xt, Bool.pick(T.Bt, fd.pt.isty(m), T.tba.subst(r, fd.pt.tv(x), fd.pt.un(a)), r))
    case _ _:
      r

def fd.pt.own(ks: List<&2, Pt>, +f: List<&2, U32>, +xs: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  match ks:
    case Nil{}:
      None{}
    case Pt{n, +ps, r} <> t:
      Bool.pick(Maybe<&2, T.Bt>, S.eq(n, f), Some{fd.pt.put(ps, xs, fd.pt.ren(ps, r))}, fd.pt.own(t, f, xs))

def fd.pt.ans.of(+ks: List<&2, Pt>, +f: List<&2, U32>, +xs: List<&2, T.Bt>) -> Maybe<&2, T.Bt>:
  +k = fd.pt.pre.find(fd.pt.pres(), f)
  Bool.pick(Maybe<&2, T.Bt>, Nat.is_gt(k, 0n), fd.pt.pre.ans(k, xs), fd.pt.own(ks, f, xs))

def fd.pt.isown(ks: List<&2, Pt>, +f: List<&2, U32>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Pt{n, ps, r} <> t:
      Bool.or(S.eq(n, f), fd.pt.isown(t, f))

def fd.pt.is(+ks: List<&2, Pt>, +f: List<&2, U32>) -> Bool:
  Bool.or(Nat.is_gt(fd.pt.pre.find(fd.pt.pres(), f), 0n), fd.pt.isown(ks, f))

def fd.pt.any(+ks: List<&2, Pt>, rs: List<&2, List<&2, U32>>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(fd.pt.is(ks, r), fd.pt.any(ks, t))

# whether a term calls (or names) a partial def
def fd.pt.has(+ks: List<&2, Pt>, t: T.Bt) -> Bool:
  fd.pt.any(ks, T.tba.refs(t, Nil{}))

# the defs whose thunks are answers: an if, a compare's three ways
def fd.pt.br(+f: List<&2, U32>) -> Bool:
  Bool.or(fd.is(f, "Bool.if"), Bool.or(fd.is(f, "HsBool.if"), Bool.or(fd.is(f, "HsPrelude.HsBool.if"), Bool.or(fd.is(f, "HsCmp.on"), fd.is(f, "HsPrelude.HsCmp.on")))))

# an if with a partial argument (else its arguments are walked as any)
def fd.pt.brh(br: Bool, +ks: List<&2, Pt>, a: T.Bt) -> Bool:
  match br:
    case True{}:
      fd.pt.has(ks, a)
    case False{}:
      False{}

def fd.pt.amode(brh: Bool) -> Ptm:
  match brh:
    case True{}:
      PtIm{}
    case False{}:
      PtWm{}

def fd.pt.n(w: Pw) -> Nat:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      n

def fd.pt.inr(e: Bool, t: T.Bt) -> T.Bt:
  match e:
    case True{}:
      t
    case False{}:
      T.BtCon{S.b("Inr"), T.tba.args([t])}

# the binds in front of an answer z (an Either at the answer type ty)
def fd.pt.binds(bs: List<&2, Pb>, z: T.Bt, +ty: T.Bt) -> T.Bt:
  match bs:
    case Nil{}:
      z
    case Pb{+x, a, c} <> t:
      +rest = fd.pt.binds(t, z, ty)
      fd.callS("hs.either.bind", [fd.pt.sty(), a, ty, c, T.BtLam{fd.mode(fd.uses(rest, x)), x, rest}])

# an answer's Either: its binds, then the answer (a total one in Inr)
def fd.pt.fin(w: Pw, +ty: T.Bt) -> T.Bt:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      fd.pt.binds(bs, fd.pt.inr(e, t), ty)

def fd.pt.bad(w: Pw) -> Bool:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      bad

# a call of f, its arguments walked: the answer itself (an answer's), bound
# to a fresh variable (an expression's), or as it was (f total)
def fd.pt.app.go(at: Maybe<&2, T.Bt>, m: Ptm, +f: T.Bt, a: T.Bt, bs: List<&2, Pb>, +k: Nat, bad: Bool, lam: Bool) -> Pw:
  match at m lam:
    case None{} _ _:
      Pw{T.BtApp{f, a}, bs, k, bad, False{}, T.BtType{}}
    case Some{r} PtAm{} _:
      Pw{T.BtApp{f, a}, bs, k, bad, True{}, r}
    case Some{r} _ True{}:
      Pw{T.BtApp{f, a}, bs, k, True{}, False{}, T.BtType{}}
    case Some{r} _ False{}:
      +x = fd.cat(S.b("pt_"), fd.nshow(k))
      Pw{T.BtVar{x}, List.append(&2, Pb, bs, [Pb{x, r, T.BtApp{f, a}}]), Nat.add(k, 1n), bad, False{}, T.BtType{}}

def fd.pt.app.ty(brh: Bool, +ks: List<&2, Pt>, +f: List<&2, U32>, +a: T.Bt, at: T.Bt) -> Maybe<&2, T.Bt>:
  match brh:
    case True{}:
      Some{at}
    case False{}:
      fd.pt.ans.of(ks, f, fd.pt.list(a))

def fd.pt.t(w: Pw) -> T.Bt:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      t

def fd.pt.e(w: Pw) -> Bool:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      e

def fd.pt.a(w: Pw) -> T.Bt:
  match w:
    case Pw{t, bs, n, bad, e, a}:
      a

# a lambda applied at once ((x0 => l1(x0))(x), a comprehension's copy):
# its body, walked as an answer when it holds a partial call, is then that
# call (its binds inside the lambda), the whole a partial call; a body
# whose answer type is unknown (not itself a partial call) is out
def fd.pt.rmode(hb: Bool) -> Ptm:
  match hb:
    case True{}:
      PtAm{}
    case False{}:
      PtWm{}

def fd.pt.redex.at(hb: Bool, +wb: Pw) -> Maybe<&2, T.Bt>:
  match hb:
    case True{}:
      Bool.pick(Maybe<&2, T.Bt>, fd.pt.e(wb), Some{fd.pt.a(wb)}, None{})
    case False{}:
      None{}

def fd.pt.redex.body(hb: Bool, +wb: Pw) -> T.Bt:
  match hb:
    case True{}:
      fd.pt.fin(wb, fd.pt.a(wb))
    case False{}:
      fd.pt.t(wb)

def fd.pt.redex.bad(hb: Bool, +wb: Pw) -> Bool:
  match hb:
    case True{}:
      Bool.or(fd.pt.bad(wb), Bool.not(fd.pt.e(wb)))
    case False{}:
      fd.pt.bad(wb)

def fd.pt.app(+ks: List<&2, Pt>, m: Ptm, +f: List<&2, U32>, w: Pw, lam: Bool, brh: Bool) -> Pw:
  match w:
    case Pw{+a, bs, k, bad, e, at}:
      fd.pt.app.go(fd.pt.app.ty(brh, ks, f, a, at), m, T.BtVar{f}, a, bs, k, bad, lam)

def fd.pt.mk.app(w: Pw, v: Pw) -> Pw:
  match w v:
    case Pw{a, bs, k, bad, e, at} Pw{b, bs2, k2, bad2, e2, at2}:
      Pw{T.BtApp{a, b}, List.append(&2, Pb, bs, bs2), k2, Bool.or(bad, bad2), False{}, T.BtType{}}

def fd.pt.mk.args(w: Pw, v: Pw) -> Pw:
  match w v:
    case Pw{a, bs, k, bad, e, at} Pw{b, bs2, k2, bad2, e2, at2}:
      Pw{T.BtArgs{a, b}, List.append(&2, Pb, bs, bs2), k2, Bool.or(bad, bad2), False{}, T.BtType{}}

def fd.pt.mk.case(p: T.Bt, w: Pw, v: Pw) -> Pw:
  match w v:
    case Pw{a, bs, k, bad, e, at} Pw{b, bs2, k2, bad2, e2, at2}:
      Pw{T.BtCase{p, a, b}, Nil{}, k2, Bool.or(bad, bad2), False{}, T.BtType{}}

def fd.pt.redex(at: Maybe<&2, T.Bt>, m: Ptm, +hb: Bool, lm: T.BMode, x: List<&2, U32>, +wb: Pw, wa: Pw, lam: Bool) -> Pw:
  match wa:
    case Pw{a, bs, k, bad, e, at2}:
      fd.pt.app.go(at, m, T.BtLam{lm, x, fd.pt.redex.body(hb, wb)}, a, bs, k, Bool.or(bad, fd.pt.redex.bad(hb, wb)), lam)

# an if's thunk: its body an answer, the arguments after it
def fd.pt.mk.thunk(lm: T.BMode, x: List<&2, U32>, +w: Pw, +ty: T.Bt, v: Pw) -> Pw:
  match v:
    case Pw{b, bs2, k2, bad2, e2, at2}:
      Pw{T.BtArgs{T.BtLam{lm, x, fd.pt.fin(w, ty)}, b}, bs2, k2, Bool.or(fd.pt.bad(w), bad2), False{}, T.BtType{}}

def fd.pt.mk.if(+t0: T.Bt, w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtArgs{fd.pt.ety(t0), a}, bs, k, bad, False{}, t0}

def fd.pt.mk.match(xs: T.Bt, w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtMatch{xs, a}, Nil{}, k, bad, False{}, T.BtType{}}

def fd.pt.mk.rw(x: T.Bt, p: T.Bt, w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtRw{x, p, a}, Nil{}, k, bad, False{}, T.BtType{}}

def fd.pt.mk.expr(+w: Pw, +ty: T.Bt) -> Pw:
  Pw{T.BtExpr{fd.pt.fin(w, ty)}, Nil{}, fd.pt.n(w), fd.pt.bad(w), False{}, T.BtType{}}

# under a lambda nothing is bound (a partial call there made bad)
def fd.pt.mk.lam(lm: T.BMode, x: List<&2, U32>, w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtLam{lm, x, a}, Nil{}, k, bad, False{}, T.BtType{}}

def fd.pt.mk.tpl(w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtTplArg{a}, Nil{}, k, bad, False{}, T.BtType{}}

def fd.pt.mk.con(c: List<&2, U32>, w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtCon{c, a}, bs, k, bad, False{}, T.BtType{}}

def fd.pt.mk.ann(w: Pw, ty: T.Bt) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtAnn{a, ty}, bs, k, bad, False{}, T.BtType{}}

def fd.pt.mk.succ(w: Pw) -> Pw:
  match w:
    case Pw{a, bs, k, bad, e, at}:
      Pw{T.BtSucc{a}, bs, k, bad, False{}, T.BtType{}}

# a let: its value's partial calls bound before it (the let then inside
# the last bind's lambda, a parenthesized body)
def fd.pt.let.of(+x: List<&2, U32>, v: T.Bt, bs: List<&2, Pb>, b: T.Bt, +ty: T.Bt) -> T.Bt:
  match bs:
    case Nil{}:
      T.BtLet{x, v, b}
    case +h <> t:
      T.BtExpr{fd.pt.binds(h <> t, T.BtLet{x, v, b}, ty)}

def fd.pt.let(+x: List<&2, U32>, w: Pw, v: Pw, +ty: T.Bt) -> Pw:
  match w v:
    case Pw{a, bs, k, bad, e, at} Pw{b, bs2, k2, bad2, e2, at2}:
      Pw{fd.pt.let.of(x, a, bs, b, ty), Nil{}, k2, Bool.or(bad, bad2), False{}, T.BtType{}}

# the walk (one def: Bend takes no mutual recursion), each call at a part
# of t; ty the answer's type (an if's type in its arguments)
def fd.pt.go(+ks: List<&2, Pt>, t: T.Bt, m: Ptm, +ty: T.Bt, +n: Nat, +lam: Bool) -> Pw:
  match t m:
    case T.BtMatch{xs, cs} PtBm{}:
      fd.pt.mk.match(xs, fd.pt.go(ks, cs, PtCm{}, ty, n, lam))
    case T.BtLet{+x, v, b} PtBm{}:
      +wv = fd.pt.go(ks, v, PtWm{}, ty, n, lam)
      fd.pt.let(x, wv, fd.pt.go(ks, b, PtBm{}, ty, fd.pt.n(wv), lam), ty)
    case T.BtRw{e, p, b} PtBm{}:
      fd.pt.mk.rw(e, p, fd.pt.go(ks, b, PtBm{}, ty, n, lam))
    case T.BtExpr{e} PtBm{}:
      fd.pt.mk.expr(fd.pt.go(ks, e, PtAm{}, ty, n, lam), ty)
    case +u PtBm{}:
      Pw{u, Nil{}, n, fd.pt.has(ks, u), False{}, T.BtType{}}
    case T.BtCase{p, b, rest} PtCm{}:
      +wb = fd.pt.go(ks, b, PtBm{}, ty, n, lam)
      fd.pt.mk.case(p, wb, fd.pt.go(ks, rest, PtCm{}, ty, fd.pt.n(wb), lam))
    case u PtCm{}:
      Pw{u, Nil{}, n, False{}, False{}, T.BtType{}}
    case T.BtArgs{+t0, rest} PtIm{}:
      fd.pt.mk.if(t0, fd.pt.go(ks, rest, PtJm{}, t0, n, lam))
    case u PtIm{}:
      Pw{u, Nil{}, n, True{}, False{}, T.BtType{}}
    case T.BtArgs{T.BtLam{lm, x, b}, rest} PtJm{}:
      +wb = fd.pt.go(ks, b, PtAm{}, ty, n, False{})
      fd.pt.mk.thunk(lm, x, wb, ty, fd.pt.go(ks, rest, PtJm{}, ty, fd.pt.n(wb), lam))
    case T.BtArgs{h, rest} PtJm{}:
      +wh = fd.pt.go(ks, h, PtWm{}, ty, n, lam)
      fd.pt.mk.args(wh, fd.pt.go(ks, rest, PtJm{}, ty, fd.pt.n(wh), lam))
    case u PtJm{}:
      Pw{u, Nil{}, n, False{}, False{}, T.BtType{}}
    case T.BtApp{T.BtVar{+f}, +a} mw:
      +brh = fd.pt.brh(fd.pt.br(f), ks, a)
      fd.pt.app(ks, mw, f, fd.pt.go(ks, a, fd.pt.amode(brh), ty, n, lam), lam, brh)
    case T.BtApp{T.BtLam{lm, x, +b}, a} mw:
      +hb = fd.pt.has(ks, b)
      +wb = fd.pt.go(ks, b, fd.pt.rmode(hb), ty, n, Bool.not(hb))
      fd.pt.redex(fd.pt.redex.at(hb, wb), mw, hb, lm, x, wb, fd.pt.go(ks, a, PtWm{}, ty, fd.pt.n(wb), lam), lam)
    case T.BtApp{f, a} _:
      +wf = fd.pt.go(ks, f, PtWm{}, ty, n, lam)
      fd.pt.mk.app(wf, fd.pt.go(ks, a, PtWm{}, ty, fd.pt.n(wf), lam))
    case T.BtArgs{h, rest} _:
      +wh = fd.pt.go(ks, h, PtWm{}, ty, n, lam)
      fd.pt.mk.args(wh, fd.pt.go(ks, rest, PtWm{}, ty, fd.pt.n(wh), lam))
    case T.BtLam{lm, x, b} _:
      fd.pt.mk.lam(lm, x, fd.pt.go(ks, b, PtWm{}, ty, n, True{}))
    case T.BtCon{c, a} _:
      fd.pt.mk.con(c, fd.pt.go(ks, a, PtWm{}, ty, n, lam))
    case T.BtTplArg{a} _:
      fd.pt.mk.tpl(fd.pt.go(ks, a, PtWm{}, ty, n, True{}))
    case T.BtAnn{a, at} _:
      fd.pt.mk.ann(fd.pt.go(ks, a, PtWm{}, ty, n, lam), at)
    case T.BtSucc{a} _:
      fd.pt.mk.succ(fd.pt.go(ks, a, PtWm{}, ty, n, lam))
    case T.BtVar{+x} _:
      Pw{T.BtVar{x}, Nil{}, n, fd.pt.is(ks, x), False{}, T.BtType{}}
    case +u _:
      Pw{u, Nil{}, n, fd.pt.has(ks, u), False{}, T.BtType{}}

# a def and the names its body mentions
type Pr is Data:
  Pr{n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, rs: List<&2, List<&2, U32>>}

def fd.pt.prs(its: List<&2, T.BItem>) -> List<&2, Pr>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, b, d} <> t:
      Pr{n, ps, r, T.tba.refs(b, Nil{})} <> fd.pt.prs(t)
    case _ <> t:
      fd.pt.prs(t)

def fd.pt.add(c: Bool, n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, ks: List<&2, Pt>) -> List<&2, Pt>:
  match c:
    case True{}:
      Pt{n, ps, r} <> ks
    case False{}:
      ks

# one round: the defs that call a partial one join them
def fd.pt.round(rs: List<&2, Pr>, +ks: List<&2, Pt>) -> List<&2, Pt>:
  match rs:
    case Nil{}:
      ks
    case Pr{+n, ps, r, refs} <> t:
      fd.pt.round(t, fd.pt.add(Bool.and(Bool.not(fd.pt.isown(ks, n)), fd.pt.any(ks, refs)), n, ps, r, ks))

# rounds until none joins (fuel: the number of defs)
def fd.pt.fix(fuel: Nat, done: Bool, +rs: List<&2, Pr>, +ks: List<&2, Pt>) -> List<&2, Pt>:
  match fuel done:
    case _ True{}:
      ks
    case 0n _:
      ks
    case 1n+k False{}:
      +ks2 = fd.pt.round(rs, ks)
      fd.pt.fix(k, Nat.is_eq(List.length(&2, Pt, ks2), List.length(&2, Pt, ks)), rs, ks2)

def fd.pt.def(n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, w: Pw, d: List<&2, List<&2, U32>>) -> T.BItem:
  match w:
    case Pw{b, bs, k, bad, e, at}:
      T.BiDef{n, ps, fd.pt.ety(r), Bool.pick(T.Bt, bad, T.BtExpr{fd.todo("fold:partial-in-lambda")}, b), List.append(&2, List<&2, U32>, d, [S.b(fd.pt.doc())])}

def fd.pt.item(p: Bool, +ks: List<&2, Pt>, n: List<&2, U32>, ps: List<&2, T.BParam>, +r: T.Bt, b: T.Bt, d: List<&2, List<&2, U32>>) -> T.BItem:
  match p:
    case True{}:
      fd.pt.def(n, ps, r, fd.pt.go(ks, b, PtBm{}, r, 0n, False{}), d)
    case False{}:
      T.BiDef{n, ps, r, b, d}

def fd.pt.items(its: List<&2, T.BItem>, +ks: List<&2, Pt>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{+n, ps, r, b, d} <> t:
      fd.pt.item(fd.pt.isown(ks, n), ks, n, ps, r, b, d) <> fd.pt.items(t, ks)
    case h <> t:
      h <> fd.pt.items(t, ks)

# the earlier modules' partial defs (fd.dt.export: a def's signature with
# fd.pt.doc's line)
def fd.pt.imported(dt: List<&2, T.BItem>) -> List<&2, Pt>:
  match dt:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, b, d} <> t:
      Pt{n, ps, r} <> fd.pt.imported(t)
    case _ <> t:
      fd.pt.imported(t)

def fd.pt.all(+its: List<&2, T.BItem>, +dt: List<&2, T.BItem>) -> List<&2, T.BItem>:
  +rs = fd.pt.prs(its)
  fd.pt.items(its, fd.pt.fix(List.length(&2, Pr, rs), False{}, rs, fd.pt.imported(dt)))

def fd.mod.its(+gs: List<&2, Got>, +xs: List<&2, X.Sx>, +m: List<&2, U32>, +env: Env, +px: Px) -> List<&2, T.BItem>:
  fd.mu.all(fd.ti.all(fd.pt.all(fd.lc.all(fd.eta.all(fd.got.items(gs)), List.append(&2, Fz, fd.fzs(xs, m), fd.ix.fzs(fd.env.ix(env))), fd.px.dt(px)), fd.px.dt(px))), fd.px.dt(px))

# one round's verdict: done when Bend accepts the file
def fd.gate.step(g: Gs, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +out: List<&2, U32>, +dt: List<&2, T.BItem>) -> Gs:
  match g:
    case Gs{its, o, True{}}:
      Gs{its, o, True{}}
    case Gs{+its, +o, False{}}:
      +ls = S.split(out, 10)
      +who = fd.gate.who2(fd.tpl.loc(ls), ls, fd.render(file, m, ims, its), its)
      +why = fd.errwhy(ls)
      Bool.pick(Gs, S.prefix(out, S.b("ALL PROOFS CHECK")), Gs{its, o, True{}}, fd.gate.fix(fd.fu.can(who, why, its, dt), who, its, o, fd.cat(S.b("check:"), why), dt))

# one round's check: write the file and run bend on it (nothing once done)
def fd.gate.io(g: Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>) -> IO(S.Out):
  match g:
    case Gs{its, o, True{}}:
      IO.pure(S.Out, S.Out{0, S.b("ALL PROOFS CHECK")})
    case Gs{its, o, False{}}:
      do IO<S.Out>:
        S.write(path, fd.render(file, m, ims, its))
        S.run(".", Nil{}, 300, bend, [path, "--check-only"], Nil{})

# the gate: check, drop the item the error is in (and what uses it), and
# check again, until Bend accepts the file or nothing is left (each round's
# answer from bend, its first lines, is appended to PATH.log)
def fd.gate(fuel: Nat, g: Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +dt: List<&2, T.BItem>) -> IO(Gs):
  match fuel:
    case 0n:
      IO.pure(Gs, g)
    case 1n+p:
      +g1 = g
      do IO<Gs>:
        +o : S.Out <- fd.gate.io(g1, bend, path, file, m, ims)
        S.add(path ++ ".log", S.append(S.lines.take(S.Out.text(o), 12n), [10, 10]))
        fd.gate(p, fd.gate.step(g1, file, m, ims, S.Out.text(o), dt), bend, path, file, m, ims, dt)

# The module -------------------------------------------------------------------------

def fd.got.outs(gs: List<&2, Got>) -> List<&2, Dr>:
  match gs:
    case GotOut{n, w} <> t:
      Dr{fd.oname(n), w} <> fd.got.outs(t)
    case _ <> t:
      fd.got.outs(t)
    case Nil{}:
      Nil{}

# whether a def is one cata wrote itself (a functor's cata), not a binding
def fd.isgen(d: List<&2, List<&2, U32>>) -> Bool:
  match d:
    case h <> t:
      S.prefix(h, S.b("generated"))
    case Nil{}:
      False{}

def fd.ledger.ok(+file: List<&2, U32>, its: List<&2, T.BItem>) -> List<&2, U32>:
  match its:
    case T.BiDef{n, ps, r, b, d} <> t:
      fd.cat(S.join([file, n, fd.bpick(fd.isgen(d), S.b("ok-gen"), S.b("ok")), Nil{}], 9), 10 <> fd.ledger.ok(file, t))
    case T.BiType{n, ps, k, cs, d} <> t:
      fd.cat(S.join([file, n, fd.bpick(fd.isgen(d), S.b("ok-gen"), S.b("ok-type")), Nil{}], 9), 10 <> fd.ledger.ok(file, t))
    case _ <> t:
      fd.ledger.ok(file, t)
    case Nil{}:
      Nil{}

def fd.ledger.out(+file: List<&2, U32>, ds: List<&2, Dr>) -> List<&2, U32>:
  match ds:
    case Dr{n, w} <> t:
      fd.cat(S.join([file, n, S.b("out"), w], 9), 10 <> fd.ledger.out(file, t))
    case Nil{}:
      Nil{}

def fd.ledger(+file: List<&2, U32>, keep: List<&2, T.BItem>, out: List<&2, Dr>) -> List<&2, U32>:
  List.append(&2, U32, fd.ledger.ok(file, keep), fd.ledger.out(file, out))

def fd.hasdef(its: List<&2, T.BItem>) -> Bool:
  match its:
    case T.BiDef{n, ps, r, b, d} <> t:
      True{}
    case _ <> t:
      fd.hasdef(t)
    case Nil{}:
      False{}

def fd.module.write(has: Bool, +path: String, text: List<&2, U32>) -> IO(Unit):
  match has:
    case True{}:
      S.write(path, text)
    case False{}:
      IO.pure(Unit, Unit{})

# whether the module's file is written: it has a def, or (in a package,
# where later modules may import its types) any item
def fd.wrote(+pkg: Bool, +its: List<&2, T.BItem>) -> Bool:
  Bool.or(fd.hasdef(its), Bool.and(pkg, Bool.not(List.is_empty(&2, T.BItem, its))))

def fd.module.fin(+out: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +path: String, +pkg: Bool, g: Gs) -> IO(Unit):
  match g:
    case Gs{+k, o, d}:
      do IO<Unit>:
        fd.module.write(fd.wrote(pkg, k), path, fd.render(file, m, ims, k))
        S.add(out ++ "/ledger.tsv", fd.ledger(file, k, o))

def fd.env0(m: List<&2, U32>, cs: List<&2, Ctr>, ds: List<&2, Df>, px: Px) -> Env:
  Env{m, cs, ds, None{}, Nil{}, Nil{}, Nil{}, px, Nil{}}

# (synonym NAME (TV...) TYPE SPAN), folded with the synonyms of the round
# before; as many rounds as there are synonyms, so one that names another
# declared after it is still expanded
def fd.syns.if(d: Bool, +x: X.Sx, +env: Env, acc: List<&2, Syn>) -> List<&2, Syn>:
  match d:
    case True{}:
      Syn{V.sv.str(x, 1n), fd.tvs(V.sv.at(x, 2n)), fd.rt(fd.go(V.sv.at(x, 3n), fd.k(RoTy{}, V.sv.at(x, 3n)), env))} <> acc
    case False{}:
      acc

def fd.syns.round(xs: List<&2, X.Sx>, +env: Env) -> List<&2, Syn>:
  match xs:
    case +h <> t:
      fd.syns.if(V.sv.is(V.sv.hd(h), "synonym"), h, env, fd.syns.round(t, env))
    case Nil{}:
      Nil{}

# the synonyms of the package's earlier modules, by key, folded here (their
# types are this module's imports)
def fd.isyns(ys: List<&2, Sy>, +env: Env) -> List<&2, Syn>:
  match ys:
    case Sy{+k, +x} <> t:
      Syn{k, fd.tvs(V.sv.at(x, 2n)), fd.rt(fd.go(V.sv.at(x, 3n), fd.k(RoTy{}, V.sv.at(x, 3n)), env))} <> fd.isyns(t, env)
    case Nil{}:
      Nil{}

def fd.syns(fuel: Nat, +xs: List<&2, X.Sx>, +env: Env) -> Env:
  match fuel:
    case 0n:
      env
    case 1n+p:
      fd.syns(p, xs, fd.withsyn(env, List.append(&2, Syn, fd.syns.round(xs, env), fd.isyns(fd.px.sy(fd.env.px(env)), env))))

def fd.nsyn(xs: List<&2, X.Sx>) -> Nat:
  match xs:
    case h <> t:
      Nat.add(Bool.pick(Nat, V.sv.is(V.sv.hd(h), "synonym"), 1n, 0n), fd.nsyn(t))
    case Nil{}:
      0n

# Templates ---------------------------------------------------------------------

# A function parameter used twice must be a template (~f), and so must
# every parameter a template argument names: a template is known when the
# program is compiled, so its argument names no local but templates (a
# type variable a template's type names is one too). The module's defs take
# ~ at their template positions and their calls pass it there; the flags
# settle by rounds, at most as many as there are items. A template argument
# that names a pattern's, a lambda's or a let's variable is a closure, and
# its def is out (fold:closure-argument).

# the names a body binds: patterns', lambdas', lets'
def fd.binds(t: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtLet{x, v, b}:
      fd.binds(v, fd.unplus(x) <> fd.binds(b, acc))
    case T.BtLam{m, x, b}:
      x <> fd.binds(b, acc)
    case T.BtCase{p, b, rest}:
      T.tba.pvars(p, fd.binds(b, fd.binds(rest, acc)))
    case T.BtRw{e, p, b}:
      fd.binds(e, fd.binds(p, fd.binds(b, acc)))
    case T.BtDead{a}:
      fd.binds(a, acc)
    case T.BtApp{f, a}:
      fd.binds(f, fd.binds(a, acc))
    case T.BtTplArg{a}:
      fd.binds(a, acc)
    case T.BtCon{c, a}:
      fd.binds(a, acc)
    case T.BtSucc{a}:
      fd.binds(a, acc)
    case T.BtAnn{a, ty}:
      fd.binds(a, acc)
    case T.BtMatch{xs, cs}:
      fd.binds(cs, acc)
    case T.BtExpr{e}:
      fd.binds(e, acc)
    case T.BtArgs{a, rest}:
      fd.binds(a, fd.binds(rest, acc))
    case _:
      acc

def fd.anyin(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case +h <> t:
      Bool.or(S.mem(h, ys), fd.anyin(t, ys))
    case Nil{}:
      False{}

def fd.ispi(t: T.Bt) -> Bool:
  match t:
    case T.BtPi{m, x, d, a, b}:
      True{}
    case _:
      False{}

def fd.istpl(m: T.BMode) -> Bool:
  match m:
    case T.BmTpl{}:
      True{}
    case _:
      False{}

def fd.iscopy(m: T.BMode) -> Bool:
  match m:
    case T.BmCopy{}:
      True{}
    case _:
      False{}

def fd.isera(m: T.BMode) -> Bool:
  match m:
    case T.BmErased{}:
      True{}
    case _:
      False{}

# a value parameter is a template if it was, if it is a function used
# twice, or if a template argument names it
def fd.vtpl(+m: T.BMode, ty: T.Bt, +x: List<&2, U32>, +tas: List<&2, List<&2, U32>>) -> Bool:
  Bool.or(fd.istpl(m), Bool.or(Bool.and(fd.iscopy(m), fd.ispi(ty)), S.mem(x, tas)))

# the names in the types of the value parameters that are templates
def fd.vfrees(ps: List<&2, T.BParam>, +tas: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case T.BParam{+m, +x, +ty} <> t:
      List.append(&2, List<&2, U32>, Bool.pick(List<&2, List<&2, U32>>, Bool.and(Bool.not(fd.isera(m)), fd.vtpl(m, ty, x, tas)), T.tba.frees(ty, Nil{}), Nil{}), fd.vfrees(t, tas))
    case Nil{}:
      Nil{}

# each parameter's flag: a type variable is a template if a template
# argument or a template parameter's type names it
def fd.pflags(ps: List<&2, T.BParam>, +tas: List<&2, List<&2, U32>>, +tyf: List<&2, List<&2, U32>>) -> List<&2, Bool>:
  match ps:
    case T.BParam{+m, +x, ty} <> t:
      Bool.pick(Bool, fd.isera(m), Bool.or(S.mem(x, tas), S.mem(x, tyf)), fd.vtpl(m, ty, x, tas)) <> fd.pflags(t, tas, tyf)
    case Nil{}:
      Nil{}

def fd.bpick.ps(b: Bool, p: T.BParam, t: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match b:
    case True{}:
      p <> t
    case False{}:
      t

def fd.setp(ps: List<&2, T.BParam>, fl: List<&2, Bool>) -> List<&2, T.BParam>:
  match ps fl:
    case T.BParam{m, x, ty} <> t True{} <> u:
      T.BParam{T.BmTpl{}, x, ty} <> fd.setp(t, u)
    case p <> t False{} <> u:
      p <> fd.setp(t, u)
    case qs _:
      qs

def fd.tf.find(ts: List<&2, Tf>, +n: List<&2, U32>) -> Maybe<&2, List<&2, Bool>>:
  match ts:
    case Tf{+k, fl} <> t:
      Bool.pick(Maybe<&2, List<&2, Bool>>, S.eq(k, n), Some{fl}, fd.tf.find(t, n))
    case Nil{}:
      None{}

def fd.tplarg(x: T.Bt) -> T.Bt:
  match x:
    case T.BtTplArg{y}:
      T.BtTplArg{y}
    case u:
      T.BtTplArg{u}

def fd.wrap1(b: Bool, x: T.Bt) -> T.Bt:
  match b:
    case True{}:
      fd.tplarg(x)
    case False{}:
      x

def fd.wrap(fl: List<&2, Bool>, a: T.Bt) -> T.Bt:
  match fl a:
    case b <> t T.BtArgs{x, rest}:
      T.BtArgs{fd.wrap1(b, x), fd.wrap(t, rest)}
    case _ u:
      u

def fd.wrapargs(found: Maybe<&2, List<&2, Bool>>, a: T.Bt) -> T.Bt:
  match found:
    case Some{fl}:
      fd.wrap(fl, a)
    case None{}:
      a

def fd.tcall.app(f: T.Bt, a: T.Bt, +tfs: List<&2, Tf>) -> T.Bt:
  match f:
    case T.BtVar{+g}:
      T.BtApp{T.BtVar{g}, fd.wrapargs(fd.tf.find(tfs, g), a)}
    case u:
      T.BtApp{u, a}

# the calls of the module's defs in t, ~ at their template positions
def fd.tcall(t: T.Bt, +tfs: List<&2, Tf>) -> T.Bt:
  match t:
    case T.BtApp{f, a}:
      fd.tcall.app(fd.tcall(f, tfs), fd.tcall(a, tfs), tfs)
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.tcall(a, tfs), fd.tcall(rest, tfs)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.tcall(a, tfs)}
    case T.BtLam{m, y, b}:
      T.BtLam{m, y, fd.tcall(b, tfs)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.tcall(a, tfs)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.tcall(cs, tfs)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.tcall(b, tfs), fd.tcall(rest, tfs)}
    case T.BtLet{y, v, b}:
      T.BtLet{y, fd.tcall(v, tfs), fd.tcall(b, tfs)}
    case T.BtExpr{e}:
      T.BtExpr{fd.tcall(e, tfs)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.tcall(a, tfs), ty}
    case T.BtSucc{a}:
      T.BtSucc{fd.tcall(a, tfs)}
    case u:
      u

def fd.tpl.def(n: List<&2, U32>, +ps: List<&2, T.BParam>, r: T.Bt, +b: T.Bt, d: List<&2, List<&2, U32>>) -> T.BItem:
  +tas = fd.tas(b, Nil{})
  T.BiDef{n, fd.setp(ps, fd.pflags(ps, tas, fd.vfrees(ps, tas))), r, b, d}

# one round on an item: its calls with the flags so far, then its own
def fd.tpl.item(it: T.BItem, +tfs: List<&2, Tf>) -> T.BItem:
  match it:
    case T.BiDef{n, ps, r, b, d}:
      fd.tpl.def(n, ps, r, fd.tcall(b, tfs), d)
    case u:
      u

def fd.pfl(ps: List<&2, T.BParam>) -> List<&2, Bool>:
  match ps:
    case T.BParam{m, x, ty} <> t:
      fd.istpl(m) <> fd.pfl(t)
    case Nil{}:
      Nil{}

def fd.tfs(gs: List<&2, Got>) -> List<&2, Tf>:
  match gs:
    case GotDef{n, T.BiDef{k, ps, r, b, d}} <> t:
      Tf{k, fd.pfl(ps)} <> fd.tfs(t)
    case _ <> t:
      fd.tfs(t)
    case Nil{}:
      Nil{}

def fd.bits(fl: List<&2, Bool>) -> List<&2, U32>:
  match fl:
    case b <> t:
      Bool.pick(U32, b, 49, 48) <> fd.bits(t)
    case Nil{}:
      Nil{}

# the flags as text, to see whether a round changed them
def fd.tfs.key(ts: List<&2, Tf>) -> List<&2, U32>:
  match ts:
    case Tf{n, fl} <> t:
      fd.cat(n, fd.cat(fd.bits(fl), 32 <> fd.tfs.key(t)))
    case Nil{}:
      Nil{}

def fd.tpl.round(gs: List<&2, Got>, +tfs: List<&2, Tf>) -> List<&2, Got>:
  match gs:
    case GotDef{n, it} <> t:
      GotDef{n, fd.tpl.item(it, tfs)} <> fd.tpl.round(t, tfs)
    case g <> t:
      g <> fd.tpl.round(t, tfs)
    case Nil{}:
      Nil{}

def fd.tpl.rounds(fuel: Nat, done: Bool, +gs: List<&2, Got>, +itfs: List<&2, Tf>) -> List<&2, Got>:
  match fuel done:
    case 0n _:
      gs
    case 1n+p True{}:
      gs
    case 1n+p False{}:
      +g2 = fd.tpl.round(gs, List.append(&2, Tf, fd.tfs(gs), itfs))
      fd.tpl.rounds(p, S.eq(fd.tfs.key(fd.tfs(gs)), fd.tfs.key(fd.tfs(g2))), g2, itfs)

# a def whose template argument is a closure is out
def fd.tpl.check(it: T.BItem) -> T.BItem:
  match it:
    case T.BiDef{n, ps, r, +b, d}:
      T.BiDef{n, ps, r, Bool.pick(T.Bt, fd.anyin(fd.tas(b, Nil{}), fd.binds(b, Nil{})), fd.todo("fold:closure-argument"), b), d}
    case u:
      u

# Only leading binders take ~: once the flags are settled, a def's
# templates move to the front (in their order), and so do its calls'
# arguments at those positions.
def fd.ps.tpl(ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match ps:
    case T.BParam{+m, x, ty} <> t:
      fd.bpick.ps(fd.istpl(m), T.BParam{m, x, ty}, fd.ps.tpl(t))
    case Nil{}:
      Nil{}

def fd.ps.rest(ps: List<&2, T.BParam>) -> List<&2, T.BParam>:
  match ps:
    case T.BParam{+m, x, ty} <> t:
      fd.bpick.ps(Bool.not(fd.istpl(m)), T.BParam{m, x, ty}, fd.ps.rest(t))
    case Nil{}:
      Nil{}

def fd.pick.t(fl: List<&2, Bool>, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match fl xs:
    case True{} <> t x <> u:
      x <> fd.pick.t(t, u)
    case False{} <> t x <> u:
      fd.pick.t(t, u)
    case _ _:
      Nil{}

def fd.pick.f(fl: List<&2, Bool>, xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match fl xs:
    case True{} <> t x <> u:
      fd.pick.f(t, u)
    case False{} <> t x <> u:
      x <> fd.pick.f(t, u)
    case _ u:
      u

def fd.args.perm(+fl: List<&2, Bool>, a: T.Bt) -> T.Bt:
  +xs = fd.spine(a)
  T.tba.args(List.append(&2, T.Bt, fd.pick.t(fl, xs), fd.pick.f(fl, xs)))

def fd.permargs(found: Maybe<&2, List<&2, Bool>>, a: T.Bt) -> T.Bt:
  match found:
    case Some{fl}:
      fd.args.perm(fl, a)
    case None{}:
      a

def fd.tperm.app(f: T.Bt, a: T.Bt, +tfs: List<&2, Tf>) -> T.Bt:
  match f:
    case T.BtVar{+g}:
      T.BtApp{T.BtVar{g}, fd.permargs(fd.tf.find(tfs, g), a)}
    case u:
      T.BtApp{u, a}

def fd.tperm(t: T.Bt, +tfs: List<&2, Tf>) -> T.Bt:
  match t:
    case T.BtApp{f, a}:
      fd.tperm.app(fd.tperm(f, tfs), fd.tperm(a, tfs), tfs)
    case T.BtArgs{a, rest}:
      T.BtArgs{fd.tperm(a, tfs), fd.tperm(rest, tfs)}
    case T.BtTplArg{a}:
      T.BtTplArg{fd.tperm(a, tfs)}
    case T.BtLam{m, y, b}:
      T.BtLam{m, y, fd.tperm(b, tfs)}
    case T.BtCon{c, a}:
      T.BtCon{c, fd.tperm(a, tfs)}
    case T.BtMatch{xs, cs}:
      T.BtMatch{xs, fd.tperm(cs, tfs)}
    case T.BtCase{p, b, rest}:
      T.BtCase{p, fd.tperm(b, tfs), fd.tperm(rest, tfs)}
    case T.BtLet{y, v, b}:
      T.BtLet{y, fd.tperm(v, tfs), fd.tperm(b, tfs)}
    case T.BtExpr{e}:
      T.BtExpr{fd.tperm(e, tfs)}
    case T.BtAnn{a, ty}:
      T.BtAnn{fd.tperm(a, tfs), ty}
    case T.BtSucc{a}:
      T.BtSucc{fd.tperm(a, tfs)}
    case u:
      u

def fd.tpl.order(it: T.BItem, +tfs: List<&2, Tf>) -> T.BItem:
  match it:
    case T.BiDef{n, +ps, r, b, d}:
      T.BiDef{n, List.append(&2, T.BParam, fd.ps.tpl(ps), fd.ps.rest(ps)), r, fd.tperm(b, tfs), d}
    case u:
      u

def fd.tpl.fin(gs: List<&2, Got>, +tfs: List<&2, Tf>) -> List<&2, Got>:
  match gs:
    case GotDef{+n, it} <> t:
      fd.got.def(n, fd.tpl.check(fd.tpl.order(it, tfs))) <> fd.tpl.fin(t, tfs)
    case g <> t:
      g <> fd.tpl.fin(t, tfs)
    case Nil{}:
      Nil{}

# the flags settled (itfs: the package's defs', which are fixed)
def fd.tpl.settle(+gs: List<&2, Got>, +itfs: List<&2, Tf>) -> List<&2, Got>:
  fd.tpl.rounds(1n+List.length(&2, Got, gs), False{}, gs, itfs)

def fd.templates(+gs: List<&2, Got>, +itfs: List<&2, Tf>) -> List<&2, Got>:
  +g2 = fd.tpl.settle(gs, itfs)
  fd.tpl.fin(g2, List.append(&2, Tf, fd.tfs(g2), itfs))

# Package mode: what a module gives the modules after it ----------------------

def fd.akey(+alias: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  fd.cat3(alias, S.b("."), b)

def fd.iface.con(same: Bool, +c: List<&2, U32>, +t: List<&2, U32>, n: Nat, fs: List<&2, List<&2, U32>>, +m: List<&2, U32>, +alias: List<&2, U32>, acc: List<&2, Ix>) -> List<&2, Ix>:
  match same:
    case True{}:
      IxCon{V.sv.key(m, c), fd.akey(alias, fd.cname(t, c)), n, fs} <> acc
    case False{}:
      acc

# the constructors of the type t
def fd.iface.cons(cs: List<&2, Ctr>, +t: List<&2, U32>, +m: List<&2, U32>, +alias: List<&2, U32>, acc: List<&2, Ix>) -> List<&2, Ix>:
  match cs:
    case Ctr{+c, +t2, n, fs} <> rest:
      fd.iface.cons(rest, t, m, alias, fd.iface.con(S.eq(t, t2), c, t2, n, fs, m, alias, acc))
    case Nil{}:
      acc

def fd.iface.def(in: Bool, +m: List<&2, U32>, +alias: List<&2, U32>, +n: List<&2, U32>, +bn: List<&2, U32>, +ds: List<&2, Df>, acc: List<&2, Ix>) -> List<&2, Ix>:
  match in:
    case True{}:
      IxDef{V.sv.key(m, n), fd.akey(alias, bn), Maybe.default(&2, Nat, fd.df.find(ds, n), 1n)} <> acc
    case False{}:
      acc

def fd.iface.ty(in: Bool, +m: List<&2, U32>, +alias: List<&2, U32>, +n: List<&2, U32>, +bn: List<&2, U32>, +cs: List<&2, Ctr>, acc: List<&2, Ix>) -> List<&2, Ix>:
  match in:
    case True{}:
      IxTy{V.sv.key(m, n), fd.akey(alias, bn)} <> fd.iface.cons(cs, n, m, alias, acc)
    case False{}:
      acc

# the defs (selectors among them) and types the gate kept, and the kept
# types' constructors, by key
def fd.iface(gs: List<&2, Got>, +m: List<&2, U32>, +alias: List<&2, U32>, +kept: List<&2, List<&2, U32>>, +cs: List<&2, Ctr>, +ds: List<&2, Df>) -> List<&2, Ix>:
  match gs:
    case GotDef{+n, T.BiDef{+bn, ps, r, b, d}} <> t:
      fd.iface.def(S.mem(bn, kept), m, alias, n, bn, ds, fd.iface(t, m, alias, kept, cs, ds))
    case GotDef{+n, T.BiType{+bn, ps, k, cs2, d}} <> t:
      fd.iface.ty(S.mem(bn, kept), m, alias, n, bn, cs, fd.iface(t, m, alias, kept, cs, ds))
    case _ <> t:
      fd.iface(t, m, alias, kept, cs, ds)
    case Nil{}:
      Nil{}

def fd.iface.syn(isyn: Bool, +x: X.Sx, +m: List<&2, U32>, acc: List<&2, Sy>) -> List<&2, Sy>:
  match isyn:
    case True{}:
      Sy{V.sv.key(m, V.sv.str(x, 1n)), x} <> acc
    case False{}:
      acc

# the module's synonyms, by key
def fd.iface.syns(xs: List<&2, X.Sx>, +m: List<&2, U32>) -> List<&2, Sy>:
  match xs:
    case +h <> t:
      fd.iface.syn(V.sv.is(V.sv.hd(h), "synonym"), h, m, fd.iface.syns(t, m))
    case Nil{}:
      Nil{}

def fd.iface.tf(in: Bool, +alias: List<&2, U32>, +n: List<&2, U32>, fl: List<&2, Bool>, acc: List<&2, Tf>) -> List<&2, Tf>:
  match in:
    case True{}:
      Tf{fd.akey(alias, n), fl} <> acc
    case False{}:
      acc

# the kept defs' template flags, by their names as the package writes them
def fd.iface.tfs(ts: List<&2, Tf>, +alias: List<&2, U32>, +kept: List<&2, List<&2, U32>>) -> List<&2, Tf>:
  match ts:
    case Tf{+n, fl} <> t:
      fd.iface.tf(S.mem(n, kept), alias, n, fl, fd.iface.tfs(t, alias, kept))
    case Nil{}:
      Nil{}

def fd.its.names(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case h <> t:
      fd.item.name(h) <> fd.its.names(t)
    case Nil{}:
      Nil{}

def fd.files.if(wrote: Bool, +a: List<&2, U32>, fs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match wrote:
    case True{}:
      a <> fs
    case False{}:
      fs

def fd.iface.fcs(cs: List<&2, Fc>, +alias: List<&2, U32>) -> List<&2, Fc>:
  match cs:
    case Fc{c, rs} <> t:
      Fc{fd.akey(alias, c), rs} <> fd.iface.fcs(t, alias)
    case Nil{}:
      Nil{}

def fd.iface.fz(in: Bool, z: Fz, +alias: List<&2, U32>, acc: List<&2, Ix>) -> List<&2, Ix>:
  match in z:
    case True{} Fz{k, b, tvs, cs}:
      IxFun{k, fd.akey(alias, b), fd.iface.fcs(cs, alias)} <> acc
    case _ _:
      acc

# the module's functors whose types it kept, their names as the package
# writes them
def fd.iface.fzs(zs: List<&2, Fz>, +alias: List<&2, U32>, +kept: List<&2, List<&2, U32>>) -> List<&2, Ix>:
  match zs:
    case +z <> t:
      fd.iface.fz(S.mem(fd.fz.b(z), kept), z, alias, fd.iface.fzs(t, alias, kept))
    case Nil{}:
      Nil{}

# the package after the module m (alias: its file's base name) kept the items kept
def fd.px.add(p: Px, +m: List<&2, U32>, +alias: List<&2, U32>, wrote: Bool, ix: List<&2, Ix>, sy: List<&2, Sy>, tf: List<&2, Tf>, dt: List<&2, T.BItem>) -> Px:
  match p:
    case Px{h, f, i, s, t, z}:
      Px{m <> h, fd.files.if(wrote, alias, f), List.append(&2, Ix, ix, i), List.append(&2, Sy, sy, s), List.append(&2, Tf, tf, t), List.append(&2, T.BItem, dt, z)}

# A kept data type as a later module names it: Alias.T, its constructors
# Alias.T.C, the types of the module in its fields Alias.U
def fd.dt.q(t: T.Bt, +tn: List<&2, List<&2, U32>>, +a: List<&2, U32>) -> T.Bt:
  match t:
    case T.BtTyApp{+n, args}:
      T.BtTyApp{fd.bpick(S.mem(n, tn), fd.akey(a, n), n), fd.dt.q(args, tn, a)}
    case T.BtVar{+n}:
      T.BtVar{fd.bpick(S.mem(n, tn), fd.akey(a, n), n)}
    case T.BtArgs{h, r}:
      T.BtArgs{fd.dt.q(h, tn, a), fd.dt.q(r, tn, a)}
    case T.BtLam{m, x, b}:
      T.BtLam{m, x, fd.dt.q(b, tn, a)}
    case T.BtPi{m, x, d, a2, b}:
      T.BtPi{m, x, d, fd.dt.q(a2, tn, a), fd.dt.q(b, tn, a)}
    case T.BtApp{f, a2}:
      T.BtApp{fd.dt.q(f, tn, a), fd.dt.q(a2, tn, a)}
    case u:
      u

def fd.dt.fields(fs: List<&2, T.BField>, +tn: List<&2, List<&2, U32>>, +a: List<&2, U32>) -> List<&2, T.BField>:
  match fs:
    case Nil{}:
      Nil{}
    case T.BField{x, ty} <> t:
      T.BField{x, fd.dt.q(ty, tn, a)} <> fd.dt.fields(t, tn, a)

def fd.dt.ctors(cs: List<&2, T.BCtor>, +tn: List<&2, List<&2, U32>>, +a: List<&2, U32>) -> List<&2, T.BCtor>:
  match cs:
    case Nil{}:
      Nil{}
    case T.BCtor{c, fs} <> t:
      T.BCtor{fd.akey(a, c), fd.dt.fields(fs, tn, a)} <> fd.dt.ctors(t, tn, a)

def fd.dt.tnames(its: List<&2, T.BItem>) -> List<&2, List<&2, U32>>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiType{n, ps, k, cs, d} <> t:
      n <> fd.dt.tnames(t)
    case h <> t:
      fd.dt.tnames(t)

# a partial def (fd.pt) as a later module calls it: Alias.f, its
# signature with the answer inside the Either (fd.pt.imported reads it)
def fd.dt.params(ps: List<&2, T.BParam>, +tn: List<&2, List<&2, U32>>, +a: List<&2, U32>) -> List<&2, T.BParam>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      T.BParam{m, x, fd.dt.q(ty, tn, a)} <> fd.dt.params(t, tn, a)

def fd.pt.inner(r: T.Bt) -> T.Bt:
  match r:
    case T.BtTyApp{n, args}:
      fd.pt.nth(fd.pt.list(args), 3n)
    case u:
      u

def fd.dt.def(c: Bool, n: List<&2, U32>, ps: List<&2, T.BParam>, r: T.Bt, rest: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match c:
    case True{}:
      T.BiDef{n, ps, r, T.BtExpr{T.BtType{}}, [S.b(fd.pt.doc())]} <> rest
    case False{}:
      rest

def fd.dt.export(its: List<&2, T.BItem>, +a: List<&2, U32>, +tn: List<&2, List<&2, U32>>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiType{n, ps, k, cs, d} <> t:
      T.BiType{fd.akey(a, n), ps, k, fd.dt.ctors(cs, tn, a), d} <> fd.dt.export(t, a, tn)
    case T.BiDef{n, ps, r, b, +d} <> t:
      fd.dt.def(S.mem(S.b(fd.pt.doc()), d), fd.akey(a, n), fd.dt.params(ps, tn, a), fd.dt.q(fd.pt.inner(r), tn, a), fd.dt.export(t, a, tn))
    case h <> t:
      fd.dt.export(t, a, tn)

# in package mode, the package after the module; a module alone gives nothing
def fd.px.next(pkg: Bool, +p: Px, +m: List<&2, U32>, +alias: List<&2, U32>, +xs: List<&2, X.Sx>, +gs: List<&2, Got>, +tfs: List<&2, Tf>, +cs: List<&2, Ctr>, +ds: List<&2, Df>, +kept: List<&2, T.BItem>) -> Px:
  match pkg:
    case True{}:
      +names = fd.its.names(kept)
      fd.px.add(p, m, alias, fd.wrote(True{}, kept), List.append(&2, Ix, fd.iface.fzs(fd.fzs(xs, m), alias, names), fd.iface(gs, m, alias, names, cs, ds)), fd.iface.syns(xs, m), fd.iface.tfs(tfs, alias, names), fd.dt.export(kept, alias, fd.dt.tnames(kept)))
    case False{}:
      p

def fd.gs.its(g: Gs) -> List<&2, T.BItem>:
  match g:
    case Gs{k, o, d}:
      k

# A def a pass after the fold left a place unfilled in (a BtTodo: the
# partial pass's fold:partial-in-lambda) is out before the first check,
# its first reason its why (the fold's own todos are out as Gots)
def fd.td.keep(its: List<&2, T.BItem>) -> List<&2, T.BItem>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, +b, d} <> t:
      fd.without.put(Bool.not(List.is_empty(&2, List<&2, U32>, T.tba.todos(b, Nil{}))), T.BiDef{n, ps, r, b, d}, fd.td.keep(t))
    case h <> t:
      h <> fd.td.keep(t)

def fd.td.out(ws: List<&2, List<&2, U32>>, n: List<&2, U32>, rest: List<&2, Dr>) -> List<&2, Dr>:
  match ws:
    case Nil{}:
      rest
    case w <> t:
      Dr{n, w} <> rest

def fd.td.outs(its: List<&2, T.BItem>) -> List<&2, Dr>:
  match its:
    case Nil{}:
      Nil{}
    case T.BiDef{n, ps, r, b, d} <> t:
      fd.td.out(T.tba.todos(b, Nil{}), n, fd.td.outs(t))
    case _ <> t:
      fd.td.outs(t)

# the items that use a binding that is out go too, before the first check
def fd.predrop(+its: List<&2, T.BItem>, +outs: List<&2, Dr>) -> Gs:
  +ki = fd.td.keep(its)
  +os = List.append(&2, Dr, outs, fd.td.outs(its))
  +s = fd.closure(List.length(&2, T.BItem, ki), fd.split(ki, fd.dr.names(os), S.b("dep")), S.b("dep"), os)
  Gs{Split.keep(s), Split.out(s), List.is_empty(&2, T.BItem, Split.keep(s))}

# a module: fold its bindings, gate them, write OUT/BASE.bend and the ledger
# a module of a package (px: what the modules before it gave, fd.px0() for
# a module alone); the package after it
def fd.module(+rounds: Nat, +bend: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, bytes: List<&2, U32>, +pkg: Bool, +px: Px) -> IO(Px):
  +xs = X.tsx.read(bytes)
  +m = V.sv.modname(xs)
  +tbs = fd.tbs(xs)
  +cs = fd.ctrs(xs)
  +ds = fd.dfs(tbs)
  +env = fd.syns(Nat.add(fd.nsyn(xs), List.length(&2, Sy, fd.px.sy(px))), xs, fd.env0(m, cs, ds, px))
  +g2 = fd.tpl.settle(fd.allgots(xs, tbs, env), fd.px.tfs(px))
  +gs = fd.tpl.fin(g2, List.append(&2, Tf, fd.tfs(g2), fd.px.tfs(px)))
  +its = fd.mod.its(gs, xs, m, env, px)
  +ims = fd.ims(px)
  +path = out ++ "/" ++ S.str(base) ++ ".bend"
  +try = out ++ "/" ++ S.str(base) ++ "_try.bend"
  do IO<Px>:
    fd.hsprelude.write(out)
    +g : Gs <- fd.gate(Bool.pick(Nat, Nat.is_eq(rounds, 0n), Nat.mul(3n, 1n+List.length(&2, T.BItem, its)), rounds), fd.predrop(its, fd.got.outs(gs)), bend, try, file, m, ims, fd.px.dt(px))
    fd.module.fin(out, file, m, ims, path, pkg, g)
    return fd.px.next(pkg, px, m, base, xs, gs, fd.tfs(g2), cs, ds, fd.gs.its(g))

def fd.base.strip(r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case 112 <> 120 <> 101 <> 115 <> 46 <> t:
      List.reverse(&2, U32, t)
    case u:
      List.reverse(&2, U32, u)

# a file's base name without .sexp
def fd.base(+f: List<&2, U32>) -> List<&2, U32>:
  fd.base.strip(List.reverse(&2, U32, Maybe.default(&2, List<&2, U32>, List.last(&2, List<&2, U32>, S.split(f, 47)), f)))

def fd.run(xs: List<String>, +rounds: Nat, +bend: String, +out: String, +pkg: Bool, +px: Px) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +p2 : Px <- fd.module(rounds, bend, out, S.b(f), fd.base(S.b(f)), bytes, pkg, px)
        fd.run(t, rounds, bend, out, pkg, p2)

def fd.main.go(pkg: Bool, args: List<String>, +rounds: Nat, +bend: String) -> IO(Unit):
  match args:
    case out <> files:
      fd.run(files, rounds, bend, out, pkg, fd.px0())
    case Nil{}:
      IO.print("usage: fold [--package] OUT FILE.sexp...  (BEND: the bend to check with)")

def fd.main.pkg(pkg: Bool, a: String, rest: List<String>, +rounds: Nat, +bend: String) -> IO(Unit):
  match pkg:
    case True{}:
      fd.main.go(True{}, rest, rounds, bend)
    case False{}:
      fd.main.go(False{}, a <> rest, rounds, bend)

# `fold OUT FILE...` folds each module alone; `fold --package OUT FILE...`
# folds one package's modules in dependency order (hs-export --package's
# modules.txt): each may use what the ones before it kept, and imports
# their files
def fd.main(args: List<String>, +rounds: Nat, +bend: String) -> IO(Unit):
  match args:
    case +a <> rest:
      fd.main.pkg(S.eq(S.b(a), S.b("--package")), a, rest, rounds, bend)
    case Nil{}:
      fd.main.go(False{}, Nil{}, rounds, bend)

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    bend : String <- S.env("BEND", "bend")
    rounds : Nat <- S.env.nat("FOLD_ROUNDS", 0n)
    fd.main(List.tail(&1, String, argv), rounds, bend)
