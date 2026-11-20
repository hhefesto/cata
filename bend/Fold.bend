import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X
import ./a2b/ToBend/Ast.bend as T
import ./a2b/ToBend/Print.bend as P
import ./a2b/ToBend/Order.bend as O
import ./Survey.bend as V

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
#     (~f), so the function must be closed: a lambda over locals is out.
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
  TkNone{}

type TkE is Data:
  TkE{k: String, v: Tk}

def fd.tktab() -> List<&2, TkE>:
  [TkE{"GHC.Types.Int", TkNat{}}, TkE{"GHC.Num.Integer.Integer", TkNat{}}, TkE{"GHC.Num.Natural.Natural", TkNat{}}, TkE{"GHC.Types.Bool", TkBool{}}, TkE{"GHC.Types.Char", TkChar{}}, TkE{"GHC.Types.Float", TkF32{}}, TkE{"GHC.Types.List", TkList{}}, TkE{"GHC.Internal.Base.String", TkStr{}}, TkE{"GHC.Internal.IO.FilePath", TkStr{}}, TkE{"GHC.Internal.Maybe.Maybe", TkMaybe{}}, TkE{"GHC.Internal.Data.Either.Either", TkEither{}}, TkE{"GHC.Tuple.Tuple2", TkT2{}}, TkE{"GHC.Tuple.Tuple3", TkT3{}}, TkE{"GHC.Tuple.Unit", TkUnit{}}, TkE{"GHC.Types.Ordering", TkCmp{}}, TkE{"Data.Fix.Fix", TkFix{}}, TkE{"Control.Comonad.Cofree.Cofree", TkCofree{}}, TkE{"Control.Comonad.Trans.Cofree.CofreeF", TkCofreeF{}}, TkE{"Data.Functor.Foldable.Base", TkBase{}}, TkE{"Control.Monad.Trans.State.Lazy.State", TkState{}}, TkE{"Control.Monad.Trans.State.Strict.State", TkState{}}, TkE{"Control.Monad.Trans.State.Lazy.StateT", TkStateT{}}, TkE{"Control.Monad.Trans.State.Strict.StateT", TkStateT{}}, TkE{"GHC.Internal.Data.Functor.Identity.Identity", TkIdentity{}}]

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

def fd.ty.cofreef(args: List<&2, T.Bt>) -> T.Bt:
  match args:
    case f <> a <> b <> Nil{}:
      T.BtTyApp{S.b("HsPrelude.CofreeF"), T.tba.args([fd.fn.lam(f), a, b])}
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

def fd.ty.base.if(fix: Bool, cof: Bool, rest: T.Bt, l: T.Bt, a: T.Bt) -> T.Bt:
  match fix cof rest:
    case True{} _ _:
      fd.lam.at(l, a)
    case False{} True{} T.BtArgs{w, _}:
      T.BtTyApp{S.b("HsPrelude.CofreeF"), T.tba.args([l, w, a])}
    case _ _ _:
      fd.todo("type:Data.Functor.Foldable.Base")

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
def fd.tc.none(tn: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>, args: List<&2, T.Bt>) -> T.Bt:
  match tn:
    case Some{b}:
      T.BtTyApp{b, T.tba.args(args)}
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
    case _:
      fd.todo("fold:identity-type")

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
  CbNone{}

type CbE is Data:
  CbE{k: String, v: Cb}

def fd.cbtab() -> List<&2, CbE>:
  [CbE{"GHC.Types.:", CbCons{}}, CbE{"GHC.Types.[]", CbNil{}}, CbE{"GHC.Types.True", CbTrue{}}, CbE{"GHC.Types.False", CbFalse{}}, CbE{"GHC.Internal.Maybe.Just", CbJust{}}, CbE{"GHC.Internal.Maybe.Nothing", CbNothing{}}, CbE{"GHC.Internal.Data.Either.Left", CbLeft{}}, CbE{"GHC.Internal.Data.Either.Right", CbRight{}}, CbE{"GHC.Types.LT", CbLT{}}, CbE{"GHC.Types.EQ", CbEQ{}}, CbE{"GHC.Types.GT", CbGT{}}, CbE{"GHC.Tuple.()", CbUnit{}}, CbE{"GHC.Tuple.(,)", CbT2{}}, CbE{"GHC.Tuple.(,,)", CbT3{}}, CbE{"Data.Fix.Fix", CbFix{}}, CbE{"Control.Comonad.Cofree.:<", CbCofree{}}, CbE{"Control.Comonad.Trans.Cofree.:<", CbCofreeF{}}]

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
  Px{home: List<&2, List<&2, U32>>, files: List<&2, List<&2, U32>>, ix: List<&2, Ix>, sy: List<&2, Sy>, tfs: List<&2, Tf>}

def fd.px0() -> Px:
  Px{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

def fd.px.home(p: Px) -> List<&2, List<&2, U32>>:
  match p:
    case Px{h, f, i, s, t}:
      h

def fd.px.files(p: Px) -> List<&2, List<&2, U32>>:
  match p:
    case Px{h, f, i, s, t}:
      f

def fd.px.ix(p: Px) -> List<&2, Ix>:
  match p:
    case Px{h, f, i, s, t}:
      i

def fd.px.sy(p: Px) -> List<&2, Sy>:
  match p:
    case Px{h, f, i, s, t}:
      s

def fd.px.tfs(p: Px) -> List<&2, Tf>:
  match p:
    case Px{h, f, i, s, t}:
      t

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
  BfNone{}

type BfE is Data:
  BfE{k: String, v: Bf}

def fd.bftab() -> List<&2, BfE>:
  [BfE{"GHC.Classes.==", BfCmp{"is_eq"}}, BfE{"GHC.Classes./=", BfCmp{"is_ne"}}, BfE{"GHC.Classes.<", BfCmp{"is_lt"}}, BfE{"GHC.Classes.<=", BfCmp{"is_le"}}, BfE{"GHC.Classes.>", BfCmp{"is_gt"}}, BfE{"GHC.Classes.>=", BfCmp{"is_ge"}}, BfE{"GHC.Classes.compare", BfCmp{"cmp"}}, BfE{"GHC.Classes.max", BfCmp{"max"}}, BfE{"GHC.Classes.min", BfCmp{"min"}}, BfE{"GHC.Classes.&&", BfAnd{}}, BfE{"GHC.Classes.||", BfOr{}}, BfE{"GHC.Classes.not", BfNot{}}, BfE{"GHC.Internal.Base.otherwise", BfTrue{}}, BfE{"GHC.Internal.Num.+", BfNum{"add"}}, BfE{"GHC.Internal.Num.*", BfNum{"mul"}}, BfE{"GHC.Internal.Real.div", BfNum{"div"}}, BfE{"GHC.Internal.Real.mod", BfNum{"mod"}}, BfE{"GHC.Internal.Real.quot", BfNum{"div"}}, BfE{"GHC.Internal.Real.rem", BfNum{"mod"}}, BfE{"GHC.Internal.Real.^", BfNum{"pow"}}, BfE{"GHC.Internal.Real./", BfNum{"div"}}, BfE{"GHC.Internal.Base.++", BfAppend{}}, BfE{"GHC.Internal.Data.Foldable.length", BfLength{}}, BfE{"GHC.Internal.Data.Foldable.null", BfNull{}}, BfE{"GHC.Internal.List.reverse", BfReverse{}}, BfE{"GHC.Internal.Data.Foldable.concat", BfConcat{}}, BfE{"GHC.Internal.List.take", BfTake{}}, BfE{"GHC.Internal.List.drop", BfDrop{}}, BfE{"GHC.Internal.List.replicate", BfReplicate{}}, BfE{"GHC.Internal.Base.map", BfMap{}}, BfE{"GHC.Internal.List.filter", BfFilter{}}, BfE{"GHC.Internal.Data.Foldable.any", BfAny{}}, BfE{"GHC.Internal.Data.Foldable.all", BfAll{}}, BfE{"GHC.Internal.Data.Foldable.foldr", BfFoldr{}}, BfE{"GHC.Internal.Data.Foldable.foldl", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.foldl'", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.elem", BfElem{}}, BfE{"GHC.Internal.Data.Foldable.sum", BfSum{}}, BfE{"GHC.Internal.Data.Foldable.product", BfProduct{}}, BfE{"GHC.Internal.Data.Foldable.and", BfAndL{}}, BfE{"GHC.Internal.Data.Foldable.or", BfOrL{}}, BfE{"GHC.Internal.Data.Foldable.concatMap", BfConcatMap{}}, BfE{"GHC.Internal.Show.show", BfShow{}}, BfE{"GHC.Internal.Base.id", BfId{}}, BfE{"GHC.Internal.Base.const", BfConst{}}, BfE{"GHC.Internal.Enum.succ", BfSucc{}}, BfE{"Data.Fix.unFix", BfUnFix{}}, BfE{"Data.Functor.Foldable.project", BfProject{}}, BfE{"Data.Functor.Foldable.embed", BfEmbed{}}, BfE{"Data.Functor.Foldable.cata", BfCata{}}, BfE{"GHC.Internal.Base.>>=", BfBind{}}, BfE{"GHC.Internal.Base.>>", BfThen{}}, BfE{"GHC.Internal.Base.return", BfPure{}}, BfE{"GHC.Internal.Base.pure", BfPure{}}, BfE{"GHC.Internal.Base.fmap", BfFmap{}}, BfE{"GHC.Internal.Data.Functor.<$>", BfFmap{}}, BfE{"GHC.Internal.Data.Maybe.maybe", BfMaybe{}}, BfE{"GHC.Internal.Data.Maybe.fromMaybe", BfFromMaybe{}}, BfE{"GHC.Internal.Data.Either.either", BfEither{}}, BfE{"GHC.Internal.Base.<>", BfSemi{}}, BfE{"GHC.Internal.Base.<*>", BfAp{}}, BfE{"Control.Monad.State.Class.get", BfGet{}}, BfE{"Control.Monad.State.Class.put", BfPut{}}, BfE{"Control.Monad.State.Class.modify", BfModify{}}, BfE{"Control.Monad.State.Class.modify'", BfModify{}}, BfE{"Control.Monad.State.Class.gets", BfGets{}}, BfE{"Control.Monad.Trans.State.Lazy.evalState", BfEval{}}, BfE{"Control.Monad.Trans.State.Strict.evalState", BfEval{}}, BfE{"Control.Monad.Trans.State.Lazy.execState", BfExec{}}, BfE{"Control.Monad.Trans.State.Strict.execState", BfExec{}}, BfE{"Control.Monad.Trans.State.Lazy.runState", BfRun{}}, BfE{"Control.Monad.Trans.State.Strict.runState", BfRun{}}]

def fd.bf.find(xs: List<&2, BfE>, +k: List<&2, U32>) -> Bf:
  match xs:
    case Nil{}:
      BfNone{}
    case BfE{s, v} <> t:
      Bool.pick(Bf, S.eq(S.b(s), k), v, fd.bf.find(t, k))

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
    case BfMaybe{}:
      3n
    case BfEither{}:
      3n
    case BfFoldr{}:
      3n
    case BfFoldl{}:
      3n
    case _:
      2n

# what a type argument is, for the functions that differ by type
type Tq is Data:
  TqNat{}
  TqChar{}
  TqBool{}
  TqF32{}
  TqOther{}

def fd.tq.of(+n: List<&2, U32>) -> Tq:
  Bool.pick(Tq, fd.is(n, "Nat"), TqNat{}, Bool.pick(Tq, fd.is(n, "Char"), TqChar{}, Bool.pick(Tq, fd.is(n, "Bool"), TqBool{}, Bool.pick(Tq, fd.is(n, "F32"), TqF32{}, TqOther{}))))

def fd.tq(t: T.Bt) -> Tq:
  match t:
    case T.BtTyApp{n, T.BtANil{}}:
      fd.tq.of(n)
    case _:
      TqOther{}

# Foldable's functions at a list (the container argument is the marker List)
def fd.foldable(c: T.Bt, t: T.Bt) -> T.Bt:
  match c:
    case T.BtVar{n}:
      Bool.pick(T.Bt, fd.is(n, "List"), t, fd.todo("fold:foldable-not-list"))
    case _:
      fd.todo("fold:foldable-not-list")

def fd.cmp.char(+op: List<&2, U32>, +a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(op, "is_eq"), fd.callS("Char.is_eq", [a, b]), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.not", [fd.callS("Char.is_eq", [a, b])]), Bool.pick(T.Bt, Bool.or(fd.is(op, "max"), fd.is(op, "min")), fd.todo("fold:char-max"), T.tba.call(T.BtVar{fd.cat(S.b("U32."), op)}, [fd.callS("Char.to_u32", [a]), fd.callS("Char.to_u32", [b])]))))

def fd.cmp.bool(+op: List<&2, U32>, +a: T.Bt, +b: T.Bt) -> T.Bt:
  Bool.pick(T.Bt, fd.is(op, "is_eq"), fd.callS("Bool.not", [fd.callS("Bool.xor", [a, b])]), Bool.pick(T.Bt, fd.is(op, "is_ne"), fd.callS("Bool.xor", [a, b]), fd.todo("fold:bool-order")))

def fd.cmp(q: Tq, op: String, a: T.Bt, b: T.Bt) -> T.Bt:
  match q:
    case TqF32{}:
      fd.callS("F32." ++ op, [a, b])
    case TqNat{}:
      fd.callS("Nat." ++ op, [a, b])
    case TqChar{}:
      fd.cmp.char(S.b(op), a, b)
    case TqBool{}:
      fd.cmp.bool(S.b(op), a, b)
    case TqOther{}:
      fd.todo("fold:eq-at-type")

def fd.num(q: Tq, op: String, a: T.Bt, b: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.callS("Nat." ++ op, [a, b])
    case TqF32{}:
      fd.callS("F32." ++ op, [a, b])
    case _:
      fd.todo("fold:num-at-type")

def fd.elem(q: Tq, +t: T.Bt, x: T.Bt, xs: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.v("Nat.is_eq")), xs, x])
    case TqChar{}:
      fd.callS("List.contains", [fd.tpl0(t), fd.tpl0(fd.v("Char.is_eq")), xs, x])
    case _:
      fd.todo("fold:elem-at-type")

def fd.sum(q: Tq, f: T.Bt, z: T.Bt, xs: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.callS("List.foldl", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Nat")), fd.tpl0(fd.ty0("Nat")), fd.tpl0(f), xs, z])
    case _:
      fd.todo("fold:sum-at-type")

def fd.show(q: Tq, x: T.Bt) -> T.Bt:
  match q:
    case TqNat{}:
      fd.callS("String.to_list", [fd.callS("Nat.show", [x])])
    case _:
      fd.todo("fold:show-at-type")

def fd.succ(q: Tq, x: T.Bt) -> T.Bt:
  match q:
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
  MkOther{}

def fd.mk.one(+n: List<&2, U32>, a: T.Bt) -> Mk:
  Bool.pick(Mk, fd.is(n, "Maybe"), MkMaybe{}, Bool.pick(Mk, fd.is(n, "hs.State"), MkState{a}, MkOther{}))

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
    case T.BtTyApp{+n, T.BtArgs{a, T.BtANil{}}}:
      fd.mk.one(n, a)
    case T.BtTyApp{n, T.BtArgs{a, T.BtArgs{b, T.BtArgs{e, T.BtANil{}}}}}:
      fd.mk.three(fd.is(n, "Either"), e)
    case T.BtVar{n}:
      fd.mk.var(fd.is(n, "List"))
    case _:
      MkOther{}

def fd.bind(k: Mk, a: T.Bt, b: T.Bt, x: T.Bt, f: T.Bt) -> T.Bt:
  match k:
    case MkMaybe{}:
      fd.callS("Maybe.bind", [fd.v("&2"), a, b, x, f])
    case MkEither{e}:
      fd.callS("hs.either.bind", [e, a, b, x, f])
    case MkState{s}:
      fd.callS("hs.state.bind", [s, a, b, x, f])
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
    case MkList{}:
      fd.callS("hs.map", [fd.tpl0(a), fd.tpl0(b), g, x])
    case _:
      fd.todo("fold:fmap-at-type")

# <*>, and MonadState's methods (mtl), at State s
def fd.ap(k: Mk, a: T.Bt, b: T.Bt, f: T.Bt, x: T.Bt) -> T.Bt:
  match k:
    case MkState{s}:
      fd.callS("hs.state.ap", [s, a, b, fd.untpl(f), x])
    case _:
      fd.todo("fold:applicative-at-type")

def fd.st.get(k: Mk, s: T.Bt) -> T.Bt:
  match k:
    case MkState{t}:
      fd.callS("hs.state.get", [s])
    case _:
      fd.todo("fold:monadstate-at-type")

def fd.st.call(k: Mk, f: String, xs: List<&2, T.Bt>) -> T.Bt:
  match k:
    case MkState{t}:
      fd.callS(f, xs)
    case _:
      fd.todo("fold:monadstate-at-type")

# <> at a list
def fd.semi(t: T.Bt, x: T.Bt, y: T.Bt) -> T.Bt:
  match t:
    case T.BtTyApp{n, T.BtArgs{q, T.BtArgs{a, T.BtANil{}}}}:
      Bool.pick(T.Bt, fd.is(n, "List"), fd.callS("List.append", [fd.v("&2"), a, x, y]), fd.todo("fold:semigroup-at-type"))
    case _:
      fd.todo("fold:semigroup-at-type")

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

def fd.tpls(xs: List<&2, T.Bt>) -> List<&2, T.Bt>:
  match xs:
    case h <> t:
      fd.tpl0(h) <> fd.tpls(t)
    case Nil{}:
      Nil{}

# G.cata(~A.., ~R, ~alg, x) at Fix<(r_ => G<A.., r_>)>, and
# G.cata.cofree(~A.., ~W, ~R, ~alg, x) at Cofree<(r_ => G<A.., r_>), W>
def fd.cata.call(+n: List<&2, U32>, +s: String, args: T.Bt, more: List<&2, T.Bt>) -> T.Bt:
  T.tba.call(T.BtVar{fd.cat(n, S.b(s))}, List.append(&2, T.Bt, fd.tpls(fd.init(fd.spine(args))), more))

def fd.cata.if(fix: Bool, cof: Bool, own: Bool, +n: List<&2, U32>, args: T.Bt, rest: T.Bt, r: T.Bt, g: T.Bt, x: T.Bt) -> T.Bt:
  match fix cof own rest:
    case True{} _ True{} _:
      fd.cata.call(n, ".cata", args, [fd.tpl0(r), g, x])
    case False{} True{} True{} T.BtArgs{w, _}:
      fd.cata.call(n, ".cata.cofree", args, [fd.tpl0(w), fd.tpl0(r), g, x])
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

def fd.mul2() -> T.Bt:
  T.BtLam{T.BmLive{}, S.b("p"), T.BtLam{T.BmLive{}, S.b("q"), fd.callS("Nat.mul", [fd.v("p"), fd.v("q")])}}

# a saturated call of one of base's functions, as Base writes it
def fd.bf.mk(f: Bf, tys: List<&2, T.Bt>, xs: List<&2, T.Bt>, +ls: List<&2, List<&2, U32>>) -> T.Bt:
  match f tys xs:
    case BfCmp{op} t <> _ a <> b <> _:
      fd.cmp(fd.tq(t), op, a, b)
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
    case BfLength{} c <> t <> _ a <> _:
      fd.foldable(c, fd.callS("List.length", [fd.v("&2"), t, a]))
    case BfNull{} c <> t <> _ a <> _:
      fd.foldable(c, fd.callS("List.is_empty", [fd.v("&2"), t, a]))
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
    case BfAny{} c <> t <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.any", [fd.tpl0(fd.v("&2")), fd.tpl0(t), fd.tpl(ls, g), l]))
    case BfAll{} c <> t <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.all", [fd.tpl0(fd.v("&2")), fd.tpl0(t), fd.tpl(ls, g), l]))
    case BfFoldr{} c <> a <> b <> _ g <> z <> l <> _:
      fd.foldable(c, fd.callS("List.foldr", [fd.tpl0(fd.v("&2")), fd.tpl0(a), fd.tpl0(b), fd.tpl(ls, g), l, z]))
    case BfFoldl{} c <> b <> a <> _ g <> z <> l <> _:
      fd.foldable(c, fd.callS("List.foldl", [fd.tpl0(fd.v("&2")), fd.tpl0(a), fd.tpl0(b), fd.tpl(ls, g), l, z]))
    case BfElem{} c <> +t <> _ x <> l <> _:
      fd.foldable(c, fd.elem(fd.tq(t), t, x, l))
    case BfSum{} c <> +t <> _ l <> _:
      fd.foldable(c, fd.sum(fd.tq(t), fd.v("Nat.add"), T.BtNat{S.b("0")}, l))
    case BfProduct{} c <> +t <> _ l <> _:
      fd.foldable(c, fd.sum(fd.tq(t), fd.mul2(), T.BtNat{S.b("1")}, l))
    case BfAndL{} c <> _ l <> _:
      fd.foldable(c, fd.callS("List.all", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Bool")), fd.tpl0(T.BtLam{T.BmLive{}, S.b("b"), fd.v("b")}), l]))
    case BfOrL{} c <> _ l <> _:
      fd.foldable(c, fd.callS("List.any", [fd.tpl0(fd.v("&2")), fd.tpl0(fd.ty0("Bool")), fd.tpl0(T.BtLam{T.BmLive{}, S.b("b"), fd.v("b")}), l]))
    case BfConcatMap{} c <> a <> +b <> _ g <> l <> _:
      fd.foldable(c, fd.callS("List.concat", [fd.v("&2"), b, fd.callS("hs.map", [fd.tpl0(a), fd.tpl0(fd.list(b)), fd.tpl(ls, g), l])]))
    case BfShow{} +t <> _ x <> _:
      fd.show(fd.tq(t), x)
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
      fd.fmap(fd.mk(m), a, b, fd.tpl(ls, g), x)
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
      fd.st.call(fd.mk(m), "hs.state.put", [s, x])
    case BfModify{} s <> m <> _ g <> _:
      fd.st.call(fd.mk(m), "hs.state.modify", [s, fd.untpl(g)])
    case BfGets{} s <> m <> a <> _ g <> _:
      fd.st.call(fd.mk(m), "hs.state.gets", [s, a, fd.untpl(g)])
    case BfEval{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.eval", [s, a, m, x])
    case BfExec{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.exec", [s, a, m, x])
    case BfRun{} s <> a <> _ m <> x <> _:
      fd.callS("hs.state.run", [s, a, m, x])
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

def fd.bglobal(con: Bool, +key: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match con:
    case True{}:
      fd.bcon(fd.cb.find(fd.cbtab(), key), key, all)
    case False{}:
      fd.bfun(fd.bf.find(fd.bftab(), key), key, tys, all, fd.env.ls(env))

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
      fd.imp.g(fd.ix.find(fd.env.ix(env), key), key, tys, all)
    case False{}:
      fd.bglobal(fd.is(k, "con"), key, tys, all, env)

def fd.global(own: Bool, +m: List<&2, U32>, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match own:
    case True{}:
      fd.own.g(fd.is(k, "var"), fd.is(k, "con"), n, k, tys, all, env)
    case False{}:
      +key = fd.cat3(m, S.b("."), n)
      fd.hglobal(S.mem(m, fd.env.home(env)), key, k, tys, all, env)

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
      fd.pcon.imp(fd.ix.find(fd.env.ix(env), key), key, ps)
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

def fd.pconf.of(own: Bool, m: Maybe<&2, Ctr>, +xs: List<&2, R>) -> T.Bt:
  match own m:
    case True{} Some{Ctr{+c, +t, n, fs}}:
      T.BtCon{fd.cname(t, c), T.tba.args(fd.pfields(fs, xs))}
    case True{} None{}:
      fd.todo("fold:unknown-constructor")
    case False{} _:
      fd.todo("fold:record-pattern-base")

def fd.pconf.imp(found: Maybe<&2, Ix>, +xs: List<&2, R>) -> T.Bt:
  match found:
    case Some{IxCon{k, b, n, fs}}:
      T.BtCon{b, T.tba.args(fd.pfields(fs, xs))}
    case _:
      fd.todo("fold:unknown-constructor")

def fd.pconf.at(own: Bool, home: Bool, +g: X.Sx, +xs: List<&2, R>, +env: Env) -> T.Bt:
  match own home:
    case True{} _:
      fd.pconf.of(True{}, fd.ctr.find(fd.env.cons(env), V.sv.str(g, 2n)), xs)
    case False{} True{}:
      fd.pconf.imp(fd.ix.find(fd.env.ix(env), fd.gkey(g)), xs)
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
      fd.reccon.imp(fd.ix.find(fd.env.ix(env), fd.gkey(g)), xs, env)
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
def fd.olit.of(q: Tq, +v: X.Sx) -> T.Bt:
  match q:
    case TqNat{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtNat{X.tsx.atom.of(V.sv.at(v, 1n))}, fd.todo("fold:literal"))
    case TqF32{}:
      Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtVar{fd.cat(X.tsx.atom.of(V.sv.at(v, 1n)), S.b(".0"))}, Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "frac"), T.BtVar{V.sv.str(v, 3n)}, fd.todo("fold:literal")))
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
      Bool.pick(Lq, fd.is(x, "%ldef"), LqDef{}, LqNo{})
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

def fd.thunk(t: T.Bt) -> T.Bt:
  T.BtLam{T.BmLive{}, S.b("u"), fd.expr(t)}

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
    case RLf{x, tys, res, cls} <> t:
      x <> fd.bnames(t)
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
def fd.wilds(n: Nat) -> List<&2, T.Bt>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      T.BtWild{} <> fd.wilds(p)

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

# local bindings in front of a body (some: a statement is written already;
# a local function's %ldef is not one, fd.def.of takes it out)
def fd.lets.go(bs: List<&2, R>, b: T.Bt, +env: Env, some: Bool) -> T.Bt:
  match bs:
    case RB{x, v} <> t:
      T.BtLet{x, fd.expr(v), fd.lets.go(t, b, env, True{})}
    case RLf{x, tys, res, cls} <> t:
      T.BtLet{S.b("_"), fd.ldef.of(x, tys, res, cls, env), fd.lets.go(t, b, env, some)}
    case RT{v} <> t:
      T.BtLet{S.b("_"), v, fd.lets.go(t, b, env, True{})}
    case _ <> t:
      T.BtLet{S.b("_"), fd.todo("fold:local-binding"), fd.lets.go(t, b, env, True{})}
    case Nil{}:
      fd.lets.end(some, b, env)

def fd.lets(bs: List<&2, R>, b: T.Bt, +env: Env) -> T.Bt:
  fd.lets.go(bs, b, env, False{})

# a local binding: a value (a fun with no arguments) is a let, lifted when
# its body is a statement; a local function is lifted (RLf)
def fd.lbind(+x: List<&2, U32>, r: R, +env: Env) -> R:
  match r:
    case RMs{Nil{}, +res, +cls}:
      RB{x, T.BtAnn{fd.lam.if(fd.lam.flat(cls), Nil{}, res, cls, env), res}}
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
    case _ <> t:
      fd.rlf.names(t)
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

def fd.eif(c: R, a: R, b: R, +env: Env) -> R:
  RE{fd.et(fd.if(fd.env.res(env), fd.ex(c, env), fd.ex(a, env), fd.ex(b, env)))}

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

# a type applied to more arguments (a synonym of fewer variables than its
# use has arguments: type M = State Meter, used as M ())
def fd.ty.app.if(st: Bool, +n: List<&2, U32>, a: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match st:
    case True{}:
      fd.ty.state(List.append(&2, T.Bt, fd.spine(a), args))
    case False{}:
      T.BtTyApp{n, T.tba.args(List.append(&2, T.Bt, fd.spine(a), args))}

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
      fd.tc.imp(fd.ix.find(fd.env.ix(env), key))
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

def fd.pnlit(+v: X.Sx) -> R:
  RT{Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "int"), T.BtNat{X.tsx.atom.of(V.sv.at(v, 1n))}, fd.todo("fold:literal-pattern"))}

def fd.plit(+v: X.Sx) -> R:
  RT{Bool.pick(T.Bt, V.sv.is(V.sv.hd(v), "char"), fd.char(X.tsx.nat(V.sv.at(v, 1n))), fd.todo("fold:literal-pattern"))}

def fd.selfname(+v: X.Sx) -> List<&2, U32>:
  fd.bpick(V.sv.is(V.sv.hd(v), "g"), V.sv.str(v, 2n), V.sv.str(v, 1n))

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
  KAbs1{}
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
  [Kt{"g", KEg{}}, Kt{"l", KEl{}}, Kt{"self", KEself{}}, Kt{"app", KEapp{}}, Kt{"tyapp", KEtyapp{}}, Kt{"evapp", KEevapp{}}, Kt{"cast", KEskip1{}}, Kt{"expanded", KEskip2{}}, Kt{"tylam", KEskip2{}}, Kt{"evlam", KEskip2{}}, Kt{"evlet", KEskip2{}}, Kt{"olit", KEolit{}}, Kt{"char", KEchar{}}, Kt{"string", KEstring{}}, Kt{"lam", KElam{}}, Kt{"tuple", KEtuple{}}, Kt{"case", KEcase{}}, Kt{"if", KEif{}}, Kt{"multiif", KEmultiif{}}, Kt{"let", KElet{}}, Kt{"list", KElist{}}, Kt{"reccon", KEreccon{}}]

def fd.k.bad(s: String, +h: List<&2, U32>) -> K:
  KBad{fd.cat(S.b(s), h)}

# the refinements: a constructor pattern with fields, a negative literal,
# a case on a computed value, \case
def fd.k.pat(k: K, +x: X.Sx) -> K:
  match k:
    case KPcon{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 3n)), "args"), KPcon{}, KPconF{})
    case KPnlit{}:
      Bool.pick(K, V.sv.is(X.tsx.atom.of(V.sv.at(x, 2n)), "pos"), KPnlit{}, KBad{S.b("int-sub")})
    case k1:
      k1

def fd.k.ex(k: K, +x: X.Sx) -> K:
  match k:
    case KEcase{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 1n)), "l"), KEcase{}, KEcaseC{})
    case KElam{}:
      Bool.pick(K, V.sv.is(X.tsx.atom.of(V.sv.at(x, 1n)), "single"), KElam{}, KBad{S.b("fold:lambda-case")})
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
  Bool.pick(K, V.sv.is(V.sv.hd(x), "fun"), KBfun{}, Bool.pick(K, V.sv.is(V.sv.hd(x), "abs"), fd.k.abs(x), fd.k.bad("fold:local-", V.sv.hd(x))))

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
    case X.SxCons{_, X.SxCons{+g, X.SxCons{_, X.SxCons{X.SxCons{_, ps}, _}}}} KPcon{}:
      fd.pcon(g, fd.go(ps, KPs{}, env), env)
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
    case X.SxCons{_, X.SxCons{X.SxCons{_, X.SxCons{+v, _}}, _}} KPnlit{}:
      fd.pnlit(v)
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
      RE{fd.e0(HdSelf{fd.selfname(v)})}
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
    case X.SxCons{+b, X.SxNil{}} KAbs1{}:
      fd.go(b, fd.k.bind(b), env)
    case _ KAbs1{}:
      fd.bad(S.b("fold:local-group"))
    case X.SxCons{_, X.SxCons{+v, X.SxCons{_, X.SxCons{_, X.SxCons{ms, _}}}}} KBfun{}:
      fd.lbind(fd.bvname(X.SxCons{X.SxAtom{S.b("bv")}, X.SxCons{fd.unself(v), X.SxNil{}}}), fd.go(ms, KMatches{}, fd.notail(env)), env)
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
def fd.datas.if(d: Bool, +x: X.Sx, +env: Env, acc: List<&2, Got>) -> List<&2, Got>:
  match d:
    case True{}:
      fd.got.def(V.sv.str(x, 1n), fd.data(x, env)) <> List.append(&2, Got, fd.sels(x, env), acc)
    case False{}:
      acc

def fd.datas(xs: List<&2, X.Sx>, +env: Env) -> List<&2, Got>:
  match xs:
    case +h <> t:
      fd.datas.if(fd.isdata(h), h, env, fd.datas(t, env))
    case Nil{}:
      Nil{}

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

# whether the binding is one a user wrote (not GHC's $-names)
def fd.tb.user(+tb: Tb) -> Bool:
  Bool.not(V.sv.dollar(fd.tb.name(tb)))

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

def fd.fr.one(+key: List<&2, U32>, r: Fr) -> Fr:
  match r:
    case FrCopy{}:
      FrCopy{}
    case FrRec{}:
      Bool.pick(Fr, fd.is(key, "GHC.Internal.Maybe.Maybe"), FrMaybe{FrRec{}}, FrIn{key})
    case r1:
      Bool.pick(Fr, fd.is(key, "GHC.Internal.Maybe.Maybe"), FrMaybe{r1}, FrNo{})

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
  Cg{fz: List<&2, Fz>, n: List<&2, U32>, tas: List<&2, T.Bt>, cof: Bool}

def fd.cg.fz(+c: Cg) -> List<&2, Fz>:
  match c:
    case Cg{fz, n, tas, cof}:
      fz

def fd.cg.call(+c: Cg, +v: List<&2, U32>) -> T.Bt:
  match c:
    case Cg{fz, n, tas, cof}:
      T.tba.call(T.BtVar{n}, List.append(&2, T.Bt, tas, T.BtVar{v} <> Nil{}))

def fd.cg.leaf.of(cof: Bool, v: T.Bt) -> T.Bt:
  match cof:
    case True{}:
      T.BtExpr{T.tba.call(T.BtVar{S.b("alg")}, [T.BtCon{S.b("HsPrelude.CofreeF.CofreeF"), T.tba.args([T.BtVar{S.b("w0")}, v])}])}
    case False{}:
      T.BtExpr{T.tba.call(T.BtVar{S.b("alg")}, [v])}

def fd.cg.leaf(+c: Cg, vs: List<&2, T.Bt>) -> T.Bt:
  match c vs:
    case Cg{fz, n, tas, cof} v <> Nil{}:
      fd.cg.leaf.of(cof, v)
    case _ _:
      fd.todo("fold:cata-shape")

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
    case 1n+p CwB{+b, +n} <> rest:
      fd.cg(p, rest, fd.cg.build(b, n, vs), k, c)
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

# ~A: Data for each
def fd.tvtpls(tvs: List<&2, List<&2, U32>>) -> List<&2, T.BParam>:
  match tvs:
    case Nil{}:
      Nil{}
    case h <> t:
      T.BParam{T.BmTpl{}, h, fd.v("Data")} <> fd.tvtpls(t)

def fd.cata.doc(cof: Bool, +b: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match cof:
    case True{}:
      [fd.cat3(S.b("generated: Data.Functor.Foldable.cata at Cofree "), b, S.b(" w (Base: CofreeF)"))]
    case False{}:
      [fd.cat(S.b("generated: Data.Functor.Foldable.cata at Fix "), b)]

# G.cata (cof False) or G.cata.cofree (cof True)
def fd.cata.def(+cof: Bool, z: Fz, +fz: List<&2, Fz>) -> T.BItem:
  match z:
    case Fz{k, +b, +tvs, +cs}:
      +name = fd.cat(b, fd.bpick(cof, S.b(".cata.cofree"), S.b(".cata")))
      +tas = fd.tvbts(tvs)
      +lam = {T.BtLam{T.BmLive{}, fd.rv(), T.BtTyApp{b, T.tba.args(List.append(&2, T.Bt, tas, T.BtVar{fd.rv()} <> Nil{}))}} : T.Bt}
      +r = {T.BtVar{S.b("R_c")} : T.Bt}
      +w = {T.BtVar{S.b("W_c")} : T.Bt}
      +layer = Bool.pick(T.Bt, cof, T.BtTyApp{S.b("HsPrelude.CofreeF"), T.tba.args([lam, w, r])}, T.BtTyApp{b, T.tba.args(List.append(&2, T.Bt, tas, r <> Nil{}))})
      +xty = Bool.pick(T.Bt, cof, T.BtTyApp{S.b("HsPrelude.Cofree"), T.tba.args([lam, w])}, T.BtTyApp{S.b("HsPrelude.Fix"), T.tba.args([lam])})
      +wp = Bool.pick(List<&2, T.BParam>, cof, [T.BParam{T.BmTpl{}, S.b("W_c"), fd.v("Data")}], Nil{})
      +ps = List.append(&2, T.BParam, fd.tvtpls(tvs), List.append(&2, T.BParam, wp, [T.BParam{T.BmTpl{}, S.b("R_c"), fd.v("Data")}, T.BParam{T.BmTpl{}, S.b("alg"), T.BtPi{T.BmLive{}, S.b("_"), False{}, layer, r}}, T.BParam{T.BmLive{}, S.b("x"), xty}]))
      +targs = fd.tpls(List.append(&2, T.Bt, tas, List.append(&2, T.Bt, Bool.pick(List<&2, T.Bt>, cof, [w], Nil{}), [r, T.BtVar{S.b("alg")}])))
      +pat = Bool.pick(T.Bt, cof, T.BtCon{S.b("HsPrelude.Cofree.Cofree"), T.tba.args([T.BtPv{T.BmLive{}, S.b("w0")}, T.BtPv{T.BmLive{}, S.b("y0")}])}, T.BtCon{S.b("HsPrelude.Fix.Fix"), T.tba.args([T.BtPv{T.BmLive{}, S.b("y0")}])})
      +inner = fd.cg(4096n, CwC{S.b("y0"), cs} <> Nil{}, Nil{}, 1n, Cg{fz, name, targs, cof})
      T.BiDef{name, ps, r, T.BtMatch{T.tba.args([T.BtVar{S.b("x")}]), T.BtCase{T.tba.args([pat]), fd.cg.match(S.b("y0"), inner), T.BtCEnd{}}}, fd.cata.doc(cof, b)}

def fd.fz.k(z: Fz) -> List<&2, U32>:
  match z:
    case Fz{k, b, tvs, cs}:
      k

def fd.fz.b(z: Fz) -> List<&2, U32>:
  match z:
    case Fz{k, b, tvs, cs}:
      b

def fd.cata.got(ok: Bool, +z: Fz, +fz: List<&2, Fz>) -> List<&2, Got>:
  match ok:
    case True{}:
      +b = fd.fz.b(z)
      [fd.got.def(fd.cat(b, S.b(".cata")), fd.cata.def(False{}, z, fz)), fd.got.def(fd.cat(b, S.b(".cata.cofree")), fd.cata.def(True{}, z, fz))]
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
def fd.allgots(+xs: List<&2, X.Sx>, +tbs: List<&2, Tb>, +env: Env) -> List<&2, Got>:
  +ds = List.append(&2, Got, fd.datas(xs, env), fd.catas(xs, env))
  List.append(&2, Got, ds, fd.gots.less(fd.gots(tbs, fd.ok(xs, fd.px.imp(fd.env.px(env))), env), fd.got.defnames(ds)))

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
  "# Written by cata: the recursion-scheme types of Haskell's data-fix and free\n# (Data.Fix, Control.Comonad.Cofree, Control.Comonad.Trans.Cofree), each\n# with its functor as a type function, and recursion-schemes' project and\n# embed at them (Data.Functor.Foldable).\nimport Base\n\n# Fix f: a layer of f whose holes are Fix f again\ntype Fix<-F: Data -> Data> is Data:\n  Fix.Fix{unFix: F(Fix<F>)}\n\n# Cofree f a: a :< f (Cofree f a), a layer of f under an annotation\ntype Cofree<-F: Data -> Data, -A: Data> is Data:\n  Cofree.Cofree{head: A, tail: F(Cofree<F, A>)}\n\n# CofreeF f a b: a :< f b, Cofree f a's base functor\ntype CofreeF<-F: Data -> Data, -A: Data, -B: Data> is Data:\n  CofreeF.CofreeF{head: A, tail: F(B)}\n\ndef Fix.unFix(-F: Data -> Data, x: Fix<F>) -> F(Fix<F>):\n  match x:\n    case Fix.Fix{y}:\n      y\n\ndef Cofree.project(-F: Data -> Data, -A: Data, x: Cofree<F, A>) -> CofreeF<F, A, Cofree<F, A>>:\n  match x:\n    case Cofree.Cofree{h, t}:\n      CofreeF.CofreeF{h, t}\n\ndef Cofree.embed(-F: Data -> Data, -A: Data, x: CofreeF<F, A, Cofree<F, A>>) -> Cofree<F, A>:\n  match x:\n    case CofreeF.CofreeF{h, t}:\n      Cofree.Cofree{h, t}\n"

def fd.hsprelude.write(+out: String) -> IO(Unit):
  S.write(out ++ "/HsPrelude.bend", S.b(fd.hsprelude()))

# the files a module's text may name: HsPrelude's and the package's
# earlier modules'
def fd.ims(+px: Px) -> List<&2, List<&2, U32>>:
  S.b("HsPrelude") <> fd.px.files(px)

def fd.uses.name(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case +h <> t:
      Bool.or(S.mem(n, T.tba.item.fold(~T.tba.refs, h, Nil{})), fd.uses.name(t, n))
    case Nil{}:
      False{}

# Maybe's and Either's monad and functions Base lacks (Base has Maybe.bind,
# Maybe.map and Maybe.default)
def fd.pre.either.bind() -> String:
  "# Either's >>= (a Left stops the rest)\ndef hs.either.bind(-E: Data, -A: Data, -B: Data, m: Either<&2, &2, E, A>, f: A -> Either<&2, &2, E, B>) -> Either<&2, &2, E, B>:\n  match m:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      f(a)\n\n"

def fd.pre.either.map() -> String:
  "# Either's fmap\ndef hs.either.map(-E: Data, -A: Data, -B: Data, f: A -> B, m: Either<&2, &2, E, A>) -> Either<&2, &2, E, B>:\n  match m:\n    case Inl{e}:\n      Inl{e}\n    case Inr{a}:\n      Inr{f(a)}\n\n"

def fd.pre.maybe() -> String:
  "# Haskell's maybe\ndef hs.maybe(-A: Data, -B: Data, d: B, f: A -> B, m: Maybe<&2, A>) -> B:\n  match m:\n    case None{}:\n      d\n    case Some{x}:\n      f(x)\n\n"

def fd.pre.either() -> String:
  "# Haskell's either\ndef hs.either(-A: Data, -B: Data, -C: Data, f: A -> C, g: B -> C, e: Either<&2, &2, A, B>) -> C:\n  match e:\n    case Inl{a}:\n      f(a)\n    case Inr{b}:\n      g(b)\n\n"

def fd.pre.state() -> String:
  "# State s a (Control.Monad.Trans.State): S -> A & S, a function of the\n# state to a result and the next state; mtl's MonadState methods at it\ndef hs.state.bind.go(-S: Data, -A: Type, -B: Type, p: Sigma<&1, &1, A, _ => S>, f: A -> S -> Sigma<&1, &1, B, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (a, s) = p\n  f(a)(s)\n\ndef hs.state.bind(-S: Data, -A: Type, -B: Type, m: S -> Sigma<&1, &1, A, _ => S>, f: A -> S -> Sigma<&1, &1, B, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.bind.go(S, A, B, m(s), f)\n\ndef hs.state.pure(-S: Data, -A: Type, a: A) -> S -> Sigma<&1, &1, A, _ => S>:\n  s => (a, s)\n\ndef hs.state.map.go(-S: Data, -A: Type, -B: Type, f: A -> B, p: Sigma<&1, &1, A, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (a, s) = p\n  (f(a), s)\n\ndef hs.state.map(-S: Data, -A: Type, -B: Type, f: A -> B, m: S -> Sigma<&1, &1, A, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.map.go(S, A, B, f, m(s))\n\ndef hs.state.ap.go(-S: Data, -A: Type, -B: Type, p: Sigma<&1, &1, (A -> B), _ => S>, m: S -> Sigma<&1, &1, A, _ => S>) -> Sigma<&1, &1, B, _ => S>:\n  (f, s) = p\n  hs.state.map.go(S, A, B, f, m(s))\n\ndef hs.state.ap(-S: Data, -A: Type, -B: Type, mf: S -> Sigma<&1, &1, (A -> B), _ => S>, m: S -> Sigma<&1, &1, A, _ => S>) -> S -> Sigma<&1, &1, B, _ => S>:\n  s => hs.state.ap.go(S, A, B, mf(s), m)\n\ndef hs.state.dup(-S: Data, +s: S) -> Sigma<&1, &1, S, _ => S>:\n  (s, s)\n\ndef hs.state.get(-S: Data) -> S -> Sigma<&1, &1, S, _ => S>:\n  s => hs.state.dup(S, s)\n\ndef hs.state.put(-S: Data, s: S) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  _ => (Unit{}, s)\n\ndef hs.state.modify(-S: Data, f: S -> S) -> S -> Sigma<&1, &1, Unit, _ => S>:\n  s => (Unit{}, f(s))\n\ndef hs.state.gets.go(-S: Data, -A: Type, f: S -> A, +s: S) -> Sigma<&1, &1, A, _ => S>:\n  (f(s), s)\n\ndef hs.state.gets(-S: Data, -A: Type, f: S -> A) -> S -> Sigma<&1, &1, A, _ => S>:\n  s => hs.state.gets.go(S, A, f, s)\n\ndef hs.state.fst(-S: Data, -A: Type, p: Sigma<&1, &1, A, _ => S>) -> A:\n  (a, s) = p\n  a\n\ndef hs.state.snd(-S: Data, -A: Type, p: Sigma<&1, &1, A, _ => S>) -> S:\n  (a, s) = p\n  s\n\ndef hs.state.re(-S: Data, -A: Data, p: Sigma<&1, &1, A, _ => S>) -> Sigma<&2, &2, A, _ => S>:\n  (a, s) = p\n  (a, s)\n\ndef hs.state.eval(-S: Data, -A: Type, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> A:\n  hs.state.fst(S, A, m(s))\n\ndef hs.state.exec(-S: Data, -A: Type, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> S:\n  hs.state.snd(S, A, m(s))\n\ndef hs.state.run(-S: Data, -A: Data, m: S -> Sigma<&1, &1, A, _ => S>, s: S) -> Sigma<&2, &2, A, _ => S>:\n  hs.state.re(S, A, m(s))\n\n"

# whether the items name any of ns
def fd.uses.any(+its: List<&2, T.BItem>, ns: List<String>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case n <> t:
      Bool.or(fd.uses.name(its, S.b(n)), fd.uses.any(its, t))

def fd.pre.one(+its: List<&2, T.BItem>, n: String, text: String) -> List<&2, U32>:
  fd.bpick(fd.uses.name(its, S.b(n)), S.b(text), Nil{})

def fd.prelude(+its: List<&2, T.BItem>) -> List<&2, U32>:
  List.concat(&2, U32, [fd.pre.one(its, "Bool.if", fd.pre.if()), fd.pre.one(its, "hs.map", fd.pre.map()), fd.pre.one(its, "hs.either.bind", fd.pre.either.bind()), fd.pre.one(its, "hs.either.map", fd.pre.either.map()), fd.pre.one(its, "hs.maybe", fd.pre.maybe()), fd.pre.one(its, "hs.either", fd.pre.either()), fd.bpick(fd.uses.any(its, ["hs.state.bind", "hs.state.pure", "hs.state.map", "hs.state.ap", "hs.state.get", "hs.state.put", "hs.state.modify", "hs.state.gets", "hs.state.eval", "hs.state.exec", "hs.state.run"]), S.b(fd.pre.state()), Nil{})])

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

# A drop: the item's name and why.
type Dr is Data:
  Dr{n: List<&2, U32>, why: List<&2, U32>}

type Split is Data:
  Split{keep: List<&2, T.BItem>, out: List<&2, Dr>}

def fd.split.if(hit: Bool, +it: T.BItem, +why: List<&2, U32>, s: Split) -> Split:
  match hit s:
    case True{} Split{k, o}:
      Split{k, Dr{fd.item.name(it), why} <> o}
    case False{} Split{k, o}:
      Split{it <> k, o}

# the items that mention a name gone go too, and the defs lifted out of one
# (see Lifting)
def fd.split(its: List<&2, T.BItem>, +gone: List<&2, List<&2, U32>>, +why: List<&2, U32>) -> Split:
  match its:
    case +h <> t:
      fd.split.if(Bool.or(fd.hits(h, gone), S.mem(fd.liftof(h), gone)), h, why, fd.split(t, gone, why))
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

def fd.bpicks(c: Bool, a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  Bool.pick(List<&2, List<&2, U32>>, c, a, b)

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

# one round's verdict: done when Bend accepts the file
def fd.gate.step(g: Gs, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>, +out: List<&2, U32>) -> Gs:
  match g:
    case Gs{its, o, True{}}:
      Gs{its, o, True{}}
    case Gs{+its, +o, False{}}:
      +ls = S.split(out, 10)
      Bool.pick(Gs, S.prefix(out, S.b("ALL PROOFS CHECK")), Gs{its, o, True{}}, fd.gate.drop(fd.gate.who(fd.errline(ls), fd.render(file, m, ims, its)), its, o, fd.cat(S.b("check:"), fd.errwhy(ls))))

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
# check again, until Bend accepts the file or nothing is left
def fd.gate(fuel: Nat, g: Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>, +ims: List<&2, List<&2, U32>>) -> IO(Gs):
  match fuel:
    case 0n:
      IO.pure(Gs, g)
    case 1n+p:
      +g1 = g
      do IO<Gs>:
        o : S.Out <- fd.gate.io(g1, bend, path, file, m, ims)
        fd.gate(p, fd.gate.step(g1, file, m, ims, S.Out.text(o)), bend, path, file, m, ims)

# The module -------------------------------------------------------------------------

def fd.got.items(gs: List<&2, Got>) -> List<&2, T.BItem>:
  match gs:
    case GotDef{n, it} <> t:
      it <> fd.got.items(t)
    case _ <> t:
      fd.got.items(t)
    case Nil{}:
      Nil{}

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
      fd.cat(S.join([file, n, S.b("ok-type"), Nil{}], 9), 10 <> fd.ledger.ok(file, t))
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

# the names the template arguments in t use
def fd.tas(t: T.Bt, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtTplArg{a}:
      T.tba.frees(a, acc)
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

# a let's name without the + fd.mark gave it
def fd.unplus(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case 43 <> t:
      t
    case u:
      u

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
def fd.px.add(p: Px, +m: List<&2, U32>, +alias: List<&2, U32>, wrote: Bool, ix: List<&2, Ix>, sy: List<&2, Sy>, tf: List<&2, Tf>) -> Px:
  match p:
    case Px{h, f, i, s, t}:
      Px{m <> h, fd.files.if(wrote, alias, f), List.append(&2, Ix, ix, i), List.append(&2, Sy, sy, s), List.append(&2, Tf, tf, t)}

# in package mode, the package after the module; a module alone gives nothing
def fd.px.next(pkg: Bool, +p: Px, +m: List<&2, U32>, +alias: List<&2, U32>, +xs: List<&2, X.Sx>, +gs: List<&2, Got>, +tfs: List<&2, Tf>, +cs: List<&2, Ctr>, +ds: List<&2, Df>, +kept: List<&2, T.BItem>) -> Px:
  match pkg:
    case True{}:
      +names = fd.its.names(kept)
      fd.px.add(p, m, alias, fd.wrote(True{}, kept), List.append(&2, Ix, fd.iface.fzs(fd.fzs(xs, m), alias, names), fd.iface(gs, m, alias, names, cs, ds)), fd.iface.syns(xs, m), fd.iface.tfs(tfs, alias, names))
    case False{}:
      p

def fd.gs.its(g: Gs) -> List<&2, T.BItem>:
  match g:
    case Gs{k, o, d}:
      k

# the items that use a binding that is out go too, before the first check
def fd.predrop(+its: List<&2, T.BItem>, +outs: List<&2, Dr>) -> Gs:
  +s = fd.closure(List.length(&2, T.BItem, its), fd.split(its, fd.dr.names(outs), S.b("dep")), S.b("dep"), outs)
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
  +its = fd.got.items(gs)
  +ims = fd.ims(px)
  +path = out ++ "/" ++ S.str(base) ++ ".bend"
  +try = out ++ "/" ++ S.str(base) ++ "_try.bend"
  do IO<Px>:
    fd.hsprelude.write(out)
    +g : Gs <- fd.gate(Bool.pick(Nat, Nat.is_eq(rounds, 0n), 1n+List.length(&2, T.BItem, its), rounds), fd.predrop(its, fd.got.outs(gs)), bend, try, file, m, ims)
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
