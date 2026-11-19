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
  TkNone{}

type TkE is Data:
  TkE{k: String, v: Tk}

def fd.tktab() -> List<&2, TkE>:
  [TkE{"GHC.Types.Int", TkNat{}}, TkE{"GHC.Num.Integer.Integer", TkNat{}}, TkE{"GHC.Num.Natural.Natural", TkNat{}}, TkE{"GHC.Types.Bool", TkBool{}}, TkE{"GHC.Types.Char", TkChar{}}, TkE{"GHC.Types.Float", TkF32{}}, TkE{"GHC.Types.List", TkList{}}, TkE{"GHC.Internal.Base.String", TkStr{}}, TkE{"GHC.Internal.IO.FilePath", TkStr{}}, TkE{"GHC.Internal.Maybe.Maybe", TkMaybe{}}, TkE{"GHC.Internal.Data.Either.Either", TkEither{}}, TkE{"GHC.Tuple.Tuple2", TkT2{}}, TkE{"GHC.Tuple.Tuple3", TkT3{}}, TkE{"GHC.Tuple.Unit", TkUnit{}}, TkE{"GHC.Types.Ordering", TkCmp{}}]

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

def fd.tc.of(k: Tk, own: Bool, +n: List<&2, U32>, +key: List<&2, U32>, args: List<&2, T.Bt>) -> T.Bt:
  match k own:
    case TkNat{} _:
      fd.ty0("Nat")
    case TkBool{} _:
      fd.ty0("Bool")
    case TkChar{} _:
      fd.ty0("Char")
    case TkF32{} _:
      fd.ty0("F32")
    case TkStr{} _:
      fd.list(fd.ty0("Char"))
    case TkUnit{} _:
      fd.ty0("Unit")
    case TkCmp{} _:
      fd.ty0("Cmp")
    case TkList{} _:
      fd.ty.list(args)
    case TkMaybe{} _:
      T.BtTyApp{S.b("Maybe"), T.tba.args(fd.v("&2") <> args)}
    case TkEither{} _:
      T.BtTyApp{S.b("Either"), T.tba.args(fd.v("&2") <> fd.v("&2") <> args)}
    case TkT2{} _:
      fd.ty.t2(args)
    case TkT3{} _:
      fd.ty.t3(args)
    case TkNone{} True{}:
      T.BtTyApp{fd.tyname(n), T.tba.args(args)}
    case TkNone{} False{}:
      T.BtTodo{fd.cat(S.b("type:"), key)}

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
  CbNone{}

type CbE is Data:
  CbE{k: String, v: Cb}

def fd.cbtab() -> List<&2, CbE>:
  [CbE{"GHC.Types.:", CbCons{}}, CbE{"GHC.Types.[]", CbNil{}}, CbE{"GHC.Types.True", CbTrue{}}, CbE{"GHC.Types.False", CbFalse{}}, CbE{"GHC.Internal.Maybe.Just", CbJust{}}, CbE{"GHC.Internal.Maybe.Nothing", CbNothing{}}, CbE{"GHC.Internal.Data.Either.Left", CbLeft{}}, CbE{"GHC.Internal.Data.Either.Right", CbRight{}}, CbE{"GHC.Types.LT", CbLT{}}, CbE{"GHC.Types.EQ", CbEQ{}}, CbE{"GHC.Types.GT", CbGT{}}, CbE{"GHC.Tuple.()", CbUnit{}}, CbE{"GHC.Tuple.(,)", CbT2{}}, CbE{"GHC.Tuple.(,,)", CbT3{}}]

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
    case _ _:
      fd.todo("fold:constructor")

# The module's own names ----------------------------------------------------

# a constructor of the module: its name, its type's, its arity
type Ctr is Data:
  Ctr{c: List<&2, U32>, t: List<&2, U32>, n: Nat}

# a def of the module (its Haskell name) and its arity
type Df is Data:
  Df{n: List<&2, U32>, a: Nat}

def fd.ctr.find(xs: List<&2, Ctr>, +c: List<&2, U32>) -> Maybe<&2, Ctr>:
  match xs:
    case Nil{}:
      None{}
    case Ctr{+k, t, n} <> rest:
      Bool.pick(Maybe<&2, Ctr>, S.eq(k, c), Some{Ctr{k, t, n}}, fd.ctr.find(rest, c))

def fd.df.find(xs: List<&2, Df>, +n: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Df{k, a} <> rest:
      Bool.pick(Maybe<&2, Nat>, S.eq(k, n), Some{a}, fd.df.find(rest, n))

# What the fold knows where it is: the module's name, constructors and
# defs, the type of the right-hand side it is in (None in an argument),
# the type arguments a recursive call passes, the locals in scope, and the
# module's type synonyms.

# a type synonym of the module: its Haskell name, its type variables, and
# its right-hand side, folded
type Syn is Data:
  Syn{n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, body: T.Bt}

type Env is Data:
  Env{m: List<&2, U32>, cons: List<&2, Ctr>, defs: List<&2, Df>, res: Maybe<&2, T.Bt>, self: List<&2, T.Bt>, ls: List<&2, List<&2, U32>>, syn: List<&2, Syn>}

def fd.env.m(e: Env) -> List<&2, U32>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      m

def fd.env.cons(e: Env) -> List<&2, Ctr>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      c

def fd.env.defs(e: Env) -> List<&2, Df>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      d

def fd.env.res(e: Env) -> Maybe<&2, T.Bt>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      r

def fd.env.self(e: Env) -> List<&2, T.Bt>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      s

def fd.env.ls(e: Env) -> List<&2, List<&2, U32>>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      l

def fd.env.syn(e: Env) -> List<&2, Syn>:
  match e:
    case Env{m, c, d, r, s, l, y}:
      y

def fd.withsyn(e: Env, ys: List<&2, Syn>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y}:
      Env{m, c, d, r, s, l, ys}

def fd.withres(e: Env, t: T.Bt) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y}:
      Env{m, c, d, Some{t}, s, l, y}

def fd.notail(e: Env) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y}:
      Env{m, c, d, None{}, s, l, y}

def fd.addls(e: Env, xs: List<&2, List<&2, U32>>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y}:
      Env{m, c, d, r, s, List.append(&2, List<&2, U32>, xs, l), y}

def fd.withself(e: Env, ts: List<&2, T.Bt>) -> Env:
  match e:
    case Env{m, c, d, r, s, l, y}:
      Env{m, c, d, r, ts, l, y}

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
  BfNone{}

type BfE is Data:
  BfE{k: String, v: Bf}

def fd.bftab() -> List<&2, BfE>:
  [BfE{"GHC.Classes.==", BfCmp{"is_eq"}}, BfE{"GHC.Classes./=", BfCmp{"is_ne"}}, BfE{"GHC.Classes.<", BfCmp{"is_lt"}}, BfE{"GHC.Classes.<=", BfCmp{"is_le"}}, BfE{"GHC.Classes.>", BfCmp{"is_gt"}}, BfE{"GHC.Classes.>=", BfCmp{"is_ge"}}, BfE{"GHC.Classes.compare", BfCmp{"cmp"}}, BfE{"GHC.Classes.max", BfCmp{"max"}}, BfE{"GHC.Classes.min", BfCmp{"min"}}, BfE{"GHC.Classes.&&", BfAnd{}}, BfE{"GHC.Classes.||", BfOr{}}, BfE{"GHC.Classes.not", BfNot{}}, BfE{"GHC.Internal.Base.otherwise", BfTrue{}}, BfE{"GHC.Internal.Num.+", BfNum{"add"}}, BfE{"GHC.Internal.Num.*", BfNum{"mul"}}, BfE{"GHC.Internal.Real.div", BfNum{"div"}}, BfE{"GHC.Internal.Real.mod", BfNum{"mod"}}, BfE{"GHC.Internal.Real.quot", BfNum{"div"}}, BfE{"GHC.Internal.Real.rem", BfNum{"mod"}}, BfE{"GHC.Internal.Real.^", BfNum{"pow"}}, BfE{"GHC.Internal.Real./", BfNum{"div"}}, BfE{"GHC.Internal.Base.++", BfAppend{}}, BfE{"GHC.Internal.Data.Foldable.length", BfLength{}}, BfE{"GHC.Internal.Data.Foldable.null", BfNull{}}, BfE{"GHC.Internal.List.reverse", BfReverse{}}, BfE{"GHC.Internal.Data.Foldable.concat", BfConcat{}}, BfE{"GHC.Internal.List.take", BfTake{}}, BfE{"GHC.Internal.List.drop", BfDrop{}}, BfE{"GHC.Internal.List.replicate", BfReplicate{}}, BfE{"GHC.Internal.Base.map", BfMap{}}, BfE{"GHC.Internal.List.filter", BfFilter{}}, BfE{"GHC.Internal.Data.Foldable.any", BfAny{}}, BfE{"GHC.Internal.Data.Foldable.all", BfAll{}}, BfE{"GHC.Internal.Data.Foldable.foldr", BfFoldr{}}, BfE{"GHC.Internal.Data.Foldable.foldl", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.foldl'", BfFoldl{}}, BfE{"GHC.Internal.Data.Foldable.elem", BfElem{}}, BfE{"GHC.Internal.Data.Foldable.sum", BfSum{}}, BfE{"GHC.Internal.Data.Foldable.product", BfProduct{}}, BfE{"GHC.Internal.Data.Foldable.and", BfAndL{}}, BfE{"GHC.Internal.Data.Foldable.or", BfOrL{}}, BfE{"GHC.Internal.Data.Foldable.concatMap", BfConcatMap{}}, BfE{"GHC.Internal.Show.show", BfShow{}}, BfE{"GHC.Internal.Base.id", BfId{}}, BfE{"GHC.Internal.Base.const", BfConst{}}, BfE{"GHC.Internal.Enum.succ", BfSucc{}}]

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
    case Some{Ctr{+c, +t, +n}}:
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

def fd.own.g(var: Bool, con: Bool, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match var con:
    case True{} _:
      fd.own(fd.df.find(fd.env.defs(env), n), fd.vname(n), tys, all)
    case False{} True{}:
      fd.ucon(fd.ctr.find(fd.env.cons(env), n), all)
    case False{} False{}:
      T.BtTodo{fd.cat(S.b("fold:"), k)}

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

def fd.global(own: Bool, +m: List<&2, U32>, +n: List<&2, U32>, +k: List<&2, U32>, +tys: List<&2, T.Bt>, +all: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match own:
    case True{}:
      fd.own.g(fd.is(k, "var"), fd.is(k, "con"), n, k, tys, all, env)
    case False{}:
      +key = fd.cat3(m, S.b("."), n)
      fd.bglobal(fd.is(k, "con"), key, tys, all, env)

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
    case Some{Ctr{+c, +t, n}}:
      T.BtCon{fd.cname(t, c), T.tba.args(ps)}
    case None{}:
      fd.todo("fold:unknown-constructor")

def fd.pcon.base(c: Cb, +key: List<&2, U32>, ps: List<&2, T.Bt>) -> T.Bt:
  match c:
    case CbNone{}:
      T.BtTodo{fd.cat(S.b("base:"), key)}
    case c1:
      fd.cb.mk(c1, ps)

def fd.pcon.of(own: Bool, +g: X.Sx, ps: List<&2, T.Bt>, +env: Env) -> T.Bt:
  match own:
    case True{}:
      fd.pcon.own(fd.ctr.find(fd.env.cons(env), V.sv.str(g, 2n)), ps)
    case False{}:
      fd.pcon.base(fd.cb.find(fd.cbtab(), fd.cat3(V.sv.str(g, 1n), S.b("."), V.sv.str(g, 2n))), fd.cat3(V.sv.str(g, 1n), S.b("."), V.sv.str(g, 2n)), ps)

# (pcon CON (ARGTYPE...) (args P...)): CON is (g MOD NAME con)
def fd.pcon(+g: X.Sx, ps: R, +env: Env) -> R:
  RT{fd.pcon.of(S.eq(V.sv.str(g, 1n), fd.env.m(env)), g, fd.bts(fd.items(ps)), env)}

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

# a def from its name, its type variables and its clauses (an RMs)
def fd.def.of(+name: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, +tys: List<&2, T.Bt>, res: T.Bt, +cls: List<&2, R>) -> T.BItem:
  +pms = fd.pms(List.length(&2, T.Bt, tys), 0n, cls)
  +body = fd.mark(fd.body.of(fd.anysplit(pms), pms, cls))
  T.BiDef{fd.vname(name), List.append(&2, T.BParam, fd.tvparams(tvs), fd.params(pms, tys, body)), res, body, Nil{}}

def fd.def(+name: List<&2, U32>, +tvs: List<&2, List<&2, U32>>, r: R) -> T.BItem:
  match r:
    case RMs{tys, res, cls}:
      fd.def.of(name, tvs, tys, res, cls)
    case _:
      T.BiDef{fd.vname(name), Nil{}, fd.todo("fold:shape"), fd.todo("fold:shape"), Nil{}}

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

# local bindings in front of a body
def fd.lets(bs: List<&2, R>, b: T.Bt) -> T.Bt:
  match bs:
    case RB{x, v} <> t:
      T.BtLet{x, fd.expr(v), fd.lets(t, b)}
    case RT{v} <> t:
      T.BtLet{S.b("_"), v, fd.lets(t, b)}
    case _ <> t:
      T.BtLet{S.b("_"), fd.todo("fold:local-binding"), fd.lets(t, b)}
    case Nil{}:
      fd.stmt(b)

def fd.bnames(bs: List<&2, R>) -> List<&2, List<&2, U32>>:
  match bs:
    case RB{x, v} <> t:
      x <> fd.bnames(t)
    case _ <> t:
      fd.bnames(t)
    case Nil{}:
      Nil{}

# a local binding: a value (a fun with no arguments) is a let; a local
# function is not written yet
def fd.lbind(+x: List<&2, U32>, r: R) -> R:
  match r:
    case RMs{Nil{}, res, RC{Nil{}, b} <> Nil{}}:
      RB{x, T.BtAnn{fd.expr(b), res}}
    case _:
      RB{x, fd.todo("fold:local-function")}

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

def fd.lam(r: R) -> R:
  match r:
    case RMs{tys, res, RC{ps, b} <> Nil{}}:
      RE{fd.et(fd.lam.go(ps, b))}
    case _:
      fd.bad(S.b("fold:lambda"))

def fd.ecase.of(res: Maybe<&2, T.Bt>, +x: List<&2, U32>, cls: List<&2, R>) -> T.Bt:
  match res:
    case Some{r}:
      T.BtMatch{T.tba.args([T.BtVar{x}]), fd.cases(cls, [Pm{x, True{}}])}
    case None{}:
      fd.todo("fold:case-in-argument")

# case x of ..: a match on the local x
def fd.ecase(+x: List<&2, U32>, r: R, +env: Env) -> R:
  match r:
    case RMs{tys, res, cls}:
      RE{fd.et(fd.ecase.of(fd.env.res(env), x, cls))}
    case _:
      fd.bad(S.b("fold:case"))

def fd.eif(c: R, a: R, b: R, +env: Env) -> R:
  RE{fd.et(fd.if(fd.env.res(env), fd.ex(c, env), fd.ex(a, env), fd.ex(b, env)))}

def fd.elet.of(res: Maybe<&2, T.Bt>, bs: List<&2, R>, b: T.Bt) -> T.Bt:
  match res:
    case Some{r}:
      fd.lets(bs, b)
    case None{}:
      fd.todo("fold:let-in-argument")

def fd.elet(bs: R, e: R, +env: Env) -> R:
  RE{fd.et(fd.elet.of(fd.env.res(env), fd.items(bs), fd.ex(e, env)))}

def fd.grhss(bs: R, gs: R, +env: Env) -> R:
  RT{fd.lets(fd.items(bs), fd.chain(fd.items(gs), fd.env.res(env)))}

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

def fd.syn.fill(tvs: List<&2, List<&2, U32>>, body: T.Bt, args: List<&2, T.Bt>) -> T.Bt:
  match tvs args:
    case v <> t a <> u:
      fd.syn.fill(t, T.tba.subst(body, fd.cat(v, S.b("%")), a), u)
    case Nil{} Nil{}:
      body
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

def fd.tc.syn(found: Maybe<&2, Syn>, k: Tk, own: Bool, +n: List<&2, U32>, +key: List<&2, U32>, +args: List<&2, T.Bt>) -> T.Bt:
  match found:
    case Some{Syn{sn, +tvs, body}}:
      fd.syn.fill(tvs, fd.syn.mark(tvs, body), args)
    case None{}:
      fd.tc.of(k, own, n, key, args)

def fd.tc(+m: List<&2, U32>, +n: List<&2, U32>, args: R, +env: Env) -> R:
  +key = fd.cat3(m, S.b("."), n)
  +own = S.eq(m, fd.env.m(env))
  RT{fd.tc.syn(fd.syn.find(fd.syn.own(own, fd.env.syn(env)), n), fd.tk.find(fd.tktab(), key), own, n, key, fd.bts(fd.items(args)))}

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
  [Kt{"g", KEg{}}, Kt{"l", KEl{}}, Kt{"self", KEself{}}, Kt{"app", KEapp{}}, Kt{"tyapp", KEtyapp{}}, Kt{"evapp", KEevapp{}}, Kt{"cast", KEskip1{}}, Kt{"expanded", KEskip2{}}, Kt{"tylam", KEskip2{}}, Kt{"evlam", KEskip2{}}, Kt{"evlet", KEskip2{}}, Kt{"olit", KEolit{}}, Kt{"char", KEchar{}}, Kt{"string", KEstring{}}, Kt{"lam", KElam{}}, Kt{"tuple", KEtuple{}}, Kt{"case", KEcase{}}, Kt{"if", KEif{}}, Kt{"multiif", KEmultiif{}}, Kt{"let", KElet{}}, Kt{"list", KElist{}}]

def fd.k.bad(s: String, +h: List<&2, U32>) -> K:
  KBad{fd.cat(S.b(s), h)}

# the refinements: a constructor pattern with fields, a negative literal,
# a case on a computed value, \case
def fd.k.pat(k: K, +x: X.Sx) -> K:
  match k:
    case KPcon{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 3n)), "args"), KPcon{}, KBad{S.b("fold:record-pattern")})
    case KPnlit{}:
      Bool.pick(K, V.sv.is(X.tsx.atom.of(V.sv.at(x, 2n)), "pos"), KPnlit{}, KBad{S.b("int-sub")})
    case k1:
      k1

def fd.k.ex(k: K, +x: X.Sx) -> K:
  match k:
    case KEcase{}:
      Bool.pick(K, V.sv.is(V.sv.hd(V.sv.at(x, 1n)), "l"), KEcase{}, KBad{S.b("fold:case-of-computed")})
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
  Bool.pick(K, V.sv.is(V.sv.hd(x), "nonrec"), KNonrec{}, KBad{S.b("fold:recursive-local")})

# a local abs (GHC's generalised group) that takes no dictionary is its one
# bind (its type variables are erased in a let)
def fd.k.abs(+x: X.Sx) -> K:
  Bool.pick(K, Nat.is_eq(X.tsx.len(V.sv.at(x, 2n)), 0n), KBabs{}, KBad{S.b("fold:local-abs-class")})

def fd.k.bind(+x: X.Sx) -> K:
  Bool.pick(K, V.sv.is(V.sv.hd(x), "fun"), KBfun{}, Bool.pick(K, V.sv.is(V.sv.hd(x), "abs"), fd.k.abs(x), fd.k.bad("fold:local-", V.sv.hd(x))))

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
      fd.lam(fd.go(ms, KMatches{}, env))
    case X.SxCons{_, es} KEtuple{}:
      fd.etuple(fd.go(es, KEs{}, fd.notail(env)), env)
    case X.SxCons{_, X.SxCons{+e, X.SxCons{ms, _}}} KEcase{}:
      fd.ecase(fd.vname(V.sv.str(e, 1n)), fd.go(ms, KMatches{}, env), env)
    case X.SxCons{_, X.SxCons{+c, X.SxCons{+a, X.SxCons{+b, _}}}} KEif{}:
      fd.eif(fd.go(c, fd.k(RoEx{}, c), fd.notail(env)), fd.go(a, fd.k(RoEx{}, a), env), fd.go(b, fd.k(RoEx{}, b), env), env)
    case X.SxCons{_, X.SxCons{+t, X.SxCons{gs, _}}} KEmultiif{}:
      +ty = fd.go(t, fd.k(RoTy{}, t), env)
      fd.multiif(ty, fd.go(gs, KGrhsL{}, fd.withres(env, fd.rt(ty))))
    case X.SxCons{_, X.SxCons{bs, X.SxCons{+e, _}}} KElet{}:
      +rb = fd.go(bs, KBinds{}, fd.notail(env))
      fd.elet(rb, fd.go(e, fd.k(RoEx{}, e), fd.addls(env, fd.bnames(fd.items(rb)))), env)
    case X.SxCons{_, X.SxCons{_, X.SxCons{es, _}}} KElist{}:
      fd.elist(fd.go(es, KEs{}, fd.notail(env)), env)
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
    case X.SxCons{_, X.SxCons{ps, X.SxCons{g, _}}} KMatch{}:
      +rp = fd.go(ps, KPs{}, env)
      fd.clause(rp, fd.go(g, KGrhss{}, fd.addls(env, fd.pnames(fd.bts(fd.items(rp))))))
    case X.SxCons{_, X.SxCons{gs, X.SxCons{bs, _}}} KGrhss{}:
      +rb = fd.go(bs, KBinds{}, fd.notail(env))
      fd.grhss(rb, fd.go(gs, KGrhsL{}, fd.addls(env, fd.bnames(fd.items(rb)))), env)
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
      fd.lbind(fd.bvname(X.SxCons{X.SxAtom{S.b("bv")}, X.SxCons{fd.unself(v), X.SxNil{}}}), fd.go(ms, KMatches{}, fd.notail(env)))
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
      fd.ctrs.of(ty, t, Ctr{V.sv.str(c, 1n), ty, X.tsx.len(V.sv.at(c, 3n))} <> acc)
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

# the module's data types; one with a field type the fold cannot write is
# out, with that type as the reason, like a def
def fd.datas.if(d: Bool, +x: X.Sx, +env: Env, acc: List<&2, Got>) -> List<&2, Got>:
  match d:
    case True{}:
      fd.got.def(V.sv.str(x, 1n), fd.data(x, env)) <> acc
    case False{}:
      acc

def fd.datas(xs: List<&2, X.Sx>, +env: Env) -> List<&2, Got>:
  match xs:
    case +h <> t:
      fd.datas.if(fd.isdata(h), h, env, fd.datas(t, env))
    case Nil{}:
      Nil{}

def fd.got.of(ok: Bool, tb: Tb, +env: Env) -> Got:
  match ok tb:
    case True{} TbFun{+n, +tvs, f}:
      fd.got.def(n, fd.def(n, tvs, fd.go(V.sv.at(f, 4n), KMatches{}, fd.withself(env, fd.tvbts(tvs)))))
    case True{} TbNo{n, why}:
      GotOut{n, why}
    case False{} TbFun{n, tvs, f}:
      GotOut{n, S.b("survey")}
    case False{} TbNo{n, why}:
      GotOut{n, S.b("survey")}
    case _ _:
      GotOut{S.b("?"), S.b("fold:skip")}

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
      fd.got.of(S.mem(fd.tb.name(tb), ok), tb, env) <> acc
    case False{}:
      acc

def fd.gots(tbs: List<&2, Tb>, +ok: List<&2, List<&2, U32>>, +env: Env) -> List<&2, Got>:
  match tbs:
    case +h <> t:
      fd.gots.if(fd.tb.user(h), ok, h, env, fd.gots(t, ok, env))
    case Nil{}:
      Nil{}

# The survey's verdict --------------------------------------------------------------

# the names the survey puts in the first version (Survey.bend's sv.module.ok)
def fd.ok(+xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  +tb = V.sv.tb()
  +m = V.sv.modname(xs)
  +bad = V.sv.tys(xs, V.Env{m, tb, Nil{}}, Nil{})
  +fs0 = V.sv.tops(xs, V.Env{m, tb, bad}, Nil{})
  +all = V.sv.names(fs0)
  V.sv.ok.fix(1n+List.length(&2, V.Fn, fs0), fs0, all, all)

# The prelude ---------------------------------------------------------------------

# what the written defs call that Base does not have, as Bend text
def fd.pre.if() -> String:
  "# an if: Bend has no if, and matches only parameters, so the branches\n# are thunks, as Base's List.any.if writes it\ndef Bool.if(-R: Type, c: Bool, t: Unit -> R, e: Unit -> R) -> R:\n  match c:\n    case True{}:\n      t(Unit{})\n    case False{}:\n      e(Unit{})\n\n"

def fd.pre.map() -> String:
  "# map over a list Bend may copy (Base's List.map takes List<&1, A>)\ndef hs.map(~A: Data, ~B: Data, ~f: A -> B, xs: List<&2, A>) -> List<&2, B>:\n  match xs:\n    case Nil{}:\n      Nil{}\n    case h <> t:\n      f(h) <> hs.map(~A, ~B, ~f, t)\n\n"

def fd.uses.name(its: List<&2, T.BItem>, +n: List<&2, U32>) -> Bool:
  match its:
    case +h <> t:
      Bool.or(S.mem(n, T.tba.item.fold(~T.tba.refs, h, Nil{})), fd.uses.name(t, n))
    case Nil{}:
      False{}

def fd.prelude(+its: List<&2, T.BItem>) -> List<&2, U32>:
  fd.cat(fd.bpick(fd.uses.name(its, S.b("Bool.if")), S.b(fd.pre.if()), Nil{}), fd.bpick(fd.uses.name(its, S.b("hs.map")), S.b(fd.pre.map()), Nil{}))

# The file -------------------------------------------------------------------------

def fd.header(+file: List<&2, U32>, +m: List<&2, U32>) -> List<&2, List<&2, U32>>:
  [fd.cat(S.b("Haskell module "), m), fd.cat(S.b("from "), file), S.b("Written by cata (fixed rules, no model); every def checks with bend --check-only.")]

# the file's text: header, import Base, the prelude, the items in order
def fd.text(+file: List<&2, U32>, +m: List<&2, U32>, +its: List<&2, T.BItem>) -> List<&2, U32>:
  P.tpr.file(T.BFile{fd.header(file, m), Nil{}, O.tor.order(its)})

def fd.splice.at(hit: Bool, h: List<&2, U32>, t: List<&2, List<&2, U32>>, pre: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      h <> Nil{} <> List.append(&2, List<&2, U32>, S.split(pre, 10), t)
    case False{}:
      h <> t

def fd.splice.go(ls: List<&2, List<&2, U32>>, +pre: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ls:
    case +h <> t:
      fd.splice.at(fd.is(h, "import Base"), h, fd.splice.go(t, pre), pre)
    case Nil{}:
      Nil{}

# the prelude goes right after `import Base`
def fd.splice(text: List<&2, U32>, pre: List<&2, U32>) -> List<&2, U32>:
  S.join(fd.splice.go(S.split(text, 10), pre), 10)

def fd.render(+file: List<&2, U32>, +m: List<&2, U32>, +its: List<&2, T.BItem>) -> List<&2, U32>:
  fd.splice(fd.text(file, m, its), fd.prelude(its))

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

# the items that mention a name gone go too
def fd.split(its: List<&2, T.BItem>, +gone: List<&2, List<&2, U32>>, +why: List<&2, U32>) -> Split:
  match its:
    case +h <> t:
      fd.split.if(fd.hits(h, gone), h, why, fd.split(t, gone, why))
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

# the names of the item named n: its own, and its constructors if a type
def fd.namesof(its: List<&2, T.BItem>, +n: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match its:
    case +h <> t:
      fd.bpicks(S.eq(fd.item.name(h), n), fd.item.names(h), fd.namesof(t, n))
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

# the item an error is in gone, with every item that uses it
def fd.gate.drop(who: Maybe<&2, List<&2, U32>>, +its: List<&2, T.BItem>, out: List<&2, Dr>, +why: List<&2, U32>) -> Gs:
  match who:
    case None{}:
      Gs{Nil{}, List.append(&2, Dr, fd.gate.all(its, why), out), True{}}
    case Some{+n}:
      +dep = fd.cat(S.b("dep:"), n)
      +s = fd.closure(List.length(&2, T.BItem, its), fd.split(fd.without(its, n), fd.namesof(its, n), dep), dep, Dr{n, why} <> out)
      Gs{Split.keep(s), Split.out(s), List.is_empty(&2, T.BItem, Split.keep(s))}

def fd.gate.who(l: Maybe<&2, Nat>, text: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match l:
    case Some{n}:
      fd.owner(n, S.split(text, 10), None{})
    case None{}:
      None{}

# one round's verdict: done when Bend accepts the file
def fd.gate.step(g: Gs, +file: List<&2, U32>, +m: List<&2, U32>, +out: List<&2, U32>) -> Gs:
  match g:
    case Gs{its, o, True{}}:
      Gs{its, o, True{}}
    case Gs{+its, +o, False{}}:
      +ls = S.split(out, 10)
      Bool.pick(Gs, S.prefix(out, S.b("ALL PROOFS CHECK")), Gs{its, o, True{}}, fd.gate.drop(fd.gate.who(fd.errline(ls), fd.render(file, m, its)), its, o, fd.cat(S.b("check:"), fd.errwhy(ls))))

# one round's check: write the file and run bend on it (nothing once done)
def fd.gate.io(g: Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>) -> IO(S.Out):
  match g:
    case Gs{its, o, True{}}:
      IO.pure(S.Out, S.Out{0, S.b("ALL PROOFS CHECK")})
    case Gs{its, o, False{}}:
      do IO<S.Out>:
        S.write(path, fd.render(file, m, its))
        S.run(".", Nil{}, 300, bend, [path, "--check-only"], Nil{})

# the gate: check, drop the item the error is in (and what uses it), and
# check again, until Bend accepts the file or nothing is left
def fd.gate(fuel: Nat, g: Gs, +bend: String, +path: String, +file: List<&2, U32>, +m: List<&2, U32>) -> IO(Gs):
  match fuel:
    case 0n:
      IO.pure(Gs, g)
    case 1n+p:
      +g1 = g
      do IO<Gs>:
        o : S.Out <- fd.gate.io(g1, bend, path, file, m)
        fd.gate(p, fd.gate.step(g1, file, m, S.Out.text(o)), bend, path, file, m)

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
      Dr{fd.vname(n), w} <> fd.got.outs(t)
    case _ <> t:
      fd.got.outs(t)
    case Nil{}:
      Nil{}

def fd.ledger.ok(+file: List<&2, U32>, its: List<&2, T.BItem>) -> List<&2, U32>:
  match its:
    case T.BiDef{n, ps, r, b, d} <> t:
      fd.cat(S.join([file, n, S.b("ok"), Nil{}], 9), 10 <> fd.ledger.ok(file, t))
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

def fd.module.fin(+out: String, +file: List<&2, U32>, +m: List<&2, U32>, +path: String, g: Gs) -> IO(Unit):
  match g:
    case Gs{+k, o, d}:
      do IO<Unit>:
        fd.module.write(fd.hasdef(k), path, fd.render(file, m, k))
        S.add(out ++ "/ledger.tsv", fd.ledger(file, k, o))

def fd.env0(m: List<&2, U32>, cs: List<&2, Ctr>, ds: List<&2, Df>) -> Env:
  Env{m, cs, ds, None{}, Nil{}, Nil{}, Nil{}}

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

def fd.syns(fuel: Nat, +xs: List<&2, X.Sx>, +env: Env) -> Env:
  match fuel:
    case 0n:
      env
    case 1n+p:
      fd.syns(p, xs, fd.withsyn(env, fd.syns.round(xs, env)))

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

type Tf is Data:
  Tf{n: List<&2, U32>, fl: List<&2, Bool>}

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

def fd.tpl.rounds(fuel: Nat, done: Bool, +gs: List<&2, Got>) -> List<&2, Got>:
  match fuel done:
    case 0n _:
      gs
    case 1n+p True{}:
      gs
    case 1n+p False{}:
      +g2 = fd.tpl.round(gs, fd.tfs(gs))
      fd.tpl.rounds(p, S.eq(fd.tfs.key(fd.tfs(gs)), fd.tfs.key(fd.tfs(g2))), g2)

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

def fd.templates(+gs: List<&2, Got>) -> List<&2, Got>:
  +g2 = fd.tpl.rounds(1n+List.length(&2, Got, gs), False{}, gs)
  fd.tpl.fin(g2, fd.tfs(g2))

# the items that use a binding that is out go too, before the first check
def fd.predrop(+its: List<&2, T.BItem>, +outs: List<&2, Dr>) -> Gs:
  +s = fd.closure(List.length(&2, T.BItem, its), fd.split(its, fd.dr.names(outs), S.b("dep")), S.b("dep"), outs)
  Gs{Split.keep(s), Split.out(s), List.is_empty(&2, T.BItem, Split.keep(s))}

# a module: fold its bindings, gate them, write OUT/BASE.bend and the ledger
def fd.module(+rounds: Nat, +bend: String, +out: String, +file: List<&2, U32>, +base: List<&2, U32>, bytes: List<&2, U32>) -> IO(Unit):
  +xs = X.tsx.read(bytes)
  +m = V.sv.modname(xs)
  +tbs = fd.tbs(xs)
  +env = fd.syns(fd.nsyn(xs), xs, fd.env0(m, fd.ctrs(xs), fd.dfs(tbs)))
  +gs = fd.templates(List.append(&2, Got, fd.datas(xs, env), fd.gots(tbs, fd.ok(xs), env)))
  +its = fd.got.items(gs)
  +path = out ++ "/" ++ S.str(base) ++ ".bend"
  +try = out ++ "/" ++ S.str(base) ++ "_try.bend"
  do IO<Unit>:
    g : Gs <- fd.gate(Bool.pick(Nat, Nat.is_eq(rounds, 0n), 1n+List.length(&2, T.BItem, its), rounds), fd.predrop(its, fd.got.outs(gs)), bend, try, file, m)
    fd.module.fin(out, file, m, path, g)

def fd.base.strip(r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case 112 <> 120 <> 101 <> 115 <> 46 <> t:
      List.reverse(&2, U32, t)
    case u:
      List.reverse(&2, U32, u)

# a file's base name without .sexp
def fd.base(+f: List<&2, U32>) -> List<&2, U32>:
  fd.base.strip(List.reverse(&2, U32, Maybe.default(&2, List<&2, U32>, List.last(&2, List<&2, U32>, S.split(f, 47)), f)))

def fd.run(xs: List<String>, +rounds: Nat, +bend: String, +out: String) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        fd.module(rounds, bend, out, S.b(f), fd.base(S.b(f)), bytes)
        fd.run(t, rounds, bend, out)

def fd.main(args: List<String>, +rounds: Nat, +bend: String) -> IO(Unit):
  match args:
    case out <> files:
      fd.run(files, rounds, bend, out)
    case Nil{}:
      IO.print("usage: fold OUT FILE.sexp...  (BEND: the bend to check with)")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    bend : String <- S.env("BEND", "bend")
    rounds : Nat <- S.env.nat("FOLD_ROUNDS", 0n)
    fd.main(List.tail(&1, String, argv), rounds, bend)
