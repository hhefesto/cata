import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Ast.bend as T

# Back: bend2hs, the way back from cata's Bend to Haskell (PLAN.md, "cata
# as a functor": hs2bend is F, this is G).  It prints the items a law run
# kept (ToBend/Ast.bend's syntax tree, before Print writes them) as one
# Haskell module, so that GHC can run G(F(h)) on the inputs the laws hold
# F(h) to, and compare with h (tests/back/run.zsh).  It covers cata's own
# output fragment, no more:
#
# - every type argument is erased: an argument that is a type application,
#   a type, an arrow, a type function, or a name whose last part is
#   capitalized or a quantity (&2), and a parameter whose type is Data,
#   Type, a kind or a function to one;
# - Base's and the prelude's names (anything with a dot that the module
#   does not define) are prelude/Back/BendRt.hs's, each `b'` and the name
#   with its dots as primes (List.append is b'List'append), Base's
#   constructors Haskell's own (Con is (:), Some Just, Inl Left, Tuple (,));
# - the module's defs are `c'` and their Bend names (dots as primes), and
#   each def that GHC knows by a Haskell name (laws: the TbFun's) is that
#   name too, `name = c'name` (an operator in parentheses);
# - a type of the module and its constructors are their Haskell names
#   again (the export's: cata's List_ is List, its Cons_ Cons, its
#   op_colon_plus (:+)), qualified by the module where BendRt has the name
#   too; a type cata made (a group's .mu.In, a twin) is T' and its name,
#   its constructors C' and theirs;
# - a local (a parameter, a lambda's, a let's, a pattern's) is its name
#   without Bend's marks (+x is x), and a local hides a def of its name, as
#   in Bend;
# - match is case, on a tuple of the scrutinees when there are several; a
#   Nat pattern 1n+p is the view (b'pred -> Just p), a character pattern a
#   character literal; a let is a case on a variable (Bend's let does not
#   recurse, Haskell's would); a rewrite is its body; Bend's types become
#   BendRt's synonyms (Nat is Int: cata writes Int as Nat only where nothing
#   subtracts), but a data field's Nat is h's Int, Integer or Natural when
#   the export says so (F sends all three to Nat, so G needs h's type);
# - G(F(t)) is t only up to an iso (h's triple is G's nested pair; a
#   partial h answers Either String A), so each def GHC knows is h's name =
#   b'up (G's def), BendRt's iso at the type the laws' script names, and a
#   partial def's Either is unwrapped first (b'unfail: Inl m is h's error
#   m).
#
# Laws (defs whose type is an equation) are not printed.  What it cannot
# write it writes as b'todo, so GHC says where.  Every def is prefixed
# `bk.`.

# Names -------------------------------------------------------------------------

def bk.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def bk.b(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, acc)

def bk.s(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, S.b(s), acc)

def bk.dot.ch(+c: U32) -> U32:
  Bool.pick(U32, U32.is_eq(c, 46), 39, c)

# a name's dots as primes
def bk.dots(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> t:
      bk.dot.ch(c) <> bk.dots(t)

def bk.has.dot(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +c <> t:
      Bool.or(U32.is_eq(c, 46), bk.has.dot(t))

# the last part of a dotted name (cur: the part so far)
def bk.last.go(xs: List<&2, U32>, cur: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, cur)
    case +c <> t:
      bk.last.go(t, Bool.pick(List<&2, U32>, U32.is_eq(c, 46), Nil{}, c <> cur))

def bk.last(+xs: List<&2, U32>) -> List<&2, U32>:
  bk.last.go(xs, Nil{})

# the part before the last dot
def bk.init(+xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, xs, Nat.sub(List.length(&2, U32, xs), Nat.add(List.length(&2, U32, bk.last(xs)), 1n)))

def bk.upper(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90))

def bk.digit(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57))

def bk.head.upper(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      bk.upper(c)
    case Nil{}:
      False{}

def bk.head.digit(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      bk.digit(c)
    case Nil{}:
      False{}

def bk.lower1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      Bool.pick(U32, bk.upper(c), U32.add(c, 32), c) <> t
    case Nil{}:
      Nil{}

# Bend's marks on a binder: +x (copied), ~x, -x
def bk.mark(+c: U32) -> Bool:
  Bool.or(U32.is_eq(c, 43), Bool.or(U32.is_eq(c, 126), U32.is_eq(c, 45)))

# its mark dropped (mk), or a parenthesized one's, (+x) (pr: its last
# character dropped too)
def bk.bare.at(pr: Bool, mk: Bool, +c: U32, +t: List<&2, U32>) -> List<&2, U32>:
  match pr mk:
    case True{} _:
      List.take(&2, U32, List.drop(&2, U32, t, 1n), Nat.sub(List.length(&2, U32, t), 2n))
    case False{} True{}:
      t
    case False{} False{}:
      c <> t

# a local's name without its mark: +x, ~x, -x and (+x) are x
def bk.bare(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      bk.bare.at(U32.is_eq(c, 40), bk.mark(c), c, t)
    case Nil{}:
      Nil{}

# a Haskell name GHC knows a def, a type or a constructor by (hs) and its
# Bend name (b)
type BkA is Data:
  BkA{hs: List<&2, U32>, b: List<&2, U32>}

# the Haskell name of the Bend name b (the first pair's)
def bk.find(ps: List<&2, BkA>, +b: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      None{}
    case BkA{h, +b2} <> t:
      Bool.pick(Maybe<&2, List<&2, U32>>, S.eq(b2, b), Some{h}, bk.find(t, b))

def bk.hss(ps: List<&2, BkA>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case BkA{h, b} <> t:
      h <> bk.hss(t)

# h's type, as the export has it (its synonyms expanded): F is not one to
# one on types (Int, Integer and Natural are all Nat, h's (a, b, c) is
# Bend's (a, (b, c))), so G takes a data field's type back from h.  A type
# variable (its Bend name), one of base's (Haskell's name: Int, Maybe,
# ...), one of the module's (its Bend name), a list, a tuple (its
# elements), a function, an argument spine, or a type G does not know
type BkT is Data:
  BkTv{n: List<&2, U32>}
  BkTh{n: List<&2, U32>, args: BkT}
  BkTc{n: List<&2, U32>, args: BkT}
  BkTList{a: BkT}
  BkTTup{xs: BkT}
  BkTFun{a: BkT, b: BkT}
  BkTArgs{a: BkT, rest: BkT}
  BkTNil{}
  BkTNo{}

# a constructor's fields' h types, by its Bend name
type BkF is Data:
  BkF{c: List<&2, U32>, fs: List<&2, BkT>}

# a type whose first n parameters are kind variables (hs-export lists a
# type's kind variables with its type variables, and drops them where the
# type is applied: GHC's invisible arguments), by its Bend name
type BkD is Data:
  BkD{t: List<&2, U32>, n: Nat}

# the names the module gets: its Haskell name, its defs' Haskell names
# (as), its types' (tn) and its constructors' (cn), its partial defs'
# Bend names (pd), its constructors' fields' h types (nf), and its types'
# kind variables (kd)
type BkN is Data:
  BkN{m: List<&2, U32>, as: List<&2, BkA>, tn: List<&2, BkA>, cn: List<&2, BkA>, pd: List<&2, List<&2, U32>>, nf: List<&2, BkF>, kd: List<&2, BkD>}

# a partial def (pd: their Bend names; Fold's fd.pt: it answers
# Either<String, A>, h's error as Inl): its Bend name and its value
# parameters' count
type BkP is Data:
  BkP{b: List<&2, U32>, n: Nat}

def bk.nm.m(+nm: BkN) -> List<&2, U32>:
  match nm:
    case BkN{m, as, tn, cn, pd, nf, kd}:
      m

def bk.nm.as(+nm: BkN) -> List<&2, BkA>:
  match nm:
    case BkN{m, as, tn, cn, pd, nf, kd}:
      as

def bk.nm.pd(+nm: BkN) -> List<&2, List<&2, U32>>:
  match nm:
    case BkN{m, as, tn, cn, pd, nf, kd}:
      pd

# what the module defines: its Haskell name, its defs' and its types' Bend
# names, its types' and constructors' Haskell names, its partial defs, its
# constructors' fields' h types, its types' kind variables, and the
# constructors G reaches through a pattern synonym (cv: their Bend names)
type Bk is Data:
  Bk{m: List<&2, U32>, defs: List<&2, List<&2, U32>>, tys: List<&2, List<&2, U32>>, tn: List<&2, BkA>, cn: List<&2, BkA>, pt: List<&2, BkP>, nf: List<&2, BkF>, kd: List<&2, BkD>, cv: List<&2, List<&2, U32>>}

def bk.kd(+e: Bk) -> List<&2, BkD>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      kd

def bk.cvs(+e: Bk) -> List<&2, List<&2, U32>>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      cv

# a type's kind variables' count (0: none)
def bk.kd.find(ds: List<&2, BkD>, +t: List<&2, U32>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case BkD{+t2, n} <> r:
      Bool.pick(Nat, S.eq(t2, t), n, bk.kd.find(r, t))

# a spine's length
def bk.hk.len(t: BkT) -> Nat:
  match t:
    case BkTArgs{a, r}:
      1n+bk.hk.len(r)
    case _:
      0n

# whether F reshapes h's type (a tuple of 3 or more within: Bend's are
# nested pairs)
def bk.hk.re(t: BkT) -> Bool:
  match t:
    case BkTTup{+xs}:
      Bool.or(Nat.is_ge(bk.hk.len(xs), 3n), bk.hk.re(xs))
    case BkTh{n, a}:
      bk.hk.re(a)
    case BkTc{n, a}:
      bk.hk.re(a)
    case BkTList{a}:
      bk.hk.re(a)
    case BkTFun{a, b}:
      Bool.or(bk.hk.re(a), bk.hk.re(b))
    case BkTArgs{a, r}:
      Bool.or(bk.hk.re(a), bk.hk.re(r))
    case _:
      False{}

# h's types: whether G knows one (a type of the module applied to one F
# reshapes it is beyond: G would have to map inside it)
def bk.hk.ok(t: BkT) -> Bool:
  match t:
    case BkTNo{}:
      False{}
    case BkTv{n}:
      True{}
    case BkTh{n, a}:
      bk.hk.ok(a)
    case BkTc{n, +a}:
      Bool.and(bk.hk.ok(a), Bool.not(bk.hk.re(a)))
    case BkTList{a}:
      bk.hk.ok(a)
    case BkTTup{xs}:
      bk.hk.ok(xs)
    case BkTFun{a, b}:
      Bool.and(bk.hk.ok(a), bk.hk.ok(b))
    case BkTArgs{a, r}:
      Bool.and(bk.hk.ok(a), bk.hk.ok(r))
    case BkTNil{}:
      True{}

# a field G prints as h has it, through a pattern synonym
def bk.hk.cv(+t: BkT) -> Bool:
  Bool.and(bk.hk.ok(t), bk.hk.re(t))

def bk.hk.anycv(ts: List<&2, BkT>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> r:
      Bool.or(bk.hk.cv(t), bk.hk.anycv(r))

# the constructors with a field F reshapes
def bk.cv(fs: List<&2, BkF>) -> List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      Nil{}
    case BkF{c, +ts} <> r:
      +rest = bk.cv(r)
      Bool.pick(List<&2, List<&2, U32>>, bk.hk.anycv(ts), c <> rest, rest)

def bk.nf(+e: Bk) -> List<&2, BkF>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      nf

# a constructor's fields' h types (none known: Nil)
def bk.nf.find(fs: List<&2, BkF>, +c: List<&2, U32>) -> List<&2, BkT>:
  match fs:
    case Nil{}:
      Nil{}
    case BkF{+c2, ns} <> t:
      Bool.pick(List<&2, BkT>, S.eq(c2, c), ns, bk.nf.find(t, c))

def bk.pt(+e: Bk) -> List<&2, BkP>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      pt

def bk.m(+e: Bk) -> List<&2, U32>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      m

def bk.defs(+e: Bk) -> List<&2, List<&2, U32>>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      d

def bk.tys(+e: Bk) -> List<&2, List<&2, U32>>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      t

def bk.tn(+e: Bk) -> List<&2, BkA>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      tn

def bk.cn(+e: Bk) -> List<&2, BkA>:
  match e:
    case Bk{m, d, t, tn, cn, pt, nf, kd, cv}:
      cn

def bk.dname(+x: List<&2, U32>) -> List<&2, U32>:
  99 <> 39 <> bk.dots(x)

# whether a Haskell name is an operator's (its first character is not a
# letter or _)
def bk.alias.lead(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), U32.is_eq(c, 95)), bk.upper(c))

def bk.isop(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      Bool.not(bk.alias.lead(c))
    case Nil{}:
      False{}

def bk.paren(op: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match op:
    case True{}:
      40 <> bk.cat(xs, [41])
    case False{}:
      xs

# a Haskell name as a binder: an operator in parentheses
def bk.alias.name(+h: List<&2, U32>) -> List<&2, U32>:
  bk.paren(bk.isop(h), h)

# a Haskell name in a term or a type: M.name where BendRt has the name too
# (q), an operator in parentheses
def bk.ref(q: Bool, +m: List<&2, U32>, +h: List<&2, U32>) -> List<&2, U32>:
  match q:
    case True{}:
      bk.paren(bk.isop(h), bk.cat(m, 46 <> h))
    case False{}:
      bk.alias.name(h)

# the names BendRt has as types and as constructors (Haskell's, re-exported)
def bk.rt.tys() -> List<&2, List<&2, U32>>:
  [S.b("Bool"), S.b("Maybe"), S.b("Either"), S.b("Ordering"), S.b("Int"), S.b("Char"), S.b("String"), S.b("Float")]

def bk.rt.cons() -> List<&2, List<&2, U32>>:
  [S.b("True"), S.b("False"), S.b("Just"), S.b("Nothing"), S.b("Left"), S.b("Right"), S.b("LT"), S.b("EQ"), S.b("GT")]

# a name in a term: a local, the module's def, a character or a number, a
# name of Base or the prelude (dotted), else as it is
def bk.var.at(loc: Bool, own: Bool, lit: Bool, dot: Bool, +x: List<&2, U32>, y: List<&2, U32>) -> List<&2, U32>:
  match loc own lit dot:
    case True{} _ _ _:
      y
    case False{} True{} _ _:
      bk.dname(x)
    case False{} False{} True{} _:
      x
    case False{} False{} False{} True{}:
      98 <> 39 <> bk.dots(x)
    case False{} False{} False{} False{}:
      y

def bk.var(+e: Bk, +sc: List<&2, List<&2, U32>>, +x: List<&2, U32>) -> List<&2, U32>:
  +y = bk.bare(x)
  bk.var.at(S.mem(y, sc), S.mem(x, bk.defs(e)), Bool.or(S.head.is(x, 39), bk.head.digit(x)), bk.has.dot(x), x, y)

# a type's Haskell name: the module's own as Haskell names it (h, found),
# else one cata made T' and its name; Base's BendRt's synonym.  head: at
# its own declaration (never qualified)
def bk.tname.own(found: Maybe<&2, List<&2, U32>>, head: Bool, plain: Bool, +m: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  match found head plain:
    case Some{+h} True{} _:
      bk.alias.name(h)
    case Some{+h} False{} _:
      bk.ref(S.mem(h, bk.rt.tys()), m, h)
    case None{} _ True{}:
      n
    case None{} _ False{}:
      84 <> 39 <> bk.dots(n)

def bk.tname.at(own: Bool, head: Bool, +e: Bk, +n: List<&2, U32>) -> List<&2, U32>:
  match own:
    case True{}:
      bk.tname.own(bk.find(bk.tn(e), n), head, Bool.and(bk.head.upper(n), Bool.not(bk.has.dot(n))), bk.m(e), n)
    case False{}:
      66 <> 39 <> bk.dots(n)

def bk.tname(+e: Bk, +n: List<&2, U32>) -> List<&2, U32>:
  bk.tname.at(S.mem(n, bk.tys(e)), False{}, e, n)

# Base's constructors as Haskell's
def bk.con.base(+c: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, S.eq(c, S.b("Con")), S.b("(:)"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Nil")), S.b("[]"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Tuple")), S.b("(,)"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Some")), S.b("Just"), Bool.pick(List<&2, U32>, S.eq(c, S.b("None")), S.b("Nothing"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Inl")), S.b("Left"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Inr")), S.b("Right"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Unit")), S.b("()"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Chr")), S.b("b'chr"), Bool.pick(List<&2, U32>, bk.has.dot(c), 66 <> 39 <> bk.dots(c), c))))))))))

# Base's constructor, BendRt.C when the module has a constructor C too
def bk.con.rt(clash: Bool, +h: List<&2, U32>) -> List<&2, U32>:
  match clash:
    case True{}:
      bk.s("BendRt.", h)
    case False{}:
      h

# a constructor of the module's type: Haskell's name (found), else the
# last part of its name (a plain type's), else C' and its name (a type cata
# made); head: at its declaration
def bk.con.own(found: Maybe<&2, List<&2, U32>>, head: Bool, plain: Bool, +m: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  match found head plain:
    case Some{+h} True{} _:
      bk.alias.name(h)
    case Some{+h} False{} _:
      bk.ref(S.mem(h, bk.rt.cons()), m, h)
    case None{} _ True{}:
      bk.last(c)
    case None{} _ False{}:
      67 <> 39 <> bk.dots(c)

# the module's constructor, or (pv: in a term or a pattern, the
# constructor having a field F reshapes) its pattern synonym, P' and its
# Bend name
def bk.con.pv(pv: Bool, head: Bool, +e: Bk, +c: List<&2, U32>, +t: List<&2, U32>) -> List<&2, U32>:
  match pv:
    case True{}:
      80 <> 39 <> bk.dots(c)
    case False{}:
      bk.con.own(bk.find(bk.cn(e), c), head, Bool.and(bk.head.upper(t), Bool.not(bk.has.dot(t))), bk.m(e), c)

def bk.con.at(own: Bool, +head: Bool, +e: Bk, +c: List<&2, U32>, +t: List<&2, U32>) -> List<&2, U32>:
  match own:
    case True{}:
      bk.con.pv(Bool.and(Bool.not(head), S.mem(c, bk.cvs(e))), head, e, c, t)
    case False{}:
      +h = bk.con.base(c)
      bk.con.rt(S.mem(h, bk.hss(bk.cn(e))), h)

def bk.con.h(head: Bool, +e: Bk, +c: List<&2, U32>) -> List<&2, U32>:
  +t = bk.init(c)
  bk.con.at(S.mem(t, bk.tys(e)), head, e, c, t)

def bk.con(+e: Bk, +c: List<&2, U32>) -> List<&2, U32>:
  bk.con.h(False{}, e, c)

# whether a term is a type (an argument G erases)
def bk.isty.var(+x: List<&2, U32>) -> Bool:
  Bool.or(S.head.is(x, 38), bk.head.upper(bk.last(x)))

def bk.isty(+t: T.Bt) -> Bool:
  match t:
    case T.BtTplArg{+a}:
      bk.isty(a)
    case T.BtDead{+a}:
      bk.isty(a)
    case T.BtTyApp{n, a}:
      True{}
    case T.BtType{}:
      True{}
    case T.BtPi{m, x, d, a, b}:
      True{}
    case T.BtLam{m, x, +b}:
      bk.isty(b)
    case T.BtVar{+x}:
      bk.isty.var(x)
    case _:
      False{}

# a parameter's type that makes it a type's (erased): Data, Type, a kind,
# or a function to one (a type function, as Fix's F)
def bk.kind(+t: T.Bt) -> Bool:
  match t:
    case T.BtType{}:
      True{}
    case T.BtVar{+x}:
      Bool.or(S.eq(x, S.b("Data")), Bool.or(S.eq(x, S.b("Type")), S.eq(x, S.b("Quant"))))
    case T.BtApp{T.BtVar{+x}, a}:
      S.eq(x, S.b("Kind"))
    case T.BtPi{m, x, d, a, +b}:
      bk.kind(b)
    case _:
      False{}

# a string's bytes as a Haskell literal's: " and \ and the control
# characters escaped (\N\&), the rest as they are (UTF-8, as GHC reads a
# source)
def bk.str.esc(ok: Bool, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      c <> rest
    case False{}:
      92 <> bk.b(S.b(U32.show(c)), 92 <> 38 <> rest)

def bk.str(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case +c <> t:
      bk.str.esc(Bool.and(Bool.and(U32.is_ge(c, 32), U32.is_ne(c, 127)), Bool.and(U32.is_ne(c, 34), U32.is_ne(c, 92))), c, bk.str(t, acc))

def bk.open(multi: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match multi:
    case True{}:
      40 <> xs
    case False{}:
      xs

def bk.close(multi: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match multi:
    case True{}:
      41 <> xs
    case False{}:
      xs

def bk.lead(skip: Bool, xs: List<&2, U32>) -> List<&2, U32>:
  match skip:
    case True{}:
      xs
    case False{}:
      32 <> xs

# the variables a pattern binds, before sc
def bk.pv(t: T.Bt, sc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match t:
    case T.BtArgs{a, rest}:
      bk.pv(a, bk.pv(rest, sc))
    case T.BtCon{c, args}:
      bk.pv(args, sc)
    case T.BtSucc{p}:
      bk.pv(p, sc)
    case T.BtPv{m, x}:
      bk.bare(x) <> sc
    case T.BtVar{x}:
      bk.bare(x) <> sc
    case _:
      sc

# Terms -------------------------------------------------------------------------

# where a term is printed: a term, nothing (an erased argument), an
# application's or a constructor's arguments (each after a space), a
# pattern, a constructor pattern's arguments, a case's patterns and the
# scrutinees (", " between: first, rest), a match's cases
type BkK is Data:
  BkTerm{}
  BkSkip{}
  BkArgs{}
  BkCArgs{}
  BkPat{}
  BkPArgs{}
  BkList{}
  BkListRest{}
  BkScr{}
  BkScrRest{}
  BkChr{}
  BkCases{multi: Bool}

def bk.argk(skip: Bool) -> BkK:
  match skip:
    case True{}:
      BkSkip{}
    case False{}:
      BkTerm{}

# a constructor pattern with arguments: a character's (Chr{N}) as its
# literal '\N', another as (C ARGS); its arguments as k says (pk)
def bk.pk(chr: Bool) -> BkK:
  match chr:
    case True{}:
      BkChr{}
    case False{}:
      BkPArgs{}

def bk.pcon.open(chr: Bool, +e: Bk, +c: List<&2, U32>, inner: List<&2, U32>) -> List<&2, U32>:
  match chr:
    case True{}:
      39 <> 92 <> inner
    case False{}:
      40 <> bk.b(bk.con(e, c), inner)

def bk.pcon.close(chr: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match chr:
    case True{}:
      39 <> acc
    case False{}:
      41 <> acc

# t, printed as k says; e: the module's names; sc: the locals in scope
def bk.t(t: T.Bt, k: BkK, +e: Bk, +sc: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match t k:
    case _ BkSkip{}:
      acc
    # argument lists
    case T.BtArgs{+a, rest} BkArgs{}:
      bk.lead(bk.isty(a), bk.t(a, bk.argk(bk.isty(a)), e, sc, bk.t(rest, BkArgs{}, e, sc, acc)))
    case T.BtArgs{a, rest} BkCArgs{}:
      32 <> bk.t(a, BkTerm{}, e, sc, bk.t(rest, BkCArgs{}, e, sc, acc))
    case T.BtArgs{a, rest} BkPArgs{}:
      32 <> bk.t(a, BkPat{}, e, sc, bk.t(rest, BkPArgs{}, e, sc, acc))
    case T.BtArgs{a, rest} BkList{}:
      bk.t(a, BkPat{}, e, sc, bk.t(rest, BkListRest{}, e, sc, acc))
    case T.BtArgs{a, rest} BkListRest{}:
      44 <> 32 <> bk.t(a, BkPat{}, e, sc, bk.t(rest, BkListRest{}, e, sc, acc))
    case T.BtArgs{a, rest} BkScr{}:
      bk.t(a, BkTerm{}, e, sc, bk.t(rest, BkScrRest{}, e, sc, acc))
    case T.BtArgs{a, rest} BkScrRest{}:
      44 <> 32 <> bk.t(a, BkTerm{}, e, sc, bk.t(rest, BkScrRest{}, e, sc, acc))
    case T.BtArgs{a, rest} BkChr{}:
      bk.t(a, BkPat{}, e, sc, bk.t(rest, BkChr{}, e, sc, acc))
    case T.BtANil{} _:
      acc
    # a match: case on the scrutinee, or on their tuple
    case T.BtMatch{+xs, cs} _:
      +multi = Nat.is_gt(T.tba.args.len(xs), 1n)
      bk.s("(case ", bk.open(multi, bk.t(xs, BkScr{}, e, sc, bk.close(multi, bk.s(" of { ", bk.t(cs, BkCases{multi}, e, sc, bk.s(" })", acc)))))))
    case T.BtCase{+p, b, rest} BkCases{+multi}:
      bk.open(multi, bk.t(p, BkList{}, e, sc, bk.close(multi, bk.s(" -> ", bk.t(b, BkTerm{}, e, bk.pv(p, sc), bk.s("; ", bk.t(rest, BkCases{multi}, e, sc, acc)))))))
    case T.BtCEnd{} _:
      acc
    # patterns
    case T.BtSucc{p} BkPat{}:
      bk.s("(b'pred -> Just ", bk.t(p, BkPat{}, e, sc, 41 <> acc))
    case T.BtCon{+c, T.BtANil{}} BkPat{}:
      bk.b(bk.con(e, c), acc)
    case T.BtCon{+c, args} BkPat{}:
      +chr = S.eq(c, S.b("Chr"))
      bk.pcon.open(chr, e, c, bk.t(args, bk.pk(chr), e, sc, bk.pcon.close(chr, acc)))
    case T.BtPv{m, x} _:
      bk.b(bk.bare(x), acc)
    case T.BtWild{} _:
      95 <> acc
    case T.BtVar{x} BkPat{}:
      bk.b(bk.bare(x), acc)
    case T.BtNat{s} BkPat{}:
      bk.b(s, acc)
    # terms
    case T.BtVar{+x} _:
      bk.b(bk.var(e, sc, x), acc)
    case T.BtApp{f, args} _:
      40 <> bk.t(f, BkTerm{}, e, sc, bk.t(args, BkArgs{}, e, sc, 41 <> acc))
    case T.BtTplArg{a} _:
      bk.t(a, BkTerm{}, e, sc, acc)
    case T.BtLam{m, +x, b} _:
      40 <> 92 <> bk.b(bk.bare(x), bk.s(" -> ", bk.t(b, BkTerm{}, e, bk.bare(x) <> sc, 41 <> acc)))
    case T.BtCon{+c, T.BtANil{}} _:
      bk.b(bk.con(e, c), acc)
    case T.BtCon{+c, args} _:
      40 <> bk.b(bk.con(e, c), bk.t(args, BkCArgs{}, e, sc, 41 <> acc))
    case T.BtLet{+x, v, b} _:
      bk.s("(case ", bk.t(v, BkTerm{}, e, sc, bk.s(" of { ", bk.b(bk.bare(x), bk.s(" -> ", bk.t(b, BkTerm{}, e, bk.bare(x) <> sc, bk.s(" })", acc)))))))
    case T.BtRw{r, p, b} _:
      bk.t(b, BkTerm{}, e, sc, acc)
    case T.BtExpr{a} _:
      bk.t(a, BkTerm{}, e, sc, acc)
    case T.BtAnn{a, ty} _:
      bk.t(a, BkTerm{}, e, sc, acc)
    case T.BtDead{a} _:
      bk.t(a, BkTerm{}, e, sc, acc)
    case T.BtNat{s} _:
      bk.b(s, acc)
    case T.BtSucc{a} _:
      bk.s("(1 + ", bk.t(a, BkTerm{}, e, sc, 41 <> acc))
    case T.BtStr{s} _:
      34 <> bk.str(s, 34 <> acc)
    case _ _:
      bk.s("b'todo", acc)

# Types -----------------------------------------------------------------------------

# a field's type (tvs: the type's parameters, lowercase in Haskell; top: a
# whole type, args: a type application's arguments, each after a space,
# quantities dropped)
type BkY is Data:
  BkYTop{}
  BkYArgs{}
  BkYSkip{}
  BkYEta{}
  BkYInit{}
  BkYUnit{}
  BkYDropA{n: Nat}
  BkYDropI{n: Nat}

# a quantity argument (&2), which Haskell's types do not have
def bk.isq(+t: T.Bt) -> Bool:
  match t:
    case T.BtVar{+x}:
      S.head.is(x, 38)
    case _:
      False{}

def bk.yk(skip: Bool) -> BkY:
  match skip:
    case True{}:
      BkYSkip{}
    case False{}:
      BkYTop{}

# whether an argument spine ends with the variable x
def bk.args.ends(+a: T.Bt, +x: List<&2, U32>) -> Bool:
  match a:
    case T.BtArgs{T.BtVar{+y}, T.BtANil{}}:
      S.eq(y, x)
    case T.BtArgs{h, r}:
      bk.args.ends(r, x)
    case _:
      False{}

# a type function x => D<A.., x> is Haskell's D A.. (eta: its body printed
# without its last argument); another is beyond Haskell's types (unit:
# printed as ())
def bk.ty.eta(+b: T.Bt, +x: List<&2, U32>) -> Bool:
  match b:
    case T.BtTyApp{n, +args}:
      bk.args.ends(args, x)
    case _:
      False{}

# x => D<A.., x> by eta, _ => B as B (a constant type function, Sigma's
# second argument), another as ()
def bk.etak(eta: Bool, const: Bool) -> BkY:
  match eta const:
    case True{} _:
      BkYEta{}
    case False{} True{}:
      BkYTop{}
    case False{} False{}:
      BkYUnit{}

def bk.ty(t: T.Bt, k: BkY, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match t k:
    case _ BkYSkip{}:
      acc
    case _ BkYUnit{}:
      bk.s("()", acc)
    case T.BtTyApp{+n, args} BkYEta{}:
      40 <> bk.b(bk.tname(e, n), bk.ty(args, BkYDropI{bk.kd.find(bk.kd(e), n)}, e, tvs, 41 <> acc))
    case _ BkYEta{}:
      bk.s("()", acc)
    case T.BtArgs{a, rest} BkYDropA{1n+p}:
      bk.ty(rest, BkYDropA{p}, e, tvs, acc)
    case T.BtArgs{+a, rest} BkYDropA{0n}:
      bk.lead(bk.isq(a), bk.ty(a, bk.yk(bk.isq(a)), e, tvs, bk.ty(rest, BkYArgs{}, e, tvs, acc)))
    case T.BtArgs{a, rest} BkYDropI{1n+p}:
      bk.ty(rest, BkYDropI{p}, e, tvs, acc)
    case T.BtArgs{a, T.BtANil{}} BkYDropI{0n}:
      acc
    case T.BtArgs{+a, rest} BkYDropI{0n}:
      bk.lead(bk.isq(a), bk.ty(a, bk.yk(bk.isq(a)), e, tvs, bk.ty(rest, BkYInit{}, e, tvs, acc)))
    case T.BtArgs{a, T.BtANil{}} BkYInit{}:
      acc
    case T.BtArgs{+a, rest} BkYInit{}:
      bk.lead(bk.isq(a), bk.ty(a, bk.yk(bk.isq(a)), e, tvs, bk.ty(rest, BkYInit{}, e, tvs, acc)))
    case T.BtArgs{+a, rest} BkYArgs{}:
      bk.lead(bk.isq(a), bk.ty(a, bk.yk(bk.isq(a)), e, tvs, bk.ty(rest, BkYArgs{}, e, tvs, acc)))
    case T.BtANil{} _:
      acc
    case T.BtTyApp{+n, T.BtANil{}} _:
      bk.b(bk.tname(e, n), acc)
    case T.BtTyApp{+n, args} _:
      40 <> bk.b(bk.tname(e, n), bk.ty(args, BkYDropA{bk.kd.find(bk.kd(e), n)}, e, tvs, 41 <> acc))
    case T.BtVar{+x} _:
      bk.b(Bool.pick(List<&2, U32>, S.mem(x, tvs), bk.lower1(x), bk.tname(e, x)), acc)
    case T.BtPi{m, x, d, a, b} _:
      40 <> bk.ty(a, BkYTop{}, e, tvs, bk.s(" -> ", bk.ty(b, BkYTop{}, e, tvs, 41 <> acc)))
    case T.BtLam{m, +x, +b} _:
      bk.ty(b, bk.etak(bk.ty.eta(b, x), S.eq(x, S.b("_"))), e, tvs, acc)
    case _ _:
      bk.s("()", acc)

# Items -----------------------------------------------------------------------------

def bk.law(+r: T.Bt) -> Bool:
  match r:
    case T.BtEq{t, a, b}:
      True{}
    case _:
      False{}

def bk.param(kind: Bool, +x: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match kind:
    case True{}:
      rest
    case False{}:
      32 <> bk.b(bk.bare(x), rest)

def bk.params(ps: List<&2, T.BParam>, acc: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      acc
    case T.BParam{m, +x, +ty} <> t:
      bk.param(bk.kind(ty), x, bk.params(t, acc))

# the parameters' names, the def's first locals
def bk.pnames(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      bk.bare(x) <> bk.pnames(t)

def bk.tvs(ps: List<&2, T.BParam>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case T.BParam{m, x, ty} <> t:
      x <> bk.tvs(t)

def bk.tvs.text(xs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      32 <> bk.b(bk.lower1(x), bk.tvs.text(t, acc))

# h's types, printed: a whole type, or a tuple's elements (first: before
# the first)
type BkH is Data:
  BkHTop{}
  BkHTup{first: Bool}

def bk.hk.ty(t: BkT, k: BkH, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match t k:
    case BkTArgs{a, r} BkHTup{True{}}:
      bk.hk.ty(a, BkHTop{}, e, bk.hk.ty(r, BkHTup{False{}}, e, acc))
    case BkTArgs{a, r} BkHTup{False{}}:
      44 <> 32 <> bk.hk.ty(a, BkHTop{}, e, bk.hk.ty(r, BkHTup{False{}}, e, acc))
    case BkTArgs{a, r} BkHTop{}:
      32 <> bk.hk.ty(a, BkHTop{}, e, bk.hk.ty(r, BkHTop{}, e, acc))
    case BkTNil{} _:
      acc
    case BkTv{+n} _:
      bk.b(bk.lower1(n), acc)
    case BkTh{+n, BkTNil{}} _:
      bk.b(n, acc)
    case BkTh{+n, a} _:
      40 <> bk.b(n, bk.hk.ty(a, BkHTop{}, e, 41 <> acc))
    case BkTc{+n, BkTNil{}} _:
      bk.b(bk.tname(e, n), acc)
    case BkTc{+n, a} _:
      40 <> bk.b(bk.tname(e, n), bk.hk.ty(a, BkHTop{}, e, 41 <> acc))
    case BkTList{a} _:
      91 <> bk.hk.ty(a, BkHTop{}, e, 93 <> acc)
    case BkTTup{xs} _:
      40 <> bk.hk.ty(xs, BkHTup{True{}}, e, 41 <> acc)
    case BkTFun{a, b} _:
      40 <> bk.hk.ty(a, BkHTop{}, e, bk.s(" -> ", bk.hk.ty(b, BkHTop{}, e, 41 <> acc)))
    case _ _:
      bk.s("()", acc)

# x'i, the i-th of a tuple's elements in a converter
def bk.xv(+i: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  120 <> 39 <> bk.b(S.b(Nat.show(i)), acc)

# A converter between Bend's shape of h's type and h's own (up: Bend's to
# h's, else back), as a Haskell function: a tuple's is a lambda from its
# nested pairs to h's tuple (or back), a list's, a Maybe's, an Either's
# BendRt's maps of its elements' (b'cvL, b'cvM, b'cvE), a function's the
# argument's back and the result's up (b'cvF), any other the identity.
# Its parts: an element of a tuple (El: x'i, converted when F reshapes it),
# a tuple's elements flat (h's) or nested (Bend's), as a pattern of x'i or
# as the elements converted.
type BkC is Data:
  BkCFun{}
  BkCId{}
  BkCMaybe{}
  BkCEither{}
  BkCEl{i: Nat}
  BkCElRe{i: Nat}
  BkCElId{i: Nat}
  BkCFlat{i: Nat, first: Bool}
  BkCNest{i: Nat}
  BkCPatF{i: Nat, first: Bool}
  BkCPatN{i: Nat}

def bk.tup.lead(first: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match first:
    case True{}:
      40 <> acc
    case False{}:
      44 <> 32 <> acc

# a tuple's converter's pattern and body: from nested pairs to h's flat
# tuple (up), or from flat to nested
def bk.cv.pat(up: Bool) -> BkC:
  match up:
    case True{}:
      BkCPatN{1n}
    case False{}:
      BkCPatF{1n, True{}}

def bk.cv.body(up: Bool) -> BkC:
  match up:
    case True{}:
      BkCFlat{1n, True{}}
    case False{}:
      BkCNest{1n}

def bk.cv.thk(+n: List<&2, U32>) -> BkC:
  Bool.pick(BkC, S.eq(n, S.b("Maybe")), BkCMaybe{}, Bool.pick(BkC, S.eq(n, S.b("Either")), BkCEither{}, BkCId{}))

def bk.cv.el(re: Bool, +i: Nat) -> BkC:
  match re:
    case True{}:
      BkCElRe{i}
    case False{}:
      BkCElId{i}

def bk.cvt(fuel: Nat, +t: BkT, +up: Bool, k: BkC, acc: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      bk.s("b'todo", acc)
    case 1n+(+p):
      match t k:
        case _ BkCEl{+i}:
          bk.cvt(p, t, up, bk.cv.el(bk.hk.re(t), i), acc)
        case _ BkCElId{+i}:
          bk.xv(i, acc)
        case _ BkCElRe{+i}:
          40 <> bk.cvt(p, t, up, BkCFun{}, 32 <> bk.xv(i, 41 <> acc))
        case BkTTup{+xs} BkCFun{}:
          bk.s("(\\", bk.cvt(p, xs, up, bk.cv.pat(up), bk.s(" -> ", bk.cvt(p, xs, up, bk.cv.body(up), 41 <> acc))))
        case BkTList{a} BkCFun{}:
          bk.s("(b'cvL ", bk.cvt(p, a, up, BkCFun{}, 41 <> acc))
        case BkTh{+n, a} BkCFun{}:
          bk.cvt(p, a, up, bk.cv.thk(n), acc)
        case BkTFun{a, b} BkCFun{}:
          bk.s("(b'cvF ", bk.cvt(p, a, Bool.not(up), BkCFun{}, 32 <> bk.cvt(p, b, up, BkCFun{}, 41 <> acc)))
        case BkTArgs{a, r} BkCMaybe{}:
          bk.s("(b'cvM ", bk.cvt(p, a, up, BkCFun{}, 41 <> acc))
        case BkTArgs{a, BkTArgs{b, r}} BkCEither{}:
          bk.s("(b'cvE ", bk.cvt(p, a, up, BkCFun{}, 32 <> bk.cvt(p, b, up, BkCFun{}, 41 <> acc)))
        case BkTArgs{a, r} BkCFlat{+i, first}:
          bk.tup.lead(first, bk.cvt(p, a, up, BkCEl{i}, bk.cvt(p, r, up, BkCFlat{1n+i, False{}}, acc)))
        case BkTNil{} BkCFlat{i, first}:
          41 <> acc
        case BkTArgs{a, BkTNil{}} BkCNest{+i}:
          bk.cvt(p, a, up, BkCEl{i}, acc)
        case BkTArgs{a, r} BkCNest{+i}:
          40 <> bk.cvt(p, a, up, BkCEl{i}, bk.s(", ", bk.cvt(p, r, up, BkCNest{1n+i}, 41 <> acc)))
        case BkTArgs{a, r} BkCPatF{+i, first}:
          bk.tup.lead(first, bk.xv(i, bk.cvt(p, r, up, BkCPatF{1n+i, False{}}, acc)))
        case BkTNil{} BkCPatF{i, first}:
          41 <> acc
        case BkTArgs{a, BkTNil{}} BkCPatN{+i}:
          bk.xv(i, acc)
        case BkTArgs{a, r} BkCPatN{+i}:
          40 <> bk.xv(i, bk.s(", ", bk.cvt(p, r, up, BkCPatN{1n+i}, 41 <> acc)))
        case _ BkCFun{}:
          bk.s("b'id", acc)
        case _ _:
          bk.s("b'id", acc)

# a field's h type (the first of ns; none known: BkTNo)
def bk.hk.hd(ns: List<&2, BkT>) -> BkT:
  match ns:
    case h <> t:
      h
    case Nil{}:
      BkTNo{}

# h's number type, when it is Int, Integer or Natural (else empty)
def bk.hk.num(t: BkT) -> List<&2, U32>:
  match t:
    case BkTh{+n, BkTNil{}}:
      Bool.pick(List<&2, U32>, Bool.or(S.eq(n, S.b("Int")), Bool.or(S.eq(n, S.b("Integer")), S.eq(n, S.b("Natural")))), n, Nil{})
    case _:
      Nil{}

# a1 a2 .. an, each after a space (k: the next's number)
def bk.anames(n: Nat, +k: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      32 <> 97 <> bk.b(S.b(Nat.show(k)), bk.anames(p, 1n+k, acc))

def bk.ps.arg(cv: Bool, pat: Bool, +h: BkT, +i: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match cv pat:
    case True{} True{}:
      40 <> bk.cvt(64n, h, False{}, BkCFun{}, bk.s(" -> a", bk.b(S.b(Nat.show(i)), 41 <> acc)))
    case True{} False{}:
      40 <> bk.cvt(64n, h, True{}, BkCFun{}, bk.s(" a", bk.b(S.b(Nat.show(i)), 41 <> acc)))
    case False{} _:
      97 <> bk.b(S.b(Nat.show(i)), acc)

# A constructor with a field F reshapes: h's data type is printed with h's
# field types, and G's terms and patterns reach it through a bidirectional
# pattern synonym that converts each such field (Bend's shape to h's when
# it builds, back when it matches):
#   pattern P'C a1 .. an <- C (DOWN1 -> a1) .. an where P'C a1 .. an = C (UP1 a1) .. an
def bk.ps.args(ns: List<&2, BkT>, +i: Nat, +pat: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      acc
    case +h <> t:
      32 <> bk.ps.arg(bk.hk.cv(h), pat, h, i, bk.ps.args(t, 1n+i, pat, acc))

def bk.psyn(cv: Bool, +c: List<&2, U32>, +ns: List<&2, BkT>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match cv:
    case True{}:
      +p = bk.s("P'", bk.dots(c))
      +k = List.length(&2, BkT, ns)
      +hc = bk.con.pv(False{}, False{}, e, c, bk.init(c))
      bk.s("pattern ", bk.b(p, bk.anames(k, 1n, bk.s(" <- ", bk.b(hc, bk.ps.args(ns, 1n, True{}, bk.s(" where ", bk.b(p, bk.anames(k, 1n, bk.s(" = ", bk.b(hc, bk.ps.args(ns, 1n, False{}, 10 <> 10 <> acc))))))))))))
    case False{}:
      acc

def bk.psyns(cs: List<&2, T.BCtor>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case T.BCtor{+c, fs} <> t:
      bk.psyn(S.mem(c, bk.cvs(e)), c, bk.nf.find(bk.nf(e), c), e, bk.psyns(t, e, acc))

def bk.isnat(+t: T.Bt) -> Bool:
  match t:
    case T.BtVar{+x}:
      S.eq(x, S.b("Nat"))
    case T.BtTyApp{+x, T.BtANil{}}:
      S.eq(x, S.b("Nat"))
    case _:
      False{}

# a field's type: h's where F reshapes it (cv), h's number type n where
# Bend's is Nat (num), else G's
def bk.field.at(cv: Bool, num: Bool, +n: List<&2, U32>, h: BkT, ty: T.Bt, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match cv num:
    case True{} _:
      bk.hk.ty(h, BkHTop{}, e, acc)
    case False{} True{}:
      bk.b(n, acc)
    case False{} False{}:
      bk.ty(ty, BkYTop{}, e, tvs, acc)

# the fields (ns: h's types, by field)
def bk.fields(fs: List<&2, T.BField>, +ns: List<&2, BkT>, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      acc
    case T.BField{x, +ty} <> t:
      +h = bk.hk.hd(ns)
      +n = bk.hk.num(h)
      32 <> bk.field.at(bk.hk.cv(h), Bool.and(Bool.not(List.is_empty(&2, U32, n)), bk.isnat(ty)), n, h, ty, e, tvs, bk.fields(t, List.drop(&2, BkT, ns, 1n), e, tvs, acc))

def bk.ctors(cs: List<&2, T.BCtor>, first: Bool, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs first:
    case Nil{} _:
      acc
    case T.BCtor{+c, fs} <> t True{}:
      bk.s(" = ", bk.b(bk.con.h(True{}, e, c), bk.fields(fs, bk.nf.find(bk.nf(e), c), e, tvs, bk.ctors(t, False{}, e, tvs, acc))))
    case T.BCtor{+c, fs} <> t False{}:
      bk.s(" | ", bk.b(bk.con.h(True{}, e, c), bk.fields(fs, bk.nf.find(bk.nf(e), c), e, tvs, bk.ctors(t, False{}, e, tvs, acc))))

def bk.def(islaw: Bool, +n: List<&2, U32>, +ps: List<&2, T.BParam>, body: T.Bt, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match islaw:
    case True{}:
      acc
    case False{}:
      bk.b(bk.dname(n), bk.params(ps, bk.s(" = ", bk.t(body, BkTerm{}, e, bk.pnames(ps), 10 <> 10 <> acc))))

def bk.item(it: T.BItem, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match it:
    case T.BiDef{+n, ps, +ret, body, doc}:
      bk.def(bk.law(ret), n, ps, body, e, acc)
    case T.BiType{+n, +ps, k, +cs, doc}:
      bk.s("data ", bk.b(bk.tname.at(True{}, True{}, e, n), bk.tvs.text(List.drop(&2, List<&2, U32>, bk.tvs(ps), bk.kd.find(bk.kd(e), n)), bk.ctors(cs, True{}, e, bk.tvs(ps), 10 <> 10 <> bk.psyns(cs, e, acc)))))
    case _:
      acc

def bk.items(its: List<&2, T.BItem>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match its:
    case Nil{}:
      acc
    case it <> t:
      bk.item(it, e, bk.items(t, e, acc))

# the value parameters' count (a type's are erased)
def bk.nvals(ps: List<&2, T.BParam>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case T.BParam{m, x, +ty} <> t:
      +k = bk.nvals(t)
      Bool.pick(Nat, bk.kind(ty), k, 1n+k)

def bk.pt.add(yes: Bool, n: List<&2, U32>, ps: List<&2, T.BParam>, pt: List<&2, BkP>) -> List<&2, BkP>:
  match yes:
    case True{}:
      BkP{n, bk.nvals(ps)} <> pt
    case False{}:
      pt

# a partial def's value parameters' count, if b is one
def bk.pt.find(ps: List<&2, BkP>, +b: List<&2, U32>) -> Maybe<&2, Nat>:
  match ps:
    case Nil{}:
      None{}
    case BkP{+b2, k} <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(b2, b), Some{k}, bk.pt.find(t, b))

# the module's Bend names: its defs (laws too: never called), its types
# and its partial defs
def bk.env.go(its: List<&2, T.BItem>, ds: List<&2, List<&2, U32>>, ts: List<&2, List<&2, U32>>, pt: List<&2, BkP>, +nm: BkN) -> Bk:
  match its:
    case Nil{}:
      match nm:
        case BkN{m, as, tn, cn, pd, nf, kd}:
          Bk{m, ds, ts, tn, cn, pt, nf, kd, bk.cv(nf)}
    case T.BiDef{+n, ps, r, b, d} <> t:
      bk.env.go(t, n <> ds, ts, bk.pt.add(S.mem(n, bk.nm.pd(nm)), n, ps, pt), nm)
    case T.BiType{n, ps, k, cs, d} <> t:
      bk.env.go(t, ds, n <> ts, pt, nm)
    case _ <> t:
      bk.env.go(t, ds, ts, pt, nm)

# G(F(h)) at h's type: a partial def's Either unwrapped (its Inl{m} h's
# error m again, b'unfail), under a lambda of its value parameters
def bk.alias.body(pt: Maybe<&2, Nat>, +b: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match pt:
    case None{}:
      bk.b(bk.dname(b), acc)
    case Some{0n}:
      bk.s("(b'unfail ", bk.b(bk.dname(b), 41 <> acc))
    case Some{+k}:
      bk.s("(\\", bk.anames(k, 1n, bk.s(" -> b'unfail (", bk.b(bk.dname(b), bk.anames(k, 1n, bk.s("))", acc))))))

# h's name: b'up, the round trip's iso at h's type (BendRt's B'Up: G's
# nested pairs as h's tuples), of G(F(h))
def bk.alias(has: Bool, +e: Bk, +h: List<&2, U32>, +b: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match has:
    case True{}:
      bk.b(bk.alias.name(h), bk.s(" = b'up ", bk.alias.body(bk.pt.find(bk.pt(e), b), b, 10 <> rest)))
    case False{}:
      rest

def bk.aliases(as: List<&2, BkA>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match as:
    case Nil{}:
      acc
    case BkA{+h, +b} <> t:
      bk.alias(S.mem(b, bk.defs(e)), e, h, b, bk.aliases(t, e, acc))

# whether a def is printed under the Haskell name h
def bk.aliased(as: List<&2, BkA>, +e: Bk, +h: List<&2, U32>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case BkA{+h2, +b} <> t:
      Bool.or(Bool.and(S.eq(h2, h), S.mem(b, bk.defs(e))), bk.aliased(t, e, h))

# a module Main without its main (laws never run it) gets BendRt's
def bk.main(need: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match need:
    case True{}:
      bk.s("main = b'main\n", acc)
    case False{}:
      acc

# the module: file the export it came from, its, the items (in the order
# Bend checked them), nm its names (as BkN says)
def bk.module(+file: List<&2, U32>, +its: List<&2, T.BItem>, +nm: BkN) -> List<&2, U32>:
  +e = bk.env.go(its, Nil{}, Nil{}, Nil{}, nm)
  +m = bk.nm.m(nm)
  +as = bk.nm.as(nm)
  bk.s("{-# LANGUAGE ViewPatterns, PatternSynonyms, NoMonomorphismRestriction, TypeOperators, TypeFamilies, FlexibleContexts #-}\n-- bend2hs (cata's bend/Back.bend) of the Bend cata wrote from ", bk.b(file, bk.s("\nmodule ", bk.b(m, bk.s(" where\nimport Prelude ()\nimport BendRt\n\n", bk.items(its, e, bk.aliases(as, e, bk.main(Bool.and(S.eq(m, S.b("Main")), Bool.not(bk.aliased(as, e, S.b("main")))), Nil{}))))))))
