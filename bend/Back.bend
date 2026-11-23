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
#   a type, an arrow, or a name whose last part is capitalized or a
#   quantity (&2), and a parameter whose type is Data, Type or a kind;
# - Base's and the prelude's names (anything with a dot that the module
#   does not define) are prelude/Back/BendRt.hs's, each `b'` and the name
#   with its dots as primes (List.append is b'List'append), Base's
#   constructors Haskell's own (Con is (:), Some Just, Inl Left, Tuple (,));
# - the module's defs are `c'` and their Bend names (dots as primes), and
#   each def that GHC knows by a Haskell name (laws: the TbFun's) is that
#   name too, `name = c'name` (an operator in parentheses);
# - a type of the module is its Haskell data type, its constructors
#   Haskell's names (T.C is C); a type cata made (a group's .mu.In, a twin)
#   is T' and its name, its constructors C' and theirs;
# - match is case, on a tuple of the scrutinees when there are several; a
#   Nat pattern 1n+p is the view (b'pred -> Just p); a let is let; Bend's
#   types become BendRt's synonyms (Nat is Int: cata writes Int as Nat only
#   where nothing subtracts).
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

def bk.head.upper(xs: List<&2, U32>) -> Bool:
  match xs:
    case +c <> t:
      bk.upper(c)
    case Nil{}:
      False{}

def bk.lower1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case +c <> t:
      Bool.pick(U32, bk.upper(c), U32.add(c, 32), c) <> t
    case Nil{}:
      Nil{}

# what the module defines: its defs' and its types' Bend names
type Bk is Data:
  Bk{defs: List<&2, List<&2, U32>>, tys: List<&2, List<&2, U32>>}

def bk.defs(+e: Bk) -> List<&2, List<&2, U32>>:
  match e:
    case Bk{d, t}:
      d

def bk.tys(+e: Bk) -> List<&2, List<&2, U32>>:
  match e:
    case Bk{d, t}:
      t

def bk.dname(+x: List<&2, U32>) -> List<&2, U32>:
  99 <> 39 <> bk.dots(x)

# a name in a term: the module's def, a char literal, Base's or the
# prelude's (dotted), or a local
def bk.var.at(own: Bool, chr: Bool, dot: Bool, +x: List<&2, U32>) -> List<&2, U32>:
  match own chr dot:
    case True{} _ _:
      bk.dname(x)
    case False{} True{} _:
      x
    case False{} False{} True{}:
      98 <> 39 <> bk.dots(x)
    case False{} False{} False{}:
      x

def bk.var(+e: Bk, +x: List<&2, U32>) -> List<&2, U32>:
  bk.var.at(S.mem(x, bk.defs(e)), S.head.is(x, 39), bk.has.dot(x), x)

# a type's Haskell name: the module's own (plain) as it is, one cata made
# T' and its name, Base's BendRt's synonym
def bk.tname.at(own: Bool, plain: Bool, +n: List<&2, U32>) -> List<&2, U32>:
  match own plain:
    case True{} True{}:
      n
    case True{} False{}:
      84 <> 39 <> bk.dots(n)
    case False{} _:
      66 <> 39 <> bk.dots(n)

def bk.tname(+e: Bk, +n: List<&2, U32>) -> List<&2, U32>:
  bk.tname.at(S.mem(n, bk.tys(e)), Bool.and(bk.head.upper(n), Bool.not(bk.has.dot(n))), n)

# Base's constructors as Haskell's
def bk.con.base(+c: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, S.eq(c, S.b("Con")), S.b("(:)"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Nil")), S.b("[]"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Tuple")), S.b("(,)"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Some")), S.b("Just"), Bool.pick(List<&2, U32>, S.eq(c, S.b("None")), S.b("Nothing"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Inl")), S.b("Left"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Inr")), S.b("Right"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Unit")), S.b("()"), Bool.pick(List<&2, U32>, S.eq(c, S.b("Chr")), S.b("b'chr"), Bool.pick(List<&2, U32>, bk.has.dot(c), 66 <> 39 <> bk.dots(c), c))))))))))

# a constructor: the module's type's (Haskell's name, or C' for a type cata
# made), else Base's
def bk.con.at(own: Bool, plain: Bool, +c: List<&2, U32>) -> List<&2, U32>:
  match own plain:
    case True{} True{}:
      bk.last(c)
    case True{} False{}:
      67 <> 39 <> bk.dots(c)
    case False{} _:
      bk.con.base(c)

def bk.con(+e: Bk, +c: List<&2, U32>) -> List<&2, U32>:
  +t = bk.init(c)
  bk.con.at(S.mem(t, bk.tys(e)), Bool.and(bk.head.upper(t), Bool.not(bk.has.dot(t))), c)

# whether a term is a type (an argument G erases)
def bk.isty.var(+x: List<&2, U32>) -> Bool:
  Bool.or(S.head.is(x, 38), bk.head.upper(bk.last(x)))

def bk.isty0(+t: T.Bt) -> Bool:
  match t:
    case T.BtTyApp{n, a}:
      True{}
    case T.BtType{}:
      True{}
    case T.BtPi{m, x, d, a, b}:
      True{}
    case T.BtVar{+x}:
      bk.isty.var(x)
    case _:
      False{}

def bk.isty(+t: T.Bt) -> Bool:
  match t:
    case T.BtTplArg{+a}:
      bk.isty0(a)
    case _:
      bk.isty0(t)

def bk.kind(+t: T.Bt) -> Bool:
  match t:
    case T.BtType{}:
      True{}
    case T.BtVar{+x}:
      Bool.or(S.eq(x, S.b("Data")), Bool.or(S.eq(x, S.b("Type")), S.eq(x, S.b("Quant"))))
    case T.BtApp{T.BtVar{+x}, a}:
      S.eq(x, S.b("Kind"))
    case _:
      False{}

def bk.str.esc(ok: Bool, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      c <> rest
    case False{}:
      92 <> bk.b(S.b(U32.show(c)), 92 <> 38 <> rest)

# a string's bytes as a Haskell literal's: printable ASCII but " and \ as
# they are, any other as \N\&
def bk.str(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case +c <> t:
      bk.str.esc(Bool.and(Bool.and(U32.is_ge(c, 32), U32.is_le(c, 126)), Bool.and(U32.is_ne(c, 34), U32.is_ne(c, 92))), c, bk.str(t, acc))

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

# Terms -------------------------------------------------------------------------

# where a term is printed: a term, nothing (an erased argument), an
# application's or a constructor's arguments (each after a space), a
# pattern, a constructor pattern's arguments, the scrutinees and a case's
# patterns (", " between: first, rest), a match's cases
type BkK is Data:
  BkTerm{}
  BkSkip{}
  BkArgs{}
  BkCArgs{}
  BkPat{}
  BkPArgs{}
  BkList{}
  BkListRest{}
  BkCases{multi: Bool}

def bk.argk(skip: Bool) -> BkK:
  match skip:
    case True{}:
      BkSkip{}
    case False{}:
      BkTerm{}

def bk.t(t: T.Bt, k: BkK, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match t k:
    case _ BkSkip{}:
      acc
    # argument lists
    case T.BtArgs{+a, rest} BkArgs{}:
      bk.lead(bk.isty(a), bk.t(a, bk.argk(bk.isty(a)), e, bk.t(rest, BkArgs{}, e, acc)))
    case T.BtArgs{a, rest} BkCArgs{}:
      32 <> bk.t(a, BkTerm{}, e, bk.t(rest, BkCArgs{}, e, acc))
    case T.BtArgs{a, rest} BkPArgs{}:
      32 <> bk.t(a, BkPat{}, e, bk.t(rest, BkPArgs{}, e, acc))
    case T.BtArgs{a, rest} BkList{}:
      bk.t(a, BkPat{}, e, bk.t(rest, BkListRest{}, e, acc))
    case T.BtArgs{a, rest} BkListRest{}:
      44 <> 32 <> bk.t(a, BkPat{}, e, bk.t(rest, BkListRest{}, e, acc))
    case T.BtANil{} _:
      acc
    # a match: case on the scrutinee, or on their tuple
    case T.BtMatch{+xs, cs} _:
      +multi = Nat.is_gt(T.tba.args.len(xs), 1n)
      bk.s("(case ", bk.open(multi, bk.t(xs, BkList{}, e, bk.close(multi, bk.s(" of { ", bk.t(cs, BkCases{multi}, e, bk.s(" })", acc)))))))
    case T.BtCase{p, b, rest} BkCases{+multi}:
      bk.open(multi, bk.t(p, BkList{}, e, bk.close(multi, bk.s(" -> ", bk.t(b, BkTerm{}, e, bk.s("; ", bk.t(rest, BkCases{multi}, e, acc)))))))
    case T.BtCEnd{} _:
      acc
    # patterns
    case T.BtSucc{p} BkPat{}:
      bk.s("(b'pred -> Just ", bk.t(p, BkPat{}, e, 41 <> acc))
    case T.BtCon{+c, T.BtANil{}} BkPat{}:
      bk.b(bk.con(e, c), acc)
    case T.BtCon{+c, args} BkPat{}:
      40 <> bk.b(bk.con(e, c), bk.t(args, BkPArgs{}, e, 41 <> acc))
    case T.BtPv{m, x} _:
      bk.b(x, acc)
    case T.BtWild{} _:
      95 <> acc
    case T.BtVar{x} BkPat{}:
      bk.b(x, acc)
    case T.BtNat{s} BkPat{}:
      bk.b(s, acc)
    # terms
    case T.BtVar{+x} _:
      bk.b(bk.var(e, x), acc)
    case T.BtApp{f, args} _:
      40 <> bk.t(f, BkTerm{}, e, bk.t(args, BkArgs{}, e, 41 <> acc))
    case T.BtTplArg{a} _:
      bk.t(a, BkTerm{}, e, acc)
    case T.BtLam{m, x, b} _:
      40 <> 92 <> bk.b(x, bk.s(" -> ", bk.t(b, BkTerm{}, e, 41 <> acc)))
    case T.BtCon{+c, T.BtANil{}} _:
      bk.b(bk.con(e, c), acc)
    case T.BtCon{+c, args} _:
      40 <> bk.b(bk.con(e, c), bk.t(args, BkCArgs{}, e, 41 <> acc))
    case T.BtLet{x, v, b} _:
      bk.s("(let { ", bk.b(x, bk.s(" = ", bk.t(v, BkTerm{}, e, bk.s(" } in ", bk.t(b, BkTerm{}, e, 41 <> acc))))))
    case T.BtExpr{a} _:
      bk.t(a, BkTerm{}, e, acc)
    case T.BtAnn{a, ty} _:
      bk.t(a, BkTerm{}, e, acc)
    case T.BtDead{a} _:
      bk.t(a, BkTerm{}, e, acc)
    case T.BtNat{s} _:
      bk.b(s, acc)
    case T.BtSucc{a} _:
      bk.s("(1 + ", bk.t(a, BkTerm{}, e, 41 <> acc))
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

def bk.ty(t: T.Bt, k: BkY, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match t k:
    case _ BkYSkip{}:
      acc
    case T.BtArgs{+a, rest} BkYArgs{}:
      bk.lead(bk.isq(a), bk.ty(a, bk.yk(bk.isq(a)), e, tvs, bk.ty(rest, BkYArgs{}, e, tvs, acc)))
    case T.BtANil{} _:
      acc
    case T.BtTyApp{+n, T.BtANil{}} _:
      bk.b(bk.tname(e, n), acc)
    case T.BtTyApp{+n, args} _:
      40 <> bk.b(bk.tname(e, n), bk.ty(args, BkYArgs{}, e, tvs, 41 <> acc))
    case T.BtVar{+x} _:
      bk.b(Bool.pick(List<&2, U32>, S.mem(x, tvs), bk.lower1(x), bk.tname(e, x)), acc)
    case T.BtPi{m, x, d, a, b} _:
      40 <> bk.ty(a, BkYTop{}, e, tvs, bk.s(" -> ", bk.ty(b, BkYTop{}, e, tvs, 41 <> acc)))
    case T.BtLam{m, x, b} _:
      bk.ty(b, BkYTop{}, e, tvs, acc)
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
      32 <> bk.b(x, rest)

def bk.params(ps: List<&2, T.BParam>, acc: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      acc
    case T.BParam{m, +x, +ty} <> t:
      bk.param(bk.kind(ty), x, bk.params(t, acc))

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

def bk.fields(fs: List<&2, T.BField>, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      acc
    case T.BField{x, ty} <> t:
      32 <> bk.ty(ty, BkYTop{}, e, tvs, bk.fields(t, e, tvs, acc))

def bk.ctors(cs: List<&2, T.BCtor>, first: Bool, +e: Bk, +tvs: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs first:
    case Nil{} _:
      acc
    case T.BCtor{+c, fs} <> t True{}:
      bk.s(" = ", bk.b(bk.con(e, c), bk.fields(fs, e, tvs, bk.ctors(t, False{}, e, tvs, acc))))
    case T.BCtor{+c, fs} <> t False{}:
      bk.s(" | ", bk.b(bk.con(e, c), bk.fields(fs, e, tvs, bk.ctors(t, False{}, e, tvs, acc))))

def bk.def(islaw: Bool, +n: List<&2, U32>, ps: List<&2, T.BParam>, body: T.Bt, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match islaw:
    case True{}:
      acc
    case False{}:
      bk.b(bk.dname(n), bk.params(ps, bk.s(" = ", bk.t(body, BkTerm{}, e, 10 <> 10 <> acc))))

def bk.item(it: T.BItem, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match it:
    case T.BiDef{+n, ps, +ret, body, doc}:
      bk.def(bk.law(ret), n, ps, body, e, acc)
    case T.BiType{+n, +ps, k, cs, doc}:
      bk.s("data ", bk.b(bk.tname(e, n), bk.tvs.text(bk.tvs(ps), bk.ctors(cs, True{}, e, bk.tvs(ps), 10 <> 10 <> acc))))
    case _:
      acc

def bk.items(its: List<&2, T.BItem>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match its:
    case Nil{}:
      acc
    case it <> t:
      bk.item(it, e, bk.items(t, e, acc))

# the module's names: its defs (laws too: never called) and its types
def bk.env.go(its: List<&2, T.BItem>, ds: List<&2, List<&2, U32>>, ts: List<&2, List<&2, U32>>) -> Bk:
  match its:
    case Nil{}:
      Bk{ds, ts}
    case T.BiDef{n, ps, r, b, d} <> t:
      bk.env.go(t, n <> ds, ts)
    case T.BiType{n, ps, k, cs, d} <> t:
      bk.env.go(t, ds, n <> ts)
    case _ <> t:
      bk.env.go(t, ds, ts)

# a Haskell name GHC knows a def by (hs) and its Bend name (b)
type BkA is Data:
  BkA{hs: List<&2, U32>, b: List<&2, U32>}

def bk.alias.lead(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), U32.is_eq(c, 95)), bk.upper(c))

def bk.alias.name.at(lead: Bool, +h: List<&2, U32>) -> List<&2, U32>:
  match lead:
    case True{}:
      h
    case False{}:
      40 <> bk.cat(h, [41])

# a Haskell name as a binder: an operator in parentheses
def bk.alias.name(+h: List<&2, U32>) -> List<&2, U32>:
  match h:
    case +c <> t:
      bk.alias.name.at(bk.alias.lead(c), h)
    case Nil{}:
      h

def bk.alias(has: Bool, +h: List<&2, U32>, +b: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match has:
    case True{}:
      bk.b(bk.alias.name(h), bk.s(" = ", bk.b(bk.dname(b), 10 <> rest)))
    case False{}:
      rest

def bk.aliases(as: List<&2, BkA>, +e: Bk, acc: List<&2, U32>) -> List<&2, U32>:
  match as:
    case Nil{}:
      acc
    case BkA{+h, +b} <> t:
      bk.alias(S.mem(b, bk.defs(e)), h, b, bk.aliases(t, e, acc))

# the module: m its Haskell name, file the export it came from, its, the
# items (in the order Bend checked them), as the aliases
def bk.module(+m: List<&2, U32>, +file: List<&2, U32>, +its: List<&2, T.BItem>, as: List<&2, BkA>) -> List<&2, U32>:
  +e = bk.env.go(its, Nil{}, Nil{})
  bk.s("{-# LANGUAGE ViewPatterns, NoMonomorphismRestriction #-}\n-- bend2hs (cata's bend/Back.bend) of the Bend cata wrote from ", bk.b(file, bk.s("\nmodule ", bk.b(m, bk.s(" where\nimport Prelude ()\nimport BendRt\n\n", bk.items(its, e, bk.aliases(as, e, Nil{})))))))
