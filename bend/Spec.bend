import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X

# Spec: cata hs's specialiser.  `spec OUTDIR FILE.sexp...` reads a
# package's hs-export modules (tools/hs-export/FORMAT.md) in dependency
# order and writes them again to OUTDIR (same names, and modules.txt), in
# the same format, with
#
#   - each use of a pattern synonym as a pattern replaced by the pattern
#     its matcher ($mX) matches, its arguments in its variables' places,
#     and each use as an expression by its builder ($bX);
#   - each view pattern (f -> p) whose f is the identity, a constructor, a
#     projection of a one-constructor pattern, Recursive's project or
#     Corecursive's embed at Fix or Cofree, or a composition of those
#     (through the package's instance methods), replaced by the plain
#     pattern it is;
#   - each call of a def that takes dictionaries (a class constraint), at
#     types with no variable left, replaced by a call of a copy of that def
#     at those types (NAME__TYPES), written into the module that calls it
#     (once per package: a module that imports the module that wrote it
#     names that one, see sp.work2); a method of a class at such types,
#     whose instance the package wrote by hand, by a copy of that
#     instance's method.
#
# The copies are monomorphic: their type variables are the call's types,
# so the methods they call are at known types too, and are specialised in
# turn.  A dictionary is never built: the instance is found from the types
# (the package's instances, their heads matched against the types, the
# package's synonyms and type family instances, and recursion-schemes'
# Base, applied first).  Derived instances (GHC's code) are left to the
# fold, as are base's.  Nothing is decided about Bend here; the fold,
# survey and law read the output as they read hs-export's.  Every def is
# prefixed `sp.`.

# Trees --------------------------------------------------------------------

def sp.cons(h: X.Sx, t: X.Sx) -> X.Sx:
  X.SxCons{h, t}

def sp.a(s: String) -> X.Sx:
  X.SxAtom{S.b(s)}

def sp.l(xs: List<&2, X.Sx>) -> X.Sx:
  match xs:
    case Nil{}:
      X.SxNil{}
    case h <> t:
      X.SxCons{h, sp.l(t)}

# Speed (the user, 11-22: "Improve the speed of cata's checks too"): sp.is
# made its string bytes (S.b) at every call, a third of spec's time, the
# names it tells apart being many and long. An ASCII string is now read
# beside the bytes, a char a byte; any other is made bytes as before.

# whether every char of s is below 128
def sp.ascii(+s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{c}, t}:
      Bool.and(U32.is_lt(c, 128), sp.ascii(t))

# the bytes x are the ASCII string s (ok: so far)
def sp.is.go(x: List<&2, U32>, s: String, ok: Bool) -> Bool:
  match x s ok:
    case _ _ False{}:
      False{}
    case Nil{} SNil{} True{}:
      True{}
    case b <> xt SCon{Chr{c}, st} True{}:
      sp.is.go(xt, st, U32.is_eq(b, c))
    case _ _ True{}:
      False{}

def sp.is.at(asc: Bool, +x: List<&2, U32>, s: String) -> Bool:
  match asc:
    case True{}:
      sp.is.go(x, s, True{})
    case False{}:
      S.eq(x, S.b(s))

def sp.is(+x: List<&2, U32>, +s: String) -> Bool:
  sp.is.at(sp.ascii(s), x, s)

def sp.hd(+x: X.Sx) -> List<&2, U32>:
  X.tsx.head(x)

def sp.at(+x: X.Sx, i: Nat) -> X.Sx:
  X.tsx.at(i, x)

def sp.sat(+x: X.Sx, i: Nat) -> List<&2, U32>:
  X.tsx.str.of(X.tsx.at(i, x))

# a list tree's elements
def sp.els(x: X.Sx) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{h, t}:
      h <> sp.els(t)
    case _:
      Nil{}

def sp.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def sp.eq.go(a: X.Sx, b: X.Sx) -> Bool:
  match a b:
    case X.SxAtom{x} X.SxAtom{y}:
      S.eq(x, y)
    case X.SxStr{x} X.SxStr{y}:
      S.eq(x, y)
    case X.SxNil{} X.SxNil{}:
      True{}
    case X.SxCons{h1, t1} X.SxCons{h2, t2}:
      Bool.and(sp.eq.go(h1, h2), sp.eq.go(t1, t2))
    case _ _:
      False{}

def sp.eq(+a: X.Sx, +b: X.Sx) -> Bool:
  sp.eq.go(a, b)

# whether the atom a occurs anywhere in x
def sp.has(x: X.Sx, +a: List<&2, U32>) -> Bool:
  match x:
    case X.SxAtom{s}:
      S.eq(s, a)
    case X.SxCons{h, t}:
      Bool.or(sp.has(h, a), sp.has(t, a))
    case _:
      False{}

# the node (g M N K)
def sp.g(m: List<&2, U32>, n: List<&2, U32>, k: String) -> X.Sx:
  sp.l([sp.a("g"), X.SxStr{m}, X.SxStr{n}, sp.a(k)])

# a name's key, M.N
def sp.key(m: List<&2, U32>, n: List<&2, U32>) -> List<&2, U32>:
  sp.cat(m, 46 <> n)

# a node's first atom, whether it heads x: (pcon ...) is a pcon node
def sp.head.is(+x: X.Sx, s: String) -> Bool:
  sp.is(sp.hd(x), s)

# an if whose branches are thunks (Bool.pick computes both)
def sp.if(-R: Type, c: Bool, t: Unit -> R, e: Unit -> R) -> R:
  match c:
    case True{}:
      t(Unit{})
    case False{}:
      e(Unit{})

# Types ----------------------------------------------------------------------

# a type variable's value
type Sb is Data:
  Sb{v: List<&2, U32>, t: X.Sx}

def sp.sb.get(sbs: List<&2, Sb>, +v: List<&2, U32>, d: X.Sx) -> X.Sx:
  match sbs:
    case Nil{}:
      d
    case Sb{+w, +t} <> r:
      Bool.pick(X.Sx, S.eq(w, v), t, sp.sb.get(r, v, d))

def sp.sb.has(sbs: List<&2, Sb>, +v: List<&2, U32>) -> Bool:
  match sbs:
    case Nil{}:
      False{}
    case Sb{+w, t} <> r:
      Bool.or(S.eq(w, v), sp.sb.has(r, v))

def sp.isstr(x: X.Sx) -> Bool:
  match x:
    case X.SxStr{s}:
      True{}
    case _:
      False{}

# whether (h . t) is (tv NAME)
def sp.istv(+h: X.Sx, +t: X.Sx) -> Bool:
  Bool.and(sp.is(X.tsx.atom.of(h), "tv"), Bool.and(sp.eq(sp.at(t, 1n), X.SxNil{}), sp.isstr(sp.at(t, 0n))))

# each (tv V) whose V has a value, replaced by it
def sp.subst(x: X.Sx, +sbs: List<&2, Sb>) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(X.Sx, sp.istv(h, t), sp.sb.get(sbs, X.tsx.str.of(sp.at(t, 0n)), X.SxCons{h, t}), X.SxCons{sp.subst(h, sbs), sp.subst(t, sbs)})
    case y:
      y

# whether a type has no variable
def sp.closed(+t: X.Sx) -> Bool:
  Bool.not(sp.has(t, S.b("tv")))

def sp.all.closed(ts: List<&2, X.Sx>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> r:
      Bool.and(sp.closed(t), sp.all.closed(r))

# a pattern type p against a type with no variables: the values of p's
# variables, or None
def sp.bind(+v: List<&2, U32>, +t: X.Sx, acc: Maybe<&2, List<&2, Sb>>) -> Maybe<&2, List<&2, Sb>>:
  match acc:
    case None{}:
      None{}
    case Some{+sbs}:
      Bool.pick(Maybe<&2, List<&2, Sb>>, sp.sb.has(sbs, v), Bool.pick(Maybe<&2, List<&2, Sb>>, sp.eq(sp.sb.get(sbs, v, X.SxNil{}), t), Some{sbs}, None{}), Some{Sb{v, t} <> sbs})

# a list's elements but the last, and its last (SxNil when empty)
def sp.ty.init.go(t: List<&2, X.Sx>, x: X.Sx) -> List<&2, X.Sx>:
  match t:
    case Nil{}:
      Nil{}
    case y <> r:
      x <> sp.ty.init.go(r, y)

def sp.ty.init(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.ty.init.go(t, x)

def sp.ty.last.go(t: List<&2, X.Sx>, x: X.Sx) -> X.Sx:
  match t:
    case Nil{}:
      x
    case y <> r:
      sp.ty.last.go(r, y)

def sp.ty.last(xs: List<&2, X.Sx>) -> X.Sx:
  match xs:
    case Nil{}:
      X.SxNil{}
    case x <> t:
      sp.ty.last.go(t, x)

# a node (A P Q) against t: (tapp P Q), a variable applied (an instance
# head (f x)), against (tc M N a1 .. an), n > 0, a type constructor
# applied and written whole (sp.norm's form), is P against (tc M N a1 ..
# an-1) and Q against an; else t is (A P' Q'), P against P', Q against Q'
def sp.match(p: X.Sx, +t: X.Sx, +acc: Maybe<&2, List<&2, Sb>>) -> Maybe<&2, List<&2, Sb>>:
  match p:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+pp, X.SxCons{+pq, X.SxNil{}}}}:
      +es = sp.els(t)
      +n = List.length(&2, X.Sx, es)
      +app = Bool.and(sp.is(a, "tapp"), Bool.and(sp.head.is(t, "tc"), Nat.is_gt(n, 3n)))
      +same = Bool.and(S.eq(a, X.tsx.atom.of(sp.at(t, 0n))), Nat.is_eq(n, 3n))
      sp.if(Maybe<&2, List<&2, Sb>>, app, _ => sp.match(pq, sp.ty.last(es), sp.match(pp, sp.l(sp.ty.init(es)), acc)), _ => sp.if(Maybe<&2, List<&2, Sb>>, same, _ => sp.match(pq, sp.at(t, 2n), sp.match(pp, sp.at(t, 1n), acc)), _ => None{}))
    case X.SxCons{+ph, +pt}:
      Bool.pick(Maybe<&2, List<&2, Sb>>, sp.istv(ph, pt), sp.bind(X.tsx.str.of(sp.at(pt, 0n)), t, acc), sp.match(pt, X.tsx.args(t), sp.match(ph, sp.at(t, 0n), acc)))
    case X.SxAtom{a}:
      Bool.pick(Maybe<&2, List<&2, Sb>>, S.eq(a, X.tsx.atom.of(t)), acc, None{})
    case X.SxStr{a}:
      Bool.pick(Maybe<&2, List<&2, Sb>>, S.eq(a, X.tsx.str.of(t)), acc, None{})
    case X.SxNil{}:
      Bool.pick(Maybe<&2, List<&2, Sb>>, sp.eq(t, X.SxNil{}), acc, None{})

def sp.match.all(ps: List<&2, X.Sx>, ts: List<&2, X.Sx>, acc: Maybe<&2, List<&2, Sb>>) -> Maybe<&2, List<&2, Sb>>:
  match ps ts:
    case p <> pr t <> tr:
      sp.match.all(pr, tr, sp.match(p, t, acc))
    case Nil{} Nil{}:
      acc
    case _ _:
      None{}

# a type's leading (tforall V ...) names, in order
def sp.foralls(t: X.Sx) -> List<&2, List<&2, U32>>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+v}, X.SxCons{+b, X.SxNil{}}}}:
      Bool.pick(List<&2, List<&2, U32>>, sp.is(a, "tforall"), v <> sp.foralls(b), Nil{})
    case _:
      Nil{}

# a type without its leading foralls and contexts
def sp.strip(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+v, X.SxCons{+b, X.SxNil{}}}}:
      Bool.pick(X.Sx, Bool.or(sp.is(a, "tforall"), sp.is(a, "tctx")), sp.strip(b), X.SxCons{X.SxAtom{a}, X.SxCons{v, X.SxCons{b, X.SxNil{}}}})
    case u:
      u

# the substitution of names by types
def sp.zip(vs: List<&2, List<&2, U32>>, ts: List<&2, X.Sx>) -> List<&2, Sb>:
  match vs ts:
    case v <> vr t <> tr:
      Sb{v, t} <> sp.zip(vr, tr)
    case _ _:
      Nil{}

# The package's index --------------------------------------------------------

# a def that takes dictionaries: its key M.N and its top
type Df is Data:
  Df{k: List<&2, U32>, top: X.Sx}

# a top that exports a local (an instance's method): its module, name, number
type Lc is Data:
  Lc{m: List<&2, U32>, n: List<&2, U32>, i: List<&2, U32>, top: X.Sx}

# a pattern synonym: its module, name, universal type variables, the
# variables of its matcher's pattern standing for its arguments, in order,
# and that pattern
type Ps is Data:
  Ps{m: List<&2, U32>, n: List<&2, U32>, tvs: List<&2, List<&2, U32>>, bs: List<&2, X.Sx>, pat: X.Sx}

# an instance: its class (M.C), its head's types, the module of its
# dictionary's def, that def's type variables and its constructor's
# arguments (superclasses' dictionaries, then the methods)
type In is Data:
  In{c: List<&2, U32>, head: List<&2, X.Sx>, m: List<&2, U32>, tvs: List<&2, List<&2, U32>>, args: List<&2, X.Sx>}

# a class: its key, its type variables' count, its superclasses' count and
# its methods
type Cl is Data:
  Cl{k: List<&2, U32>, ntv: Nat, nsup: Nat, ms: List<&2, List<&2, U32>>}

# a synonym, a type family's instance
type Sy is Data:
  Sy{k: List<&2, U32>, tvs: List<&2, List<&2, U32>>, rhs: X.Sx}

type Fm is Data:
  Fm{k: List<&2, U32>, lhs: List<&2, X.Sx>, rhs: X.Sx}

# a constructor of the package's (a data's or a newtype's): its key M.C and
# its type's module and name, for the type of a pattern C .. (sp.lc.cty: a
# type's constructors are seldom of its name, SCC's AcyclicSCC and
# CyclicSCC, telomare's ExpandedModuleItem's ExpandedModuleBinding)
type Ct is Data:
  Ct{k: List<&2, U32>, m: List<&2, U32>, n: List<&2, U32>}

type Ix is Data:
  Ix{dfs: List<&2, Df>, lcs: List<&2, Lc>, pss: List<&2, Ps>, ins: List<&2, In>, cls: List<&2, Cl>, sys: List<&2, Sy>, fms: List<&2, Fm>, fns: List<&2, Df>, cts: List<&2, Ct>}

def sp.ix.sys(ix: Ix) -> List<&2, Sy>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      sys

def sp.ix.cts(ix: Ix) -> List<&2, Ct>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      cts

# a (data NAME (TV..) ((con C ..)..) ..) or (newtype ..) item's constructors
def sp.ct.of(+m: List<&2, U32>, +n: List<&2, U32>, cs: List<&2, X.Sx>) -> List<&2, Ct>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      Ct{sp.key(m, sp.sat(c, 1n)), m, n} <> sp.ct.of(m, n, t)

def sp.ct.find(cts: List<&2, Ct>, +k: List<&2, U32>) -> Maybe<&2, Ct>:
  match cts:
    case Nil{}:
      None{}
    case Ct{+ck, +cm, +cn} <> t:
      Bool.pick(Maybe<&2, Ct>, S.eq(ck, k), Some{Ct{ck, cm, cn}}, sp.ct.find(t, k))

def sp.ix.ct.add(+m: List<&2, U32>, +x: X.Sx, ix: Ix) -> Ix:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, List.append(&2, Ct, sp.ct.of(m, sp.sat(x, 1n), sp.els(sp.at(x, 3n))), cts)}

def sp.ix0() -> Ix:
  Ix{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

# a module's name, from its (module NAME ...) item
def sp.modname(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      Bool.pick(List<&2, U32>, sp.head.is(x, "module"), sp.sat(x, 1n), sp.modname(t))

# the leading (tapp)/(tyapp)/(evapp) of a spine, down to its head
def sp.spine.head(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, +r}}:
      Bool.pick(X.Sx, Bool.or(sp.is(a, "tyapp"), Bool.or(sp.is(a, "evapp"), sp.is(a, "app"))), sp.spine.head(e), X.SxCons{X.SxAtom{a}, X.SxCons{e, r}})
    case y:
      y

# the type arguments of a (tyapp)/(evapp) spine, innermost first
def sp.isty(+x: X.Sx) -> Bool:
  Bool.or(sp.head.is(x, "tyapp"), sp.head.is(x, "evapp"))

def sp.isapp(+x: X.Sx) -> Bool:
  Bool.or(sp.head.is(x, "app"), sp.isty(x))

def sp.spine.tys.go(x: X.Sx, go: Bool, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match x go:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, X.SxCons{+t, X.SxNil{}}}} True{}:
      sp.spine.tys.go(e, sp.isty(e), Bool.pick(List<&2, X.Sx>, sp.is(a, "tyapp"), t <> acc, acc))
    case _ _:
      acc

def sp.spine.tys(+x: X.Sx, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  sp.spine.tys.go(x, sp.isty(x), acc)

# the value arguments of an (app) spine (tyapp and evapp skipped)
def sp.spine.args.go(x: X.Sx, go: Bool, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match x go:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, X.SxCons{+t, X.SxNil{}}}} True{}:
      sp.spine.args.go(e, sp.isapp(e), Bool.pick(List<&2, X.Sx>, sp.is(a, "app"), t <> acc, acc))
    case _ _:
      acc

def sp.spine.args(+x: X.Sx, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  sp.spine.args.go(x, sp.isapp(x), acc)

# the first (fun ...) in a tree (a top's binding, in its abs)
def sp.fun.of(x: X.Sx) -> Maybe<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(Maybe<&2, X.Sx>, sp.is(X.tsx.atom.of(h), "fun"), Some{X.SxCons{h, t}}, Maybe.or(&2, X.Sx, sp.fun.of(h), sp.fun.of(t)))
    case _:
      None{}

# the first node headed by atom a in a tree
def sp.find(x: X.Sx, +a: List<&2, U32>) -> Maybe<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(Maybe<&2, X.Sx>, S.eq(X.tsx.atom.of(h), a), Some{X.SxCons{h, t}}, Maybe.or(&2, X.Sx, sp.find(h, a), sp.find(t, a)))
    case _:
      None{}

# a top's exports: (export VAR TYPE) of its abs
def sp.exports(+top: X.Sx) -> List<&2, X.Sx>:
  sp.els(sp.at(sp.at(top, 1n), 3n))

def sp.ix.lc.add(+m: List<&2, U32>, +e: X.Sx, +top: X.Sx, +ls: List<&2, Lc>) -> List<&2, Lc>:
  Bool.pick(List<&2, Lc>, sp.head.is(sp.at(e, 1n), "l"), Lc{m, sp.sat(sp.at(e, 1n), 1n), X.tsx.atom.of(sp.at(sp.at(e, 1n), 2n)), top} <> ls, ls)

# a synonym's right-hand side, by its key (sp.sy.find's, for the index)
def sp.pc.syfind(ss: List<&2, Sy>, +k: List<&2, U32>) -> Maybe<&2, X.Sx>:
  match ss:
    case Nil{}:
      None{}
    case Sy{+sk, tvs, +rhs} <> t:
      sp.if(Maybe<&2, X.Sx>, S.eq(sk, k), _ => Some{rhs}, _ => sp.pc.syfind(t, k))

# a type's head through at most n synonyms of the package
def sp.pc.unsyn(n: Nat, +t: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  match n:
    case 0n:
      t
    case 1n+k:
      +m = Bool.pick(Maybe<&2, X.Sx>, sp.head.is(t, "tc"), sp.pc.syfind(sys, sp.key(sp.sat(t, 1n), sp.sat(t, 2n))), None{})
      sp.if(X.Sx, Maybe.is_some(&2, X.Sx, m), _ => sp.pc.unsyn(k, Maybe.default(&2, X.Sx, m, t), sys), _ => t)

# whether a type is a parser: megaparsec's ParsecT, Parsec e s, or a
# synonym of the package for one (Telomare's TelomareParser); a parameter
# of one is a function's (it is a function of the parser's state)
def sp.pc.isp(+t: X.Sx, +sys: List<&2, Sy>) -> Bool:
  +h = sp.pc.unsyn(4n, t, sys)
  +k = Bool.pick(List<&2, U32>, sp.head.is(h, "tc"), sp.key(sp.sat(h, 1n), sp.sat(h, 2n)), Nil{})
  Bool.or(sp.is(k, "Text.Megaparsec.Internal.ParsecT"), sp.is(k, "Text.Megaparsec.Parsec"))

def sp.fnp.isfn(+p: X.Sx, +sys: List<&2, Sy>) -> Bool:
  Bool.or(sp.head.is(p, "tfun"), sp.pc.isp(p, sys))

# whether a type (under its foralls and contexts) takes a function
def sp.fnp.has(t: X.Sx, +sys: List<&2, Sy>) -> Bool:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{+r, X.SxNil{}}}}:
      +strip = Bool.or(sp.is(a, "tforall"), sp.is(a, "tctx"))
      +fun = sp.is(a, "tfun")
      +rest = sp.fnp.has(r, sys)
      Bool.pick(Bool, strip, rest, Bool.and(fun, Bool.or(sp.fnp.isfn(p, sys), rest)))
    case _:
      False{}

# a global def that takes a function: its key and its top (known function
# arguments)
def sp.ix.fn.add(+e: X.Sx, +top: X.Sx, +fs: List<&2, Df>, +sys: List<&2, Sy>) -> List<&2, Df>:
  Bool.pick(List<&2, Df>, Bool.and(sp.head.is(sp.at(e, 1n), "g"), sp.fnp.has(sp.at(e, 2n), sys)), Df{sp.key(sp.sat(sp.at(e, 1n), 1n), sp.sat(sp.at(e, 1n), 2n)), top} <> fs, fs)

# A def copied at its types: one that takes dictionaries (a class context),
# or one over type variables, with no context, that applies a dictionary
# inside (an evapp): a method or def it calls at its own type variables
# (patternBinders's fold at PatternF t, the derived Foldable's at any t) is
# then at known types in the copy, and copied in turn. Not one that takes
# a function or a parser (sp.fnp.has), the megaparsec model's (Cata.Parsec)
# or a package's own (telomare's commaSep1): it is copied at its known
# function arguments (rule 15), and a copy at the types alone takes the
# function as a template its lifted continuation hands back to it
# (many__Char.go from many__Char.l1, many__LocatedName's from
# commaSep1__LocatedName's: a template called before it is declared)
def sp.ix.df.dep(+e: X.Sx, +top: X.Sx, +sys: List<&2, Sy>) -> Bool:
  +ty = sp.at(e, 2n)
  +model = sp.is(sp.sat(sp.at(e, 1n), 1n), "Cata.Parsec")
  +fn = Bool.or(model, sp.fnp.has(ty, sys))
  Bool.or(sp.has(ty, S.b("tctx")), Bool.and(Bool.and(Bool.and(sp.has(ty, S.b("tforall")), Bool.not(fn)), Bool.not(S.prefix(sp.sat(sp.at(e, 1n), 2n), S.b("$")))), sp.has(top, S.b("evapp"))))

def sp.ix.df.add(+e: X.Sx, +top: X.Sx, +ds: List<&2, Df>, +sys: List<&2, Sy>) -> List<&2, Df>:
  Bool.pick(List<&2, Df>, Bool.and(sp.head.is(sp.at(e, 1n), "g"), sp.ix.df.dep(e, top, sys)), Df{sp.key(sp.sat(sp.at(e, 1n), 1n), sp.sat(sp.at(e, 1n), 2n)), top} <> ds, ds)

def sp.ix.exps(+m: List<&2, U32>, es: List<&2, X.Sx>, +top: X.Sx, ix: Ix) -> Ix:
  match es ix:
    case Nil{} i:
      i
    case +e <> r Ix{dfs, lcs, pss, ins, cls, +sys, fms, fns, cts}:
      sp.ix.exps(m, r, top, Ix{sp.ix.df.add(e, top, dfs, sys), sp.ix.lc.add(m, e, top, lcs), pss, ins, cls, sys, fms, sp.ix.fn.add(e, top, fns, sys), cts})

# a matcher $mX: X, its module, its universal type variables (its type's
# foralls after rep and r), the locals its continuation is applied to (the
# pattern's argument variables, in order) and the pattern of the first
# match of the case in its body
def sp.drop2(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case a <> b <> t:
      t
    case _:
      Nil{}

# an argument without its casts
def sp.uncast(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, +r}}:
      Bool.pick(X.Sx, sp.is(a, "cast"), sp.uncast(e), X.SxCons{X.SxAtom{a}, X.SxCons{e, r}})
    case y:
      y

def sp.locals(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x0 <> +t:
      +x = sp.uncast(x0)
      +r = sp.locals(t)
      Bool.pick(List<&2, X.Sx>, sp.head.is(x, "l"), x <> r, r)

def sp.ps.case(+m: List<&2, U32>, +n: List<&2, U32>, +ty: X.Sx, c: Maybe<&2, X.Sx>) -> List<&2, Ps>:
  match c:
    case Some{+cs}:
      +mt = sp.at(sp.at(sp.at(cs, 2n), 4n), 0n)
      [Ps{m, n, sp.drop2(sp.foralls(ty)), sp.locals(sp.spine.args(sp.at(sp.at(sp.at(sp.at(mt, 2n), 1n), 0n), 2n), Nil{})), sp.at(sp.at(mt, 1n), 0n)}]
    case None{}:
      Nil{}

def sp.ps.of(+f: X.Sx) -> List<&2, Ps>:
  +v = sp.at(f, 1n)
  sp.ps.case(sp.sat(v, 1n), List.drop(&2, U32, sp.sat(v, 2n), 2n), sp.at(f, 2n), sp.find(sp.at(f, 4n), S.b("case")))

# whether a fun's var is a matcher, $m...
def sp.is.matcher(+f: X.Sx) -> Bool:
  Bool.and(sp.head.is(sp.at(f, 1n), "g"), S.prefix(sp.sat(sp.at(f, 1n), 2n), S.b("$m")))

# a dictionary's def: its key, type variables, constructor arguments
type Dn is Data:
  Dn{k: List<&2, U32>, tvs: List<&2, List<&2, U32>>, args: List<&2, X.Sx>}

def sp.strs(x: X.Sx) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{h, t}:
      X.tsx.str.of(h) <> sp.strs(t)
    case _:
      Nil{}

def sp.ms(x: X.Sx) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{+h, t}:
      sp.sat(h, 1n) <> sp.ms(t)
    case _:
      Nil{}

def sp.dn.of(+top: X.Sx, es: List<&2, X.Sx>) -> List<&2, Dn>:
  match es:
    case +e <> t:
      Bool.pick(List<&2, Dn>, Bool.and(sp.head.is(sp.at(e, 1n), "g"), sp.is(X.tsx.atom.of(sp.at(sp.at(e, 1n), 3n)), "dfun")), [Dn{sp.key(sp.sat(sp.at(e, 1n), 1n), sp.sat(sp.at(e, 1n), 2n)), sp.strs(sp.at(sp.at(top, 1n), 1n)), sp.spine.args(sp.at(Maybe.default(&2, X.Sx, sp.find(top, S.b("varbind")), X.SxNil{}), 3n), Nil{})}], sp.dn.of(top, t))
    case Nil{}:
      Nil{}

def sp.dn.find(ds: List<&2, Dn>, +k: List<&2, U32>) -> Maybe<&2, Dn>:
  match ds:
    case Nil{}:
      None{}
    case Dn{+dk, +tvs, +args} <> t:
      Bool.pick(Maybe<&2, Dn>, S.eq(dk, k), Some{Dn{dk, tvs, args}}, sp.dn.find(t, k))

def sp.ix.top.if(abs: Bool, mat: Bool, +m: List<&2, U32>, +x: X.Sx, +b: X.Sx, ix: Ix) -> Ix:
  match abs mat ix:
    case True{} _ i:
      sp.ix.exps(m, sp.exports(x), x, i)
    case False{} True{} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Ix{dfs, lcs, List.append(&2, Ps, sp.ps.of(b), pss), ins, cls, sys, fms, fns, cts}
    case False{} False{} i:
      i

# A module's items into the index: its defs, locals, matchers, dictionaries
# (first), then its instances, classes, synonyms and family instances
def sp.ix.top(+m: List<&2, U32>, +x: X.Sx, ix: Ix) -> Ix:
  +b = sp.at(x, 1n)
  sp.ix.top.if(sp.head.is(b, "abs"), Bool.and(sp.head.is(b, "fun"), sp.is.matcher(b)), m, x, b, ix)

def sp.dns(xs: List<&2, X.Sx>) -> List<&2, Dn>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      List.append(&2, Dn, Bool.pick(List<&2, Dn>, Bool.and(sp.head.is(x, "top"), sp.head.is(sp.at(x, 1n), "abs")), sp.dn.of(x, sp.exports(x)), Nil{}), sp.dns(t))

def sp.ix.in.mk(+x: X.Sx, +m: List<&2, U32>, d: Maybe<&2, Dn>) -> List<&2, In>:
  match d:
    case Some{Dn{k, tvs, args}}:
      [In{sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), sp.els(sp.at(x, 3n)), m, tvs, args}]
    case None{}:
      Nil{}

# Lookups ----------------------------------------------------------------------

def sp.df.find(ds: List<&2, Df>, +k: List<&2, U32>) -> Maybe<&2, X.Sx>:
  match ds:
    case Nil{}:
      None{}
    case Df{+dk, +top} <> t:
      Bool.pick(Maybe<&2, X.Sx>, S.eq(dk, k), Some{top}, sp.df.find(t, k))

def sp.lc.find(ls: List<&2, Lc>, +m: List<&2, U32>, +i: List<&2, U32>) -> Maybe<&2, X.Sx>:
  match ls:
    case Nil{}:
      None{}
    case Lc{+lm, n, +li, +top} <> t:
      Bool.pick(Maybe<&2, X.Sx>, Bool.and(S.eq(lm, m), S.eq(li, i)), Some{top}, sp.lc.find(t, m, i))

def sp.ps.find(ps: List<&2, Ps>, +n: List<&2, U32>) -> Maybe<&2, Ps>:
  match ps:
    case Nil{}:
      None{}
    case Ps{+pm, +pn, +tvs, +bs, +pat} <> t:
      Bool.pick(Maybe<&2, Ps>, S.eq(pn, n), Some{Ps{pm, pn, tvs, bs, pat}}, sp.ps.find(t, n))

def sp.cl.find(cs: List<&2, Cl>, +k: List<&2, U32>) -> Maybe<&2, Cl>:
  match cs:
    case Nil{}:
      None{}
    case Cl{+ck, +ntv, +nsup, +ms} <> t:
      Bool.pick(Maybe<&2, Cl>, S.eq(ck, k), Some{Cl{ck, ntv, nsup, ms}}, sp.cl.find(t, k))

def sp.sy.find(ss: List<&2, Sy>, +k: List<&2, U32>) -> Maybe<&2, Sy>:
  match ss:
    case Nil{}:
      None{}
    case Sy{+sk, +tvs, +rhs} <> t:
      Bool.pick(Maybe<&2, Sy>, S.eq(sk, k), Some{Sy{sk, tvs, rhs}}, sp.sy.find(t, k))

def sp.take(xs: List<&2, X.Sx>, n: Nat) -> List<&2, X.Sx>:
  match xs n:
    case x <> t Succ{k}:
      x <> sp.take(t, k)
    case _ _:
      Nil{}

def sp.dropn(xs: List<&2, X.Sx>, n: Nat) -> List<&2, X.Sx>:
  match xs n:
    case x <> t Succ{k}:
      sp.dropn(t, k)
    case ys _:
      ys

# a type applied to more arguments
def sp.tyapply(args: List<&2, X.Sx>, t: X.Sx) -> X.Sx:
  match args:
    case Nil{}:
      t
    case a <> r:
      sp.tyapply(r, sp.l([sp.a("tapp"), t, a]))

def sp.fm.at(m: Maybe<&2, List<&2, Sb>>, rhs: X.Sx, rest: List<&2, X.Sx>, next: Maybe<&2, X.Sx>) -> Maybe<&2, X.Sx>:
  match m:
    case Some{sbs}:
      Some{sp.tyapply(rest, sp.subst(rhs, sbs))}
    case None{}:
      next

def sp.fm.hit(ok: Bool, +lhs: List<&2, X.Sx>, rhs: X.Sx, +args: List<&2, X.Sx>, next: Maybe<&2, X.Sx>) -> Maybe<&2, X.Sx>:
  match ok:
    case True{}:
      +n = List.length(&2, X.Sx, lhs)
      sp.fm.at(sp.match.all(lhs, sp.take(args, n), Some{Nil{}}), rhs, sp.dropn(args, n), next)
    case False{}:
      next

def sp.fm.find(fs: List<&2, Fm>, +k: List<&2, U32>, +args: List<&2, X.Sx>) -> Maybe<&2, X.Sx>:
  match fs:
    case Nil{}:
      None{}
    case Fm{+fk, +lhs, +rhs} <> t:
      sp.fm.hit(Bool.and(S.eq(fk, k), Nat.is_le(List.length(&2, X.Sx, lhs), List.length(&2, X.Sx, args))), lhs, rhs, args, sp.fm.find(t, k, args))

# Normal types: synonyms expanded, type families applied, (tapp (tc ..) b)
# as (tc .. b)
def sp.tc(+m: List<&2, U32>, +n: List<&2, U32>, args: List<&2, X.Sx>) -> X.Sx:
  X.SxCons{sp.a("tc"), X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, sp.l(args)}}}

def sp.syn.at(m: Maybe<&2, Sy>, +args: List<&2, X.Sx>, +d: X.Sx) -> X.Sx:
  match m:
    case Some{Sy{k, +tvs, +rhs}}:
      +n = List.length(&2, List<&2, U32>, tvs)
      Bool.pick(X.Sx, Nat.is_le(n, List.length(&2, X.Sx, args)), sp.tyapply(sp.dropn(args, n), sp.subst(rhs, sp.zip(tvs, sp.take(args, n)))), d)
    case None{}:
      d

def sp.fam.at(m: Maybe<&2, X.Sx>, d: X.Sx) -> X.Sx:
  match m:
    case Some{t}:
      t
    case None{}:
      d

# Parsec e s a..: ParsecT e s Identity a..
def sp.pc.parsec(args: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match args:
    case e <> s <> r:
      e <> s <> sp.tc(S.b("GHC.Internal.Data.Functor.Identity"), S.b("Identity"), Nil{}) <> r
    case xs:
      xs

# megaparsec's Parsec e s (ParsecT e s Identity) and its Stream's Token and
# Tokens at String (Char and String)
def sp.builtin.pc(+k: List<&2, U32>, +args: List<&2, X.Sx>, d: X.Sx) -> X.Sx:
  +a0 = Maybe.default(&2, X.Sx, List.head(&2, X.Sx, args), X.SxNil{})
  +str = Bool.or(sp.eq(a0, sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Types"), S.b("Char"), Nil{})])), sp.eq(a0, sp.tc(S.b("GHC.Internal.Base"), S.b("String"), Nil{})))
  +ch = sp.tc(S.b("GHC.Types"), S.b("Char"), Nil{})
  +parsec = sp.is(k, "Text.Megaparsec.Parsec")
  +tok = Bool.and(str, sp.is(k, "Text.Megaparsec.Stream.Token"))
  +toks = Bool.and(str, sp.is(k, "Text.Megaparsec.Stream.Tokens"))
  sp.if(X.Sx, parsec, _ => sp.tc(S.b("Text.Megaparsec.Internal"), S.b("ParsecT"), sp.pc.parsec(args)), _ => Bool.pick(X.Sx, tok, ch, Bool.pick(X.Sx, toks, sp.tc(S.b("GHC.Types"), S.b("List"), [ch]), d)))

# recursion-schemes' Base at Fix and Cofree (Base (Fix f) a is f a: the
# arguments after the first are kept), base's String
def sp.builtin(+m: List<&2, U32>, +n: List<&2, U32>, +args: List<&2, X.Sx>, d: X.Sx) -> X.Sx:
  +k = sp.key(m, n)
  +a0 = Maybe.default(&2, X.Sx, List.head(&2, X.Sx, args), X.SxNil{})
  +fixf = Bool.and(sp.head.is(a0, "tc"), sp.is(sp.key(sp.sat(a0, 1n), sp.sat(a0, 2n)), "Data.Fix.Fix"))
  +cof = Bool.and(sp.head.is(a0, "tc"), sp.is(sp.key(sp.sat(a0, 1n), sp.sat(a0, 2n)), "Control.Comonad.Cofree.Cofree"))
  Bool.pick(X.Sx, Bool.and(sp.is(k, "Data.Functor.Foldable.Base"), fixf), sp.tyapply(sp.dropn(args, 1n), sp.at(a0, 3n)), Bool.pick(X.Sx, Bool.and(sp.is(k, "Data.Functor.Foldable.Base"), cof), sp.tyapply(sp.dropn(args, 1n), sp.tc(S.b("Control.Comonad.Trans.Cofree"), S.b("CofreeF"), [sp.at(a0, 3n), sp.at(a0, 4n)])), Bool.pick(X.Sx, Bool.or(sp.is(k, "GHC.Internal.Base.String"), sp.is(k, "GHC.Internal.IO.FilePath")), sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Types"), S.b("Char"), Nil{})]), sp.builtin.pc(k, args, d))))

# one node, its parts already normal
def sp.norm.tc(+m: List<&2, U32>, +n: List<&2, U32>, +args: List<&2, X.Sx>, +ix: Ix) -> X.Sx:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +d = sp.tc(m, n, args)
      sp.builtin(m, n, args, sp.fam.at(sp.fm.find(fms, sp.key(m, n), args), sp.syn.at(sp.sy.find(sys, sp.key(m, n)), args, d)))

def sp.norm.node(y: X.Sx, +ix: Ix) -> X.Sx:
  match y:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{+n}, +r}}}:
      Bool.pick(X.Sx, sp.is(a, "tc"), sp.norm.tc(m, n, sp.els(r), ix), X.SxCons{X.SxAtom{a}, X.SxCons{X.SxStr{m}, X.SxCons{X.SxStr{n}, r}}})
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+b, X.SxNil{}}}}:
      Bool.pick(X.Sx, Bool.and(sp.is(a, "tapp"), sp.head.is(f, "tc")), sp.l(List.append(&2, X.Sx, sp.els(f), [b])), X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{b, X.SxNil{}}}})
    case z:
      z

# one pass, bottom up
def sp.norm.step(x: X.Sx, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      sp.norm.node(X.SxCons{sp.norm.step(h, ix), sp.norm.step(t, ix)}, ix)
    case y:
      y

# passes until nothing changes (a synonym's right-hand side may hold
# another), at most n
def sp.norm.go(n: Nat, +x: X.Sx, done: Bool, +ix: Ix) -> X.Sx:
  match n done:
    case Succ{k} False{}:
      +y = sp.norm.step(x, ix)
      sp.norm.go(k, y, sp.eq(x, y), ix)
    case _ _:
      x

def sp.norm(x: X.Sx, +ix: Ix) -> X.Sx:
  sp.norm.go(8n, x, False{}, ix)

def sp.norms(xs: List<&2, X.Sx>, +ix: Ix) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.norm(x, ix) <> sp.norms(t, ix)

def sp.fm.add(+k: List<&2, U32>, +x: X.Sx, +fms: List<&2, Fm>, +sys: List<&2, Sy>) -> List<&2, Fm>:
  Bool.pick(List<&2, Fm>, S.prefix(k, S.b("GHC.Internal.Generics.")), fms, Fm{k, sp.norms(sp.els(sp.at(x, 3n)), Ix{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, sys, Nil{}, Nil{}, Nil{}}), sp.at(x, 4n)} <> fms)

# an instance's class, from its line's (cls (TV...) (METHOD...) NSUPER)
def sp.cl.add(+x: X.Sx, +cls: List<&2, Cl>) -> List<&2, Cl>:
  +c = sp.at(x, 6n)
  Bool.pick(List<&2, Cl>, sp.head.is(c, "cls"), Cl{sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), X.tsx.len(sp.at(c, 1n)), X.tsx.nat(sp.at(c, 3n)), sp.strs(sp.at(c, 2n))} <> cls, cls)

def sp.ix.item.go(top: Bool, ins: Bool, cl: Bool, sy: Bool, fm: Bool, +m: List<&2, U32>, +ds: List<&2, Dn>, +x: X.Sx, ix: Ix) -> Ix:
  match top ins cl sy fm ix:
    case True{} _ _ _ _ i:
      sp.ix.top(m, x, i)
    case False{} True{} _ _ _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns, cts}:
      Ix{dfs, lcs, pss, List.append(&2, In, sp.ix.in.mk(x, m, sp.dn.find(ds, sp.key(sp.sat(sp.at(x, 4n), 1n), sp.sat(sp.at(x, 4n), 2n)))), iss), sp.cl.add(x, cls), sys, fms, fns, cts}
    case False{} False{} True{} _ _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns, cts}:
      Ix{dfs, lcs, pss, iss, Cl{sp.key(m, sp.sat(x, 1n)), X.tsx.len(sp.at(x, 2n)), X.tsx.len(sp.at(x, 4n)), sp.ms(sp.at(x, 3n))} <> cls, sys, fms, fns, cts}
    case False{} False{} False{} True{} _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns, cts}:
      Ix{dfs, lcs, pss, iss, cls, Sy{sp.key(m, sp.sat(x, 1n)), sp.strs(sp.at(x, 2n)), sp.at(x, 3n)} <> sys, fms, fns, cts}
    case False{} False{} False{} False{} True{} Ix{dfs, lcs, pss, iss, cls, +sys, fms, fns, cts}:
      Ix{dfs, lcs, pss, iss, cls, sys, sp.fm.add(sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), x, fms, sys), fns, cts}
    case _ _ _ _ _ i:
      i

def sp.ix.item.dt(dt: Bool, +h: List<&2, U32>, +m: List<&2, U32>, +ds: List<&2, Dn>, +x: X.Sx, ix: Ix) -> Ix:
  match dt:
    case True{}:
      sp.ix.ct.add(m, x, ix)
    case False{}:
      sp.ix.item.go(sp.is(h, "top"), sp.is(h, "instance"), sp.is(h, "class"), sp.is(h, "synonym"), sp.is(h, "faminst"), m, ds, x, ix)

def sp.ix.item(+m: List<&2, U32>, +ds: List<&2, Dn>, +x: X.Sx, ix: Ix) -> Ix:
  +h = sp.hd(x)
  sp.ix.item.dt(Bool.or(sp.is(h, "data"), sp.is(h, "newtype")), h, m, ds, x, ix)

# a class's methods' names, from its ((method NAME TYPE)...)
def sp.ix.items(+m: List<&2, U32>, +ds: List<&2, Dn>, xs: List<&2, X.Sx>, ix: Ix) -> Ix:
  match xs:
    case Nil{}:
      ix
    case +x <> t:
      sp.ix.items(m, ds, t, sp.ix.item(m, ds, x, ix))

def sp.ix.module(+xs: List<&2, X.Sx>, ix: Ix) -> Ix:
  sp.ix.items(sp.modname(xs), sp.dns(xs), xs, ix)

# Names of copies ----------------------------------------------------------------

def sp.alnum(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90))), Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)))

def sp.clean(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> t:
      +r = sp.clean(t)
      Bool.pick(List<&2, U32>, sp.alnum(c), c <> r, r)

# a type as name parts: each (tc M N ..)'s N, each string not a module
def sp.mg(x: X.Sx, +skip: Bool) -> List<&2, U32>:
  match x:
    case X.SxStr{s}:
      Bool.pick(List<&2, U32>, skip, Nil{}, 95 <> sp.clean(s))
    case X.SxCons{+h, +t}:
      sp.cat(sp.mg(h, skip), sp.mg(t, Bool.or(sp.is(X.tsx.atom.of(h), "tc"), Bool.and(skip, Bool.not(sp.isstr(h))))))
    case _:
      Nil{}

def sp.mgs(ts: List<&2, X.Sx>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      sp.cat(sp.mg(t, False{}), sp.mgs(r))

# NAME__TYPES: a copy's name
def sp.name(+n: List<&2, U32>, +ts: List<&2, X.Sx>) -> List<&2, U32>:
  sp.cat(sp.clean(n), 95 <> sp.mgs(ts))

# Instances ----------------------------------------------------------------------

# the package's instance of class c at types ts (normal, no variable left):
# the instance and its variables' values
type Ri is Data:
  Ri{i: In, sbs: List<&2, Sb>}

def sp.ri.at(m: Maybe<&2, List<&2, Sb>>, i: In, next: Maybe<&2, Ri>) -> Maybe<&2, Ri>:
  match m:
    case Some{sbs}:
      Some{Ri{i, sbs}}
    case None{}:
      next

def sp.in.hit(xs: List<&2, In>, +c: List<&2, U32>) -> Bool:
  match xs:
    case In{ic, head, m, tvs, args} <> t:
      S.eq(ic, c)
    case Nil{}:
      False{}

def sp.resolve(xs: List<&2, In>, hit: Bool, +c: List<&2, U32>, +ts: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Ri>:
  match xs hit:
    case In{+ic, +head, +m, +tvs, +args} <> +t True{}:
      sp.ri.at(sp.match.all(sp.norms(head, ix), ts, Some{Nil{}}), In{ic, head, m, tvs, args}, sp.resolve(t, sp.in.hit(t, c), c, ts, ix))
    case i <> +t False{}:
      sp.resolve(t, sp.in.hit(t, c), c, ts, ix)
    case Nil{} _:
      None{}

# a method's place among its dictionary's arguments
def sp.index(xs: List<&2, List<&2, U32>>, +x: List<&2, U32>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Bool.pick(Maybe<&2, Nat>, S.eq(h, x), Some{i}, sp.index(t, x, Succ{i}))

def sp.nth(xs: List<&2, X.Sx>, n: Nat) -> Maybe<&2, X.Sx>:
  match xs n:
    case x <> t Zero{}:
      Some{x}
    case x <> t Succ{k}:
      sp.nth(t, k)
    case Nil{} _:
      None{}

# a method m of class c at types ts: its implementation in the instance
# (a term in the instance's variables, a local $c.. applied to them, or a
# default method), the instance's module and its variables' values; None
# when the package has no instance there
type Mi is Data:
  Mi{impl: X.Sx, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, first: X.Sx, snd: X.Sx}

def sp.mi.term(t: Maybe<&2, X.Sx>, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, first: X.Sx, snd: X.Sx) -> Maybe<&2, Mi>:
  match t:
    case Some{x}:
      Some{Mi{x, m, sbs, ntv, first, snd}}
    case None{}:
      None{}

def sp.mi.at(p: Maybe<&2, Nat>, +args: List<&2, X.Sx>, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, +nsup: Nat) -> Maybe<&2, Mi>:
  match p:
    case Some{k}:
      sp.mi.term(sp.nth(args, k), m, sbs, ntv, Maybe.default(&2, X.Sx, sp.nth(args, nsup), X.SxNil{}), Maybe.default(&2, X.Sx, sp.nth(args, 1n+nsup), X.SxNil{}))
    case None{}:
      None{}

def sp.mi.of(r: Maybe<&2, Ri>, c: Maybe<&2, Cl>, +meth: List<&2, U32>) -> Maybe<&2, Mi>:
  match r c:
    case Some{Ri{In{ic, head, m, tvs, args}, sbs}} Some{Cl{k, ntv, +nsup, ms}}:
      sp.mi.at(sp.index(ms, meth, nsup), args, m, sbs, ntv, nsup)
    case _ _:
      None{}

def sp.cl.ntv(c: Cl) -> Nat:
  match c:
    case Cl{k, ntv, nsup, ms}:
      ntv

# (method CM C) of a (g M m (method CM C)) head: C's key, else empty
def sp.method.cls(+h: X.Sx) -> List<&2, U32>:
  +k = sp.at(h, 3n)
  Bool.pick(List<&2, U32>, Bool.and(sp.head.is(h, "g"), sp.head.is(k, "method")), sp.key(sp.sat(k, 1n), sp.sat(k, 2n)), Nil{})

def sp.method(+h: X.Sx, +ts: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Mi>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +c = sp.method.cls(h)
      +cl = sp.cl.find(cls, c)
      +ntv = Maybe.default(&2, Nat, Maybe.map(&2, Cl, Nat, x => sp.cl.ntv(x), cl), 0n)
      sp.mi.of(sp.resolve(ins, sp.in.hit(ins, c), c, sp.take(ts, ntv), Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}), cl, sp.sat(h, 2n))

# a method's type arguments that are its class's (they pick the instance;
# the rest are the method's own), all of them when the class is unknown
def sp.cls.args.of(c: Maybe<&2, Cl>, +tys: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match c:
    case Some{k}:
      sp.take(tys, sp.cl.ntv(k))
    case None{}:
      tys

def sp.cls.args(+h: X.Sx, +tys: List<&2, X.Sx>, +ix: Ix) -> List<&2, X.Sx>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      sp.cls.args.of(sp.cl.find(cls, sp.method.cls(h)), tys)

# Pattern synonyms ---------------------------------------------------------------

# (pvar (bv V T)) whose V is the i-th of bs replaced by the i-th of ps
def sp.pb.find(bs: List<&2, X.Sx>, ps: List<&2, X.Sx>, +v: X.Sx) -> Maybe<&2, X.Sx>:
  match bs ps:
    case +b <> bt p <> pt:
      Bool.pick(Maybe<&2, X.Sx>, sp.eq(b, v), Some{p}, sp.pb.find(bt, pt, v))
    case _ _:
      None{}

def sp.or(m: Maybe<&2, X.Sx>, d: X.Sx) -> X.Sx:
  match m:
    case Some{y}:
      y
    case None{}:
      d

def sp.pbind(x: X.Sx, +bs: List<&2, X.Sx>, +ps: List<&2, X.Sx>) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(X.Sx, sp.is(X.tsx.atom.of(h), "pvar"), sp.or(sp.pb.find(bs, ps, sp.at(sp.at(t, 0n), 1n)), X.SxCons{h, t}), X.SxCons{sp.pbind(h, bs, ps), sp.pbind(t, bs, ps)})
    case y:
      y

# whether x is (unsupported "PatSynCon" X)
def sp.unsup(+x: X.Sx) -> Bool:
  Bool.and(sp.head.is(x, "unsupported"), sp.is(sp.sat(x, 1n), "PatSynCon"))

# a use as a pattern: (pcon (unsupported "PatSynCon" X) (TYS) (args P...))
# what a use as a pattern became: what it stands for (its own uses still
# to do), or itself (a synonym the index has not, as base's CyclicSCC)
type P1r is Data:
  P1New{e: X.Sx}
  P1Old{x: X.Sx}

def sp.p1.pat.at(m: Maybe<&2, Ps>, +x: X.Sx) -> P1r:
  match m:
    case Some{Ps{pm, pn, tvs, bs, pat}}:
      +args = sp.at(x, 3n)
      Bool.pick(P1r, sp.head.is(args, "args"), P1New{sp.pbind(sp.subst(pat, sp.zip(tvs, sp.els(sp.at(x, 2n)))), bs, sp.els(X.tsx.args(args)))}, P1Old{x})
    case None{}:
      P1Old{x}

def sp.p1.pat(+x: X.Sx, +ix: Ix) -> P1r:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      sp.p1.pat.at(sp.ps.find(pss, sp.sat(sp.at(x, 1n), 2n)), x)

# a use as an expression: its builder $bX
def sp.p1.expr.at(m: Maybe<&2, Ps>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Ps{pm, pn, tvs, bs, pat}}:
      sp.g(pm, sp.cat(S.b("$b"), pn), "var")
    case None{}:
      x

def sp.p1.expr(+x: X.Sx, +ix: Ix) -> X.Sx:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      sp.p1.expr.at(sp.ps.find(pss, sp.sat(x, 2n)), x)

# each use replaced by what it stands for, and that walked in turn: fuel
# n counts the synonyms down one path (AppEE's pattern is StuckEE,
# SetEnvSF, ... eleven synonyms down, each EE two layers: GFix, then the
# FW view), so the caller gives 64; one walk of the def, where passes
# that each walked all of it were slow at Size's 58 uses
# what a node is to the pattern synonyms' pass: a use as a pattern
# expanded (to walk in turn), a node done (a use as an expression, at its
# builder, or a synonym the index has not), or a node to walk into
type P1k is Data:
  P1Into{e: X.Sx}
  P1Done{e: X.Sx}
  P1Gen{}

def sp.p1k.pat(r: P1r) -> P1k:
  match r:
    case P1New{e}:
      P1Into{e}
    case P1Old{x}:
      P1Done{x}

def sp.p1k(+x: X.Sx, +ix: Ix) -> P1k:
  sp.if(P1k, Bool.and(sp.head.is(x, "pcon"), sp.unsup(sp.at(x, 1n))), _ => sp.p1k.pat(sp.p1.pat(x, ix)), _ => sp.if(P1k, sp.unsup(x), _ => P1Done{sp.p1.expr(x, ix)}, _ => P1Gen{}))

def sp.p1(n: Nat, x: X.Sx, k: P1k, +ix: Ix) -> X.Sx:
  match n x k:
    case 0n y _:
      y
    case 1n+(+p) y P1Into{+e}:
      sp.p1(p, e, sp.p1k(e, ix), ix)
    case 1n+p y P1Done{e}:
      e
    case 1n+(+p) X.SxCons{+h, +t} P1Gen{}:
      X.SxCons{sp.p1(1n+p, h, sp.p1k(h, ix), ix), sp.p1(1n+p, t, sp.p1k(t, ix), ix)}
    case 1n+p y P1Gen{}:
      y

# whether the string s occurs anywhere in x
def sp.has.str(x: X.Sx, +s: List<&2, U32>) -> Bool:
  match x:
    case X.SxStr{a}:
      S.eq(a, s)
    case X.SxCons{h, t}:
      Bool.or(sp.has.str(h, s), sp.has.str(t, s))
    case _:
      False{}

# Views ------------------------------------------------------------------------------

# what a view's function is: the identity, a constructor (x to C x), the
# field of a one-constructor pattern p at its variable hole, a constructor
# turned into another of the same fields (Cofree's project, embed), f . g
type Vw is Data:
  VwId{}
  VwCon{c: X.Sx}
  VwProj{p: X.Sx, hole: X.Sx}
  VwIso{cin: X.Sx, tin: X.Sx, cout: X.Sx}
  VwComp{f: Vw, g: Vw}
  VwSel{p: X.Sx, hole: X.Sx}
  VwNo{}

# a spine's head, through tyapp and evapp only
def sp.vhead(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, +r}}:
      Bool.pick(X.Sx, Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp")), sp.vhead(e), X.SxCons{X.SxAtom{a}, X.SxCons{e, r}})
    case y:
      y

# a (g M N K)'s key M.N, else empty
def sp.gkey(+x: X.Sx) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, sp.head.is(x, "g"), sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), Nil{})

def sp.tckey(+x: X.Sx) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, sp.head.is(x, "tc"), sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), Nil{})

def sp.first(xs: List<&2, X.Sx>) -> X.Sx:
  match xs:
    case x <> t:
      x
    case Nil{}:
      X.SxNil{}

# a lambda \(C .. x ..) -> x: its pattern and x, else none
def sp.lam.proj(+e: X.Sx) -> Maybe<&2, X.Sx>:
  +ms = sp.els(sp.at(sp.at(e, 2n), 4n))
  +m0 = sp.first(ms)
  +ps = sp.els(sp.at(m0, 1n))
  +body = sp.at(sp.at(sp.at(sp.at(m0, 2n), 1n), 0n), 2n)
  +ok = Bool.and(Bool.and(sp.head.is(e, "lam"), Nat.is_eq(List.length(&2, X.Sx, ms), 1n)), Bool.and(Nat.is_eq(List.length(&2, X.Sx, ps), 1n), Bool.and(sp.head.is(body, "l"), sp.head.is(sp.first(ps), "pcon"))))
  Bool.pick(Maybe<&2, X.Sx>, ok, Some{sp.first(ps)}, None{})

# a function by clauses \case C .. x .. -> Just x; _ -> Nothing: the
# clause's pattern and x, when exactly one clause is Just of a variable and
# every other is Nothing
type Sel is Data:
  Sel{hit: Maybe<&2, X.Sx>, n: Nat, ok: Bool}

def sp.con.is(+x: X.Sx, s: String) -> Bool:
  +h = sp.vhead(x)
  Bool.and(sp.head.is(h, "g"), sp.is(sp.key(sp.sat(h, 1n), sp.sat(h, 2n)), s))

# Just, or pure (return) at Maybe
def sp.is.just(+f: X.Sx) -> Bool:
  +k = sp.gkey(sp.vhead(f))
  +pure = Bool.or(sp.is(k, "GHC.Internal.Base.pure"), sp.is(k, "GHC.Internal.Base.return"))
  Bool.or(sp.con.is(f, "GHC.Internal.Maybe.Just"), Bool.and(pure, sp.is(sp.tckey(sp.first(sp.spine.tys(f, Nil{}))), "GHC.Internal.Maybe.Maybe")))

def sp.sel.go(ms: List<&2, X.Sx>, acc: Sel) -> Sel:
  match ms acc:
    case +m <> t Sel{+hit, +n, +ok}:
      +ps = sp.els(sp.at(m, 1n))
      +body = sp.uncast(sp.at(sp.at(sp.at(sp.at(m, 2n), 1n), 0n), 2n))
      +x = sp.uncast(sp.at(body, 2n))
      +just = Bool.and(sp.head.is(body, "app"), Bool.and(sp.is.just(sp.at(body, 1n)), sp.head.is(x, "l")))
      +noth = Bool.and(Bool.not(sp.head.is(body, "app")), sp.con.is(body, "GHC.Internal.Maybe.Nothing"))
      +one = Nat.is_eq(List.length(&2, X.Sx, ps), 1n)
      sp.sel.go(t, Sel{Bool.pick(Maybe<&2, X.Sx>, just, Some{sp.l([sp.first(ps), x])}, hit), Bool.pick(Nat, just, Succ{n}, n), Bool.and(ok, Bool.and(one, Bool.or(just, noth)))})
    case Nil{} a:
      a

def sp.sel.of(s: Sel) -> Maybe<&2, X.Sx>:
  match s:
    case Sel{hit, +n, +ok}:
      Bool.pick(Maybe<&2, X.Sx>, Bool.and(ok, Nat.is_eq(n, 1n)), hit, None{})

def sp.lam.sel(+e: X.Sx) -> Maybe<&2, X.Sx>:
  sp.sel.of(sp.sel.go(sp.els(sp.at(sp.at(e, 2n), 4n)), Sel{None{}, 0n, Bool.and(sp.head.is(e, "lam"), Bool.not(sp.is(X.tsx.atom.of(sp.at(e, 1n)), "cases")))}))

# an instance method's body when it takes no argument (embedB = id,
# extractB = extractB . f), its variables at their values
def sp.impl.body.of(f: Maybe<&2, X.Sx>, +sbs: List<&2, Sb>, +rest: List<&2, X.Sx>) -> Maybe<&2, X.Sx>:
  match f:
    case Some{+fun}:
      +m0 = sp.first(sp.els(sp.at(sp.at(fun, 4n), 4n)))
      +noargs = sp.eq(sp.at(m0, 1n), X.SxNil{})
      +body = sp.at(sp.at(sp.at(sp.at(m0, 2n), 1n), 0n), 2n)
      Bool.pick(Maybe<&2, X.Sx>, noargs, Some{sp.subst(body, List.append(&2, Sb, sp.zip(sp.foralls(sp.at(fun, 2n)), rest), sbs))}, None{})
    case None{}:
      None{}

def sp.impl.body(mi: Maybe<&2, Mi>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match mi ix:
    case Some{Mi{impl, m, sbs, ntv, first, snd}} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +h = sp.vhead(impl)
      Bool.pick(Maybe<&2, X.Sx>, sp.head.is(h, "l"), sp.impl.body.of(Maybe.bind(&2, X.Sx, X.Sx, sp.lc.find(lcs, m, X.tsx.atom.of(sp.at(h, 2n))), t => sp.fun.of(t)), sbs, sp.dropn(tys, ntv)), None{})
    case _ _:
      None{}

# Recursive's project and Corecursive's embed at Fix f and Cofree f a
def sp.rs.view(+k: List<&2, U32>, +t: X.Sx) -> Vw:
  +tk = sp.tckey(t)
  +fix = sp.is(tk, "Data.Fix.Fix")
  +cof = sp.is(tk, "Control.Comonad.Cofree.Cofree")
  +fixc = sp.g(S.b("Data.Fix"), S.b("Fix"), "con")
  +cofc = sp.g(S.b("Control.Comonad.Cofree"), S.b(":<"), "con")
  +cffc = sp.g(S.b("Control.Comonad.Trans.Cofree"), S.b(":<"), "con")
  +hole = sp.l([sp.a("l"), X.SxStr{S.b("spec_x")}, sp.a("0")])
  +proj = sp.is(k, "Data.Functor.Foldable.project")
  +emb = sp.is(k, "Data.Functor.Foldable.embed")
  +ftys = sp.l([sp.at(t, 3n)])
  +ctys = sp.l([sp.at(t, 3n), sp.at(t, 4n)])
  +fixp = sp.l([sp.a("pcon"), fixc, ftys, sp.l([sp.a("args"), sp.l([sp.a("pvar"), sp.l([sp.a("bv"), hole, t])])])])
  Bool.pick(Vw, Bool.and(proj, fix), VwProj{fixp, hole}, Bool.pick(Vw, Bool.and(proj, cof), VwIso{cofc, ctys, cffc}, Bool.pick(Vw, Bool.and(emb, fix), VwCon{fixc}, Bool.pick(Vw, Bool.and(emb, cof), VwIso{cffc, sp.l([sp.at(t, 3n), sp.at(t, 4n), t]), cofc}, VwNo{}))))

# what a view's function is, to sp.view
type Vk is Data:
  VkId{}
  VkPure{}
  VkCon{}
  VkExp{}
  VkDot{}
  VkLam{}
  VkSel{}
  VkCast{}
  VkRs{}
  VkMeth{}
  VkNo{}

def sp.vk(+e: X.Sx, +ix: Ix) -> Vk:
  +h = sp.vhead(e)
  +k = sp.gkey(h)
  +tys = sp.norms(sp.spine.tys(e, Nil{}), ix)
  +app = sp.head.is(e, "app")
  +f = sp.at(e, 1n)
  +dot = Bool.and(app, Bool.and(sp.head.is(f, "app"), sp.is(sp.gkey(sp.vhead(sp.at(f, 1n))), "GHC.Internal.Base..")))
  +pure = Bool.and(Bool.or(sp.is(k, "GHC.Internal.Base.pure"), sp.is(k, "GHC.Internal.Base.return")), sp.is(sp.tckey(sp.first(tys)), "GHC.Internal.Maybe.Maybe"))
  +con = Bool.and(Bool.not(app), Bool.and(sp.head.is(h, "g"), sp.is(X.tsx.atom.of(sp.at(h, 3n)), "con")))
  +meth = Bool.and(Bool.not(app), Bool.and(Bool.not(S.eq(sp.method.cls(h), Nil{})), sp.all.closed(sp.cls.args(h, tys, ix))))
  +rs = Bool.or(sp.is(k, "Data.Functor.Foldable.project"), sp.is(k, "Data.Functor.Foldable.embed"))
  Bool.pick(Vk, sp.is(k, "GHC.Internal.Base.id"), VkId{}, Bool.pick(Vk, pure, VkPure{}, Bool.pick(Vk, con, VkCon{}, Bool.pick(Vk, sp.head.is(e, "expanded"), VkExp{}, Bool.pick(Vk, dot, VkDot{}, Bool.pick(Vk, sp.head.is(e, "cast"), VkCast{}, Bool.pick(Vk, Maybe.is_some(&2, X.Sx, sp.lam.proj(e)), VkLam{}, Bool.pick(Vk, Maybe.is_some(&2, X.Sx, sp.lam.sel(e)), VkSel{}, Bool.pick(Vk, Bool.and(meth, rs), VkRs{}, Bool.pick(Vk, meth, VkMeth{}, VkNo{}))))))))))

def sp.view(n: Nat, +e: X.Sx, k: Vk, +ix: Ix) -> Vw:
  match n k:
    case Zero{} _:
      VwNo{}
    case Succ{p} VkId{}:
      VwId{}
    case Succ{p} VkPure{}:
      VwCon{sp.g(S.b("GHC.Internal.Maybe"), S.b("Just"), "con")}
    case Succ{p} VkCon{}:
      VwCon{sp.vhead(e)}
    case Succ{p} VkExp{}:
      +i = sp.at(e, 2n)
      sp.view(p, i, sp.vk(i, ix), ix)
    case Succ{+p} VkDot{}:
      +f = sp.at(sp.at(e, 1n), 2n)
      +g = sp.at(e, 2n)
      VwComp{sp.view(p, f, sp.vk(f, ix), ix), sp.view(p, g, sp.vk(g, ix), ix)}
    case Succ{p} VkLam{}:
      VwProj{Maybe.default(&2, X.Sx, sp.lam.proj(e), X.SxNil{}), sp.at(sp.at(sp.at(sp.at(sp.first(sp.els(sp.at(sp.at(e, 2n), 4n))), 2n), 1n), 0n), 2n)}
    case Succ{p} VkSel{}:
      +r = Maybe.default(&2, X.Sx, sp.lam.sel(e), X.SxNil{})
      VwSel{sp.at(r, 0n), sp.at(r, 1n)}
    case Succ{p} VkCast{}:
      +i = sp.at(e, 1n)
      sp.view(p, i, sp.vk(i, ix), ix)
    case Succ{p} VkRs{}:
      sp.rs.view(sp.gkey(sp.vhead(e)), sp.first(sp.norms(sp.spine.tys(e, Nil{}), ix)))
    case Succ{p} VkMeth{}:
      +tys = sp.norms(sp.spine.tys(e, Nil{}), ix)
      +b = sp.or(sp.impl.body(sp.method(sp.vhead(e), tys, ix), tys, ix), X.SxNil{})
      sp.view(p, b, sp.vk(b, ix), ix)
    case Succ{p} VkNo{}:
      VwNo{}

# a projection's pattern with p at its hole, its other variables wild
def sp.vproj(x: X.Sx, +hole: X.Sx, +p: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      +bv = sp.at(t, 0n)
      Bool.pick(X.Sx, sp.is(X.tsx.atom.of(h), "pvar"), Bool.pick(X.Sx, sp.eq(sp.at(bv, 1n), hole), p, sp.l([sp.a("pwild"), sp.at(bv, 2n)])), X.SxCons{sp.vproj(h, hole, p), sp.vproj(t, hole, p)})
    case y:
      y

# (f -> p) as a plain pattern, when f is known
def sp.simp(v: Vw, +p: X.Sx) -> Maybe<&2, X.Sx>:
  match v:
    case VwId{}:
      Some{p}
    case VwCon{+c}:
      Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(p, "pcon"), sp.eq(sp.at(p, 1n), c)), Some{sp.at(sp.at(p, 3n), 1n)}, Bool.pick(Maybe<&2, X.Sx>, sp.head.is(p, "pwild"), Some{p}, None{}))
    case VwProj{q, hole}:
      Some{sp.vproj(q, hole, p)}
    case VwIso{cin, tin, +cout}:
      Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(p, "pcon"), sp.eq(sp.at(p, 1n), cout)), Some{sp.l([sp.a("pcon"), cin, tin, sp.at(p, 3n)])}, Bool.pick(Maybe<&2, X.Sx>, sp.head.is(p, "pwild"), Some{p}, None{}))
    case VwSel{q, hole}:
      Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(p, "pcon"), sp.con.is(sp.at(p, 1n), "GHC.Internal.Maybe.Just")), Some{sp.vproj(q, hole, sp.at(sp.at(p, 3n), 1n))}, None{})
    case VwComp{f, g}:
      Maybe.bind(&2, X.Sx, X.Sx, sp.simp(f, p), q => sp.simp(g, q))
    case VwNo{}:
      None{}

def sp.p3.view(+y: X.Sx, +ix: Ix) -> X.Sx:
  +e = sp.at(y, 1n)
  sp.or(sp.simp(sp.view(12n, e, sp.vk(e, ix), ix), sp.at(y, 2n)), y)

# bottom up: each (pview E P) whose E is known, as the pattern it is
def sp.ispv(+x: X.Sx) -> Bool:
  sp.head.is(x, "pview")

def sp.p3(x: X.Sx, pv: Bool, +ix: Ix) -> X.Sx:
  match x pv:
    case X.SxCons{+h, +t} True{}:
      sp.p3.view(sp.cons(sp.p3(h, sp.ispv(h), ix), sp.p3(t, sp.ispv(t), ix)), ix)
    case X.SxCons{+h, +t} False{}:
      X.SxCons{sp.p3(h, sp.ispv(h), ix), sp.p3(t, sp.ispv(t), ix)}
    case y _:
      y

# A binding f = \case .. (or \x -> ..), its only clause bare: f's clauses
# are the lambda's (the survey and the fold read a def's parameters off
# its clauses)
def sp.p0.cl(cs: List<&2, X.Sx>, +ops: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      sp.l([sp.a("match"), sp.l(List.append(&2, X.Sx, ops, sp.els(sp.at(c, 1n)))), sp.at(c, 2n)]) <> sp.p0.cl(t, ops)

# A generated binding (a derived instance's method) with no parameters
# whose one bare right-hand side is a function but not a lambda ($cfoldr =
# $dmfoldr at a phantom type, base's default, then Base's model's
# foldrDefault) takes its arguments: f eta_0 .. eta_n = g eta_0 .. eta_n,
# so that a template argument reaches g through f (a def's value is no
# template)
def sp.p0.ev(+i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("eta_"), S.b(Nat.show(i)))}, sp.a("0")])

def sp.p0.eps(ts: List<&2, X.Sx>, +i: Nat) -> List<&2, X.Sx>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.p0.ev(i), t])]) <> sp.p0.eps(r, 1n+i)

def sp.p0.ecall(n: Nat, +i: Nat, f: X.Sx) -> X.Sx:
  match n:
    case 0n:
      f
    case 1n+p:
      sp.p0.ecall(p, 1n+i, sp.l([sp.a("app"), f, sp.p0.ev(i)]))

# a function type's parameters' types
def sp.p0.params(t: X.Sx) -> List<&2, X.Sx>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{+r, X.SxNil{}}}}:
      Bool.pick(List<&2, X.Sx>, sp.is(a, "tfun"), p <> sp.p0.params(r), Nil{})
    case _:
      Nil{}

# a function type's result after its parameters
def sp.p0.res(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{+r, X.SxNil{}}}}:
      Bool.pick(X.Sx, sp.is(a, "tfun"), sp.p0.res(r), X.SxCons{X.SxAtom{a}, X.SxCons{p, X.SxCons{r, X.SxNil{}}}})
    case u:
      u

def sp.p0.eta(+ms: X.Sx, +body: X.Sx) -> X.Sx:
  +ps = sp.p0.params(sp.at(ms, 2n))
  +gr = sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, sp.p0.ecall(List.length(&2, X.Sx, ps), 0n, body)])]), sp.l([sp.a("binds")])])
  sp.l([sp.a("matches"), sp.l(ps), sp.p0.res(sp.at(ms, 2n)), sp.at(ms, 3n), sp.l([sp.l([sp.a("match"), sp.l(sp.p0.eps(ps, 0n)), gr])])])

def sp.p0.ms(+ms: X.Sx) -> X.Sx:
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +gs = sp.at(sp.at(m0, 2n), 1n)
  +g0 = sp.first(sp.els(gs))
  +body = sp.at(g0, 2n)
  +lm = sp.at(body, 2n)
  +one = Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 4n)), 1n), Bool.and(Nat.is_eq(X.tsx.len(gs), 1n), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(sp.at(m0, 2n), 2n), sp.l([sp.a("binds")])))))
  +bare = Bool.and(one, Bool.and(sp.head.is(body, "lam"), Bool.not(sp.is(X.tsx.atom.of(sp.at(body, 1n)), "cases"))))
  +gen = Bool.and(Bool.and(one, sp.is(X.tsx.atom.of(sp.at(ms, 3n)), "generated")), Bool.and(Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 0n), sp.head.is(sp.at(ms, 2n), "tfun")), Bool.not(sp.head.is(body, "lam"))))
  sp.if(X.Sx, bare, _ => sp.l([sp.a("matches"), sp.l(List.append(&2, X.Sx, sp.els(sp.at(ms, 1n)), sp.els(sp.at(lm, 1n)))), sp.at(lm, 2n), sp.at(ms, 3n), sp.l(sp.p0.cl(sp.els(sp.at(lm, 4n)), sp.els(sp.at(m0, 1n))))]), _ => sp.if(X.Sx, gen, _ => sp.p0.eta(ms, body), _ => ms))

def sp.p0.fun(+f: X.Sx) -> X.Sx:
  sp.l([sp.at(f, 0n), sp.at(f, 1n), sp.at(f, 2n), sp.at(f, 3n), sp.p0.ms(sp.at(f, 4n)), sp.at(f, 5n)])

def sp.isfun(+x: X.Sx) -> Bool:
  sp.head.is(x, "fun")

def sp.p0(x: X.Sx, fun: Bool) -> X.Sx:
  match x fun:
    case X.SxCons{+h, +t} True{}:
      sp.p0.fun(X.SxCons{sp.p0(h, sp.isfun(h)), sp.p0(t, sp.isfun(t))})
    case X.SxCons{+h, +t} False{}:
      X.SxCons{sp.p0(h, sp.isfun(h)), sp.p0(t, sp.isfun(t))}
    case y _:
      y

# Megaparsec --------------------------------------------------------------------

# The combinators of megaparsec and parser-combinators that run a parser
# they are given more than once, or hand one to a function, are cata's
# model's (prelude/Cata/Parsec.hs, exported with the package): their
# definitions there, at Parsec Void String, so that each is the package's
# own code, a copy at its known parser arguments (rule 15) and one def with
# the parsers that call it back (the fold's .mu). A call of one is a call
# of the model's def at the types after the monad's (its first d type
# arguments are e, s and m, or m), its dictionaries dropped. What runs a
# parser once is the fold's (HsPrelude's HsPc).
type Pcr is Data:
  Pcr{k: List<&2, U32>, n: List<&2, U32>, d: Nat}

def sp.pc.tab() -> List<&2, Pcr>:
  +cmc = {"Control.Monad.Combinators." : String}
  +lx = {"Text.Megaparsec.Char.Lexer." : String}
  [Pcr{S.b(cmc ++ "many"), S.b("many"), 1n}, Pcr{S.b(cmc ++ "some"), S.b("some"), 1n}, Pcr{S.b(cmc ++ "sepBy"), S.b("sepBy"), 1n}, Pcr{S.b(cmc ++ "sepBy1"), S.b("sepBy1"), 1n}, Pcr{S.b(cmc ++ "manyTill"), S.b("manyTill"), 1n}, Pcr{S.b(cmc ++ "skipMany"), S.b("skipMany"), 1n}, Pcr{S.b(cmc ++ "skipSome"), S.b("skipSome"), 1n}, Pcr{S.b("Text.Megaparsec.Lexer.space"), S.b("space"), 3n}, Pcr{S.b(lx ++ "skipBlockCommentNested"), S.b("skipBlockCommentNested"), 3n}, Pcr{S.b(lx ++ "lineFold"), S.b("lineFold"), 3n}, Pcr{S.b(lx ++ "indentGuard"), S.b("indentGuard"), 3n}]

def sp.pc.find(xs: List<&2, Pcr>, +k: List<&2, U32>) -> Maybe<&2, Pcr>:
  match xs:
    case Nil{}:
      None{}
    case Pcr{+a, n, d} <> t:
      sp.if(Maybe<&2, Pcr>, S.eq(a, k), _ => Some{Pcr{a, n, d}}, _ => sp.pc.find(t, k))

# a name under its type and dictionary applications: its key, the types
# and the dictionaries, in order
type Pp is Data:
  Pp{k: List<&2, U32>, tys: List<&2, X.Sx>, ds: List<&2, X.Sx>}

def sp.pc.peel(x: X.Sx, +tys: List<&2, X.Sx>, +ds: List<&2, X.Sx>) -> Maybe<&2, Pp>:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+t, X.SxNil{}}}}:
      +ty = sp.is(a, "tyapp")
      +ev = sp.is(a, "evapp")
      sp.if(Maybe<&2, Pp>, Bool.or(ty, ev), _ => sp.pc.peel(f, Bool.pick(List<&2, X.Sx>, ty, t <> tys, tys), Bool.pick(List<&2, X.Sx>, ty, ds, t <> ds)), _ => None{})
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{+n}, X.SxCons{+k, X.SxNil{}}}}}:
      Bool.pick(Maybe<&2, Pp>, sp.is(a, "g"), Some{Pp{sp.key(m, n), tys, ds}}, None{})
    case _:
      None{}

def sp.pc.key(m: Maybe<&2, Pp>) -> List<&2, U32>:
  match m:
    case Some{Pp{k, tys, ds}}:
      k
    case None{}:
      Nil{}

def sp.pc.tys(m: Maybe<&2, Pp>) -> List<&2, X.Sx>:
  match m:
    case Some{Pp{k, tys, ds}}:
      tys
    case None{}:
      Nil{}

def sp.pc.ds(m: Maybe<&2, Pp>) -> List<&2, X.Sx>:
  match m:
    case Some{Pp{k, tys, ds}}:
      ds
    case None{}:
      Nil{}

def sp.pc.drop(n: Nat, xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match n xs:
    case 1n+k h <> t:
      sp.pc.drop(k, t)
    case _ ys:
      ys

def sp.pc.tyapps(tys: List<&2, X.Sx>, f: X.Sx) -> X.Sx:
  match tys:
    case Nil{}:
      f
    case t <> r:
      sp.pc.tyapps(r, sp.l([sp.a("tyapp"), f, t]))

def sp.pc.model(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      sp.pc.tyapps(sp.pc.drop(d, tys), sp.g(S.b("Cata.Parsec"), n, "var"))
    case None{}:
      x

# Base's list functions that run a function they are given more than once
# (foldr, foldl, foldl') are cata's model's too, at a list
# (prelude/Cata/Base.hs, exported with the package as Cata/Parsec.hs is):
# a call of one whose first type argument is the list is a call of the
# model's def at the types after it, its dictionary dropped. Rule 15 then
# copies it at its known function argument, the argument's free locals its
# first parameters: a lambda over a pattern's variable is code in a
# first-order def, not a closure Bend refuses as a template.
# foldMap at a list is the model's foldMapMonoid at the list too (its
# dictionaries dropped, the list kept: at a package's derived Foldable,
# whose foldr is base's default, it stays the instance's foldMap).
def sp.pc.btab() -> List<&2, Pcr>:
  +fo = {"GHC.Internal.Data.Foldable." : String}
  [Pcr{S.b(fo ++ "foldr"), S.b("foldr"), 1n}, Pcr{S.b(fo ++ "foldl"), S.b("foldl"), 1n}, Pcr{S.b(fo ++ "foldl'"), S.b("foldl'"), 1n}, Pcr{S.b(fo ++ "concatMap"), S.b("concatMap"), 1n}, Pcr{S.b(fo ++ "foldMap"), S.b("foldMapMonoid"), 0n}]

# base's functions that are the model's at any type (Control.Monad's
# Kleisli compositions <=< and >=>: kleisliR, kleisliL; GHC.Base's until;
# GHC.List's filter; Data.Foldable's default foldr, $dmfoldr, foldrDefault,
# and asum, foldr (<|>) empty), at their own types (d is how many to drop:
# none)
def sp.pc.ktab() -> List<&2, Pcr>:
  +cm = {"GHC.Internal.Control.Monad." : String}
  [Pcr{S.b(cm ++ "<=<"), S.b("kleisliR"), 0n}, Pcr{S.b(cm ++ ">=>"), S.b("kleisliL"), 0n}, Pcr{S.b("GHC.Internal.Base.until"), S.b("until"), 0n}, Pcr{S.b("GHC.Internal.List.filter"), S.b("filter"), 0n}, Pcr{S.b("GHC.Internal.Data.Foldable.$dmfoldr"), S.b("foldrDefault"), 0n}, Pcr{S.b("GHC.Internal.Data.Foldable.asum"), S.b("asum"), 0n}]

def sp.pc.atlist(+tys: List<&2, X.Sx>) -> Bool:
  sp.is(sp.tckey(sp.first(tys)), "GHC.Types.List")

def sp.pc.bmodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      sp.pc.tyapps(sp.pc.drop(d, tys), sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# an expression under its (expanded ..) and (cast ..) wrappers
def sp.pc.strip(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+o, X.SxCons{+e, X.SxNil{}}}}:
      sp.if(X.Sx, sp.is(a, "expanded"), _ => sp.pc.strip(e), _ => X.SxCons{X.SxAtom{a}, X.SxCons{o, X.SxCons{e, X.SxNil{}}}})
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, X.SxNil{}}}:
      sp.if(X.Sx, sp.is(a, "cast"), _ => sp.pc.strip(e), _ => X.SxCons{X.SxAtom{a}, X.SxCons{e, X.SxNil{}}})
    case y:
      y

# choice [p1, .., pn] (asum: foldr (<|>) empty) is p1 <|> (.. (pn <|>
# empty)), and choice (f <$> [x1, .., xn]) is choice [f x1, .., f xn]: at
# the monad m and the element a of choice's type arguments (f, m, a), with
# its Alternative dictionary (after Foldable's)
def sp.pc.altm(+op: String, +m: X.Sx, +d: X.Sx, +a: X.Sx) -> X.Sx:
  sp.l([sp.a("tyapp"), sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("g"), X.SxStr{S.b("GHC.Internal.Base")}, X.SxStr{S.b(op)}, sp.l([sp.a("method"), X.SxStr{S.b("GHC.Internal.Base")}, X.SxStr{S.b("Alternative")}])]), m]), d]), a])

def sp.pc.alts(es: List<&2, X.Sx>, +m: X.Sx, +d: X.Sx, +a: X.Sx) -> X.Sx:
  match es:
    case Nil{}:
      sp.pc.altm("empty", m, d, a)
    case e <> t:
      sp.l([sp.a("app"), sp.l([sp.a("app"), sp.pc.altm("<|>", m, d, a), e]), sp.pc.alts(t, m, d, a)])

def sp.pc.apply(+f: X.Sx, es: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      sp.l([sp.a("app"), f, e]) <> sp.pc.apply(f, t)

def sp.pc.isfmap(+k: List<&2, U32>) -> Bool:
  Bool.or(sp.is(k, "GHC.Internal.Data.Functor.<$>"), Bool.or(sp.is(k, "GHC.Internal.Base.fmap"), sp.is(k, "GHC.Internal.Base.map")))

# a literal list's elements (through f <$> ..), if the argument is one
def sp.pc.elems.list(+x: X.Sx) -> Maybe<&2, List<&2, X.Sx>>:
  Bool.pick(Maybe<&2, List<&2, X.Sx>>, sp.head.is(x, "list"), Some{sp.els(sp.at(x, 2n))}, None{})

def sp.pc.elems.fmap(fm: Bool, +f: X.Sx, +l: X.Sx) -> Maybe<&2, List<&2, X.Sx>>:
  match fm:
    case True{}:
      Maybe.map(&2, List<&2, X.Sx>, List<&2, X.Sx>, es => sp.pc.apply(f, es), sp.pc.elems.list(sp.pc.strip(l)))
    case False{}:
      None{}

def sp.pc.elems(+x: X.Sx) -> Maybe<&2, List<&2, X.Sx>>:
  +y = sp.pc.strip(x)
  +g = sp.pc.strip(sp.at(y, 1n))
  +isapp2 = Bool.and(sp.head.is(y, "app"), sp.head.is(g, "app"))
  sp.if(Maybe<&2, List<&2, X.Sx>>, isapp2, _ => sp.pc.elems.fmap(sp.pc.isfmap(sp.pc.key(sp.pc.peel(sp.at(g, 1n), Nil{}, Nil{}))), sp.at(g, 2n), sp.at(y, 2n)), _ => sp.pc.elems.list(y))

def sp.pc.choice.at(m: Maybe<&2, List<&2, X.Sx>>, +tys: List<&2, X.Sx>, +ds: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{es}:
      sp.pc.alts(es, sp.first(sp.pc.drop(1n, tys)), sp.first(sp.pc.drop(1n, ds)), sp.first(sp.pc.drop(2n, tys)))
    case None{}:
      x

# uncurry g p, g the model's (Cata.Parsec's: a parser it makes, a Type
# that Base's uncurry does not take), is g (fst p) (snd p), base's
# definition
def sp.pc.isunc(+f: X.Sx) -> Bool:
  +sf = sp.pc.strip(f)
  Bool.and(sp.head.is(sf, "app"), Bool.and(sp.is(sp.pc.key(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{})), "GHC.Internal.Data.Tuple.uncurry"), S.prefix(sp.pc.key(sp.pc.peel(sp.pc.strip(sp.at(sf, 2n)), Nil{}, Nil{})), S.b("Cata.Parsec."))))

def sp.pc.proj(+n: String, +tys: List<&2, X.Sx>, +a: X.Sx) -> X.Sx:
  sp.l([sp.a("app"), sp.pc.tyapps(sp.pc.drop(0n, [sp.first(tys), sp.first(sp.pc.drop(1n, tys))]), sp.g(S.b("GHC.Internal.Data.Tuple"), S.b(n), "var")), a])

def sp.pc.unc(+f: X.Sx, +a: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +tys = sp.pc.tys(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{}))
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.pc.strip(sp.at(sf, 2n)), sp.pc.proj("fst", tys, a)]), sp.pc.proj("snd", tys, a)])

# f a, both already rewritten: choice at a literal list
def sp.pc.app2(+f: X.Sx, +a: X.Sx) -> X.Sx:
  +pf = sp.pc.peel(f, Nil{}, Nil{})
  sp.if(X.Sx, sp.pc.isunc(f), _ => sp.pc.unc(f, a), _ => sp.if(X.Sx, sp.is(sp.pc.key(pf), "Control.Applicative.Combinators.choice"), _ => sp.pc.choice.at(sp.pc.elems(a), sp.pc.tys(pf), sp.pc.ds(pf), sp.l([sp.a("app"), f, a])), _ => sp.l([sp.a("app"), f, a])))

# f $ a is f a
def sp.pc.app(+f: X.Sx, +a: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +dollar = Bool.and(sp.head.is(sf, "app"), sp.is(sp.pc.key(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{})), "GHC.Internal.Base.$"))
  sp.if(X.Sx, dollar, _ => sp.pc.app2(sp.pc.strip(sp.at(sf, 2n)), a), _ => sp.pc.app2(f, a))

# iterate g x !! n is the model's iterateIndex g x n (prelude/Cata/Base.hs:
# g applied n times, the infinite list never built), at iterate's type
# argument; f is (!!) applied to the list, already rewritten (its (!!)
# HsPrelude.Z's, sp.p5.ident, or base's)
def sp.pc.isiter(+f: X.Sx) -> Bool:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +bk = sp.pc.key(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{}))
  +bang = Bool.or(sp.is(bk, "GHC.Internal.List.!!"), sp.is(bk, "HsPrelude.Z.!!"))
  +iter = sp.is(sp.pc.key(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{})), "GHC.Internal.List.iterate")
  Bool.and(Bool.and(sp.head.is(sf, "app"), bang), Bool.and(Bool.and(sp.head.is(l, "app"), sp.head.is(i, "app")), iter))

def sp.pc.iter(+f: X.Sx, +n: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +it = sp.pc.tyapps(sp.pc.tys(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{})), sp.g(S.b("Cata.Base"), S.b("iterateIndex"), "var"))
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), it, sp.at(i, 2n)]), sp.at(l, 2n)]), n])

# base's instances at pairs, (,) w, are the model's too: a method of
# Functor, Applicative or Traversable whose class type is (,) w is the
# model's def (pairFmap, pairPure, pairAp, pairLiftA2, pairTraverse) at w
# then the method's types, its dictionaries dropped (a copy of the model's
# def at those types is one at its own Monoid's instance)
def sp.pc.ptab() -> List<&2, Pcr>:
  +b = {"GHC.Internal.Base." : String}
  [Pcr{S.b(b ++ "fmap"), S.b("pairFmap"), 0n}, Pcr{S.b("GHC.Internal.Data.Functor.<$>"), S.b("pairFmap"), 0n}, Pcr{S.b(b ++ "pure"), S.b("pairPure"), 0n}, Pcr{S.b(b ++ "<*>"), S.b("pairAp"), 0n}, Pcr{S.b(b ++ "liftA2"), S.b("pairLiftA2"), 0n}, Pcr{S.b("GHC.Internal.Data.Traversable.traverse"), S.b("pairTraverse"), 0n}]

def sp.pc.atpair(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "GHC.Tuple.Tuple2"), Nat.is_eq(X.tsx.len(t), 4n))

def sp.pc.pmodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      sp.pc.tyapps(sp.at(sp.first(tys), 3n) <> sp.pc.drop(1n, tys), sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# free's instances at CofreeF f a (a Cofree's layer), Functor and
# Traversable, are Base's model's defs too: a method whose class type is
# CofreeF f a is the model's def at f and a, then the method's types
# (sequence and sequenceA the model's traverse id)
def sp.pc.ctab() -> List<&2, Pcr>:
  +tr = {"GHC.Internal.Data.Traversable." : String}
  [Pcr{S.b("GHC.Internal.Base.fmap"), S.b("cofreeFFmap"), 0n}, Pcr{S.b("GHC.Internal.Data.Functor.<$>"), S.b("cofreeFFmap"), 0n}, Pcr{S.b(tr ++ "traverse"), S.b("cofreeFTraverse"), 0n}, Pcr{S.b(tr ++ "mapM"), S.b("cofreeFTraverse"), 0n}, Pcr{S.b(tr ++ "sequence"), S.b("cofreeFSequence"), 0n}, Pcr{S.b(tr ++ "sequenceA"), S.b("cofreeFSequence"), 0n}, Pcr{S.b("GHC.Internal.Data.Foldable.foldr"), S.b("cofreeFFoldr"), 0n}]

def sp.pc.atcofreef(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "Control.Comonad.Trans.Cofree.CofreeF"), Nat.is_eq(X.tsx.len(t), 5n))

def sp.pc.cmodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      +t = sp.first(tys)
      sp.pc.tyapps(sp.at(t, 3n) <> sp.at(t, 4n) <> sp.pc.drop(1n, tys), sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# Data.Foldable's fold at any container is Base's model's foldMonoid (foldr
# (<>) mempty) at the container and the Monoid, its dictionaries dropped
def sp.pc.mtab() -> List<&2, Pcr>:
  [Pcr{S.b("GHC.Internal.Data.Foldable.fold"), S.b("foldMonoid"), 0n}]

def sp.pc.amodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      sp.pc.tyapps(tys, sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# data-fix's Show instance at Fix f is Base's model's defs: a method of Show
# whose class type is Fix f, and shows at it, is the model's def at f
# (its dictionaries dropped: a copy of the model's def at f is one at
# f's own Show1 and Functor), the type normal first (a synonym of the
# package for it, as IR.Base's BasicExpr, is one too)
def sp.pc.ftab() -> List<&2, Pcr>:
  +s = {"GHC.Internal.Show." : String}
  [Pcr{S.b(s ++ "show"), S.b("fixShow"), 0n}, Pcr{S.b(s ++ "showsPrec"), S.b("fixShowsPrec"), 0n}, Pcr{S.b(s ++ "showList"), S.b("fixShowList"), 0n}, Pcr{S.b(s ++ "shows"), S.b("fixShows"), 0n}, Pcr{S.b("GHC.Classes.=="), S.b("fixEq"), 0n}, Pcr{S.b("GHC.Classes./="), S.b("fixNe"), 0n}]

def sp.pc.atfix(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "Data.Fix.Fix"), Nat.is_eq(X.tsx.len(t), 4n))

def sp.pc.fmodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      +t = sp.first(tys)
      sp.pc.tyapps(sp.at(t, 3n) <> sp.pc.drop(1n, tys), sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# free's Show instance at Cofree f a, the same way
def sp.pc.ctabs() -> List<&2, Pcr>:
  +s = {"GHC.Internal.Show." : String}
  [Pcr{S.b(s ++ "show"), S.b("cofreeShow"), 0n}, Pcr{S.b(s ++ "showsPrec"), S.b("cofreeShowsPrec"), 0n}, Pcr{S.b(s ++ "showList"), S.b("cofreeShowList"), 0n}, Pcr{S.b(s ++ "shows"), S.b("cofreeShows"), 0n}]

def sp.pc.atcof(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "Control.Comonad.Cofree.Cofree"), Nat.is_eq(X.tsx.len(t), 5n))

def sp.pc.cofmodel(m: Maybe<&2, Pcr>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      +t = sp.first(tys)
      sp.pc.tyapps([sp.at(t, 3n), sp.at(t, 4n)], sp.g(S.b("Cata.Base"), n, "var"))
    case None{}:
      x

# pairAp (pairFmap g y) x, both the model's, is pairLiftA2 g y x: a pair
# then holds no function (a function is Type, a pair's parts Data)
def sp.pc.isla2(+f: X.Sx) -> Bool:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +ap = sp.is(sp.pc.key(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{})), "Cata.Base.pairAp")
  +fm = sp.is(sp.pc.key(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{})), "Cata.Base.pairFmap")
  Bool.and(Bool.and(sp.head.is(sf, "app"), ap), Bool.and(Bool.and(sp.head.is(l, "app"), sp.head.is(i, "app")), fm))

def sp.pc.la2(+f: X.Sx, +x: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +ta = sp.pc.tys(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{}))
  +tf = sp.pc.tys(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{}))
  +tys = {[sp.first(ta), Maybe.default(&2, X.Sx, sp.nth(tf, 1n), X.SxNil{}), Maybe.default(&2, X.Sx, sp.nth(ta, 1n), X.SxNil{}), Maybe.default(&2, X.Sx, sp.nth(ta, 2n), X.SxNil{})] : List<&2, X.Sx>}
  +la = sp.pc.tyapps(tys, sp.g(S.b("Cata.Base"), S.b("pairLiftA2"), "var"))
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), la, sp.at(i, 2n)]), sp.at(l, 2n)]), x])

# The model's defs of a method, or a function of base's, containers',
# recursion-schemes' or lens's, at a container or a monad the fold has none
# for, by its key and its types (normalised), all of them written: a list's
# traverse and the rest at a monad without a prelude's (sp.pc.lmon),
# Maybe's traverse, <> and mempty, toList and foldl' at a package's own
# Foldable, mapKeys, ana at Cofree and Fix, transform at Cofree.
type Pgm is Data:
  Pgm{n: String, ts: List<&2, X.Sx>}

def sp.pc.tcmod(+t: X.Sx) -> List<&2, U32>:
  sp.if(List<&2, U32>, sp.head.is(t, "tc"), _ => sp.sat(t, 1n), _ => Nil{})

# a type of the package's own: a tc of no library's module
def sp.pc.own(+t: X.Sx) -> Bool:
  +m = sp.pc.tcmod(t)
  Bool.and(sp.head.is(t, "tc"), Bool.not(Bool.or(S.prefix(m, S.b("GHC.")), Bool.or(S.prefix(m, S.b("Data.")), Bool.or(S.prefix(m, S.b("Control.")), S.prefix(m, S.b("Text.")))))))

# a monad the prelude's list functions are not at: not Maybe, Either, State
# (StateT over Identity), ExceptT over one, a parser, IO, or a variable
def sp.pc.lmon(+m: X.Sx) -> Bool:
  +k = sp.tckey(m)
  +inner = sp.tckey(sp.at(m, 4n))
  +st = Bool.or(sp.is(k, "Control.Monad.Trans.State.Strict.StateT"), sp.is(k, "Control.Monad.Trans.State.Lazy.StateT"))
  +has = Bool.or(sp.is(k, "GHC.Internal.Maybe.Maybe"), Bool.or(sp.is(k, "GHC.Internal.Data.Either.Either"), Bool.or(sp.is(k, "Control.Monad.Trans.Except.ExceptT"), Bool.or(sp.is(k, "Text.Megaparsec.Internal.ParsecT"), sp.is(k, "GHC.Types.IO")))))
  Bool.and(sp.head.is(m, "tc"), Bool.not(Bool.or(has, Bool.and(st, sp.is(inner, "GHC.Internal.Data.Functor.Identity.Identity")))))

type Pgk is Data:
  PgkL{k: String, n: String}
  PgkH{k: String, n: String}
  PgkM{k: String, n: String}
  PgkO{k: String, n: String}
  PgkS{k: String, n: String}
  PgkA{k: String, n: String}

# at a list and such a monad; at Maybe; at a package's Foldable; at any type
def sp.pc.gtab() -> List<&2, Pgk>:
  +tr = {"GHC.Internal.Data.Traversable." : String}
  +fo = {"GHC.Internal.Data.Foldable." : String}
  [PgkL{tr ++ "traverse", "listTraverse"}, PgkL{tr ++ "mapM", "listMapM"}, PgkL{tr ++ "for", "listFor"}, PgkL{tr ++ "forM", "listForM"}, PgkL{tr ++ "sequence", "listSequence"}, PgkL{tr ++ "sequenceA", "listSequenceA"}, PgkL{fo ++ "traverse_", "listTraverse_"}, PgkL{fo ++ "for_", "listFor_"}, PgkL{fo ++ "mapM_", "listMapM_"}, PgkL{fo ++ "forM_", "listForM_"}, PgkL{"GHC.Internal.Control.Monad.foldM", "listFoldM"}, PgkH{"Cata.Hm.traverse", "listTraverse"}, PgkH{"Cata.Hm.mapM", "listMapM"}, PgkH{"Cata.Hm.for", "listFor"}, PgkH{"Cata.Hm.forM", "listForM"}, PgkH{"Cata.Hm.traverse_", "listTraverse_"}, PgkH{"Cata.Hm.for_", "listFor_"}, PgkH{"Cata.Hm.mapM_", "listMapM_"}, PgkH{"Cata.Hm.forM_", "listForM_"}, PgkH{"Cata.Hm.foldM", "listFoldM"}, PgkM{tr ++ "traverse", "maybeTraverse"}, PgkM{tr ++ "mapM", "maybeTraverse"}, PgkM{tr ++ "sequenceA", "maybeSequenceA"}, PgkM{tr ++ "sequence", "maybeSequenceA"}, PgkM{fo ++ "foldMap", "maybeFoldMap"}, PgkM{fo ++ "null", "maybeNull"}, PgkM{fo ++ "any", "maybeAny"}, PgkM{fo ++ "all", "maybeAll"}, PgkM{fo ++ "elem", "maybeElem"}, PgkM{fo ++ "toList", "maybeToListF"}, PgkM{fo ++ "length", "maybeLength"}, PgkM{"HsPrelude.Z.length", "maybeLength"}, PgkM{fo ++ "foldr", "maybeFoldr"}, PgkM{fo ++ "concatMap", "maybeConcatMap"}, PgkM{fo ++ "traverse_", "maybeTraverse_"}, PgkM{fo ++ "mapM_", "maybeTraverse_"}, PgkM{fo ++ "for_", "maybeFor_"}, PgkM{fo ++ "forM_", "maybeFor_"}, PgkO{fo ++ "toList", "toListDefault"}, PgkO{fo ++ "sum", "sumDefault"}, PgkO{fo ++ "product", "productDefault"}, PgkO{fo ++ "length", "lengthDefault"}, PgkO{fo ++ "foldl'", "foldlDefault"}, PgkO{fo ++ "foldl", "foldlDefault"}, PgkS{"GHC.Internal.Show.shows", "showsDefault"}, PgkO{"GHC.Internal.Data.Functor.<$>", "fmapOp"}, PgkO{"GHC.Internal.Data.Functor.<&>", "fmapFlip"}, PgkO{"GHC.Internal.Base.=<<", "bindFlip"}, PgkO{"GHC.Internal.Data.Functor.void", "voidOp"}, PgkO{"GHC.Internal.Base.when", "whenOp"}, PgkO{"GHC.Internal.Control.Monad.unless", "unlessOp"}, PgkO{"GHC.Internal.Base.liftM2", "liftM2Op"}, PgkO{"GHC.Internal.Base.>>", "thenOp"}, PgkO{"GHC.Internal.Base.return", "returnOp"}, PgkO{tr ++ "mapM", "mapMOp"}, PgkO{tr ++ "sequence", "sequenceOp"}, PgkO{"GHC.Internal.Base.<$", "constMap"}, PgkO{fo ++ "any", "anyDefault"}, PgkO{fo ++ "all", "allDefault"}, PgkO{fo ++ "or", "orDefault"}, PgkO{fo ++ "and", "andDefault"}, PgkO{fo ++ "null", "nullDefault"}, PgkO{fo ++ "elem", "elemDefault"}, PgkO{fo ++ "concatMap", "concatMapDefault"}, PgkA{"Data.Map.Internal.mapKeys", "mapKeys"}, PgkA{"GHC.Internal.Data.OldList.partition", "partition"}, PgkA{"Data.Set.Internal.partition", "setPartition"}, PgkA{"Data.Map.Internal.partition", "mapPartition"}, PgkA{"Data.Map.Internal.mapMaybe", "mapMapMaybe"}, PgkA{"GHC.Internal.Data.Function.on", "onOp"}, PgkA{"Data.Map.Internal.unionWithKey", "unionWithKeyOp"}]

def sp.pc.gkeys() -> List<&2, List<&2, U32>>:
  [S.b("GHC.Internal.Data.OldList.sortOn"), S.b("GHC.Internal.Data.Ord.comparing"), S.b("GHC.Internal.Base.<>"), S.b("GHC.Internal.Base.mappend"), S.b("GHC.Internal.Base.mempty"), S.b("Data.Functor.Foldable.ana"), S.b("Control.Lens.Plated.transform"), S.b("Control.Comonad.Cofree.Class.unwrap"), S.b("GHC.Internal.Exception.throw")]

def sp.pc.gm.some(b: Bool, n: String, ts: List<&2, X.Sx>) -> Maybe<&2, Pgm>:
  match b:
    case True{}:
      Some{Pgm{n, ts}}
    case False{}:
      None{}

# a list, a pair or a Maybe with a Fix or a Cofree in it
def sp.pc.fixin(t: X.Sx) -> Bool:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{+n}, +r}}}:
      Bool.or(Bool.and(sp.is(a, "tc"), Bool.or(sp.is(sp.key(m, n), "Data.Fix.Fix"), sp.is(sp.key(m, n), "Control.Comonad.Cofree.Cofree"))), sp.pc.fixin(r))
    case X.SxCons{h, r}:
      Bool.or(sp.pc.fixin(h), sp.pc.fixin(r))
    case u:
      False{}

def sp.pc.boxed(+t: X.Sx) -> Bool:
  +k = sp.tckey(t)
  Bool.and(Bool.or(sp.is(k, "GHC.Types.List"), Bool.or(sp.is(k, "GHC.Tuple.Tuple2"), sp.is(k, "GHC.Internal.Maybe.Maybe"))), sp.pc.fixin(t))

def sp.pc.gm.tab(ks: List<&2, Pgk>, +k: List<&2, U32>, +ty: List<&2, X.Sx>) -> Maybe<&2, Pgm>:
  match ks:
    case Nil{}:
      None{}
    case PgkL{+q, n} <> t:
      +m = Maybe.default(&2, X.Sx, sp.nth(ty, 1n), X.SxNil{})
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => sp.pc.gm.some(Bool.and(sp.pc.atlist(ty), sp.pc.lmon(m)), n, sp.pc.drop(1n, ty)), _ => None{}), sp.pc.gm.tab(t, k, ty))
    case PgkH{+q, n} <> t:
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => sp.pc.gm.some(sp.pc.atlist(ty), n, sp.pc.drop(1n, ty)), _ => None{}), sp.pc.gm.tab(t, k, ty))
    case PgkM{+q, n} <> t:
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => sp.pc.gm.some(sp.is(sp.tckey(sp.first(ty)), "GHC.Internal.Maybe.Maybe"), n, sp.pc.drop(1n, ty)), _ => None{}), sp.pc.gm.tab(t, k, ty))
    case PgkO{+q, n} <> t:
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => sp.pc.gm.some(sp.pc.own(sp.first(ty)), n, ty), _ => None{}), sp.pc.gm.tab(t, k, ty))
    case PgkS{+q, n} <> t:
      +t0 = sp.first(ty)
      +own = Bool.or(Bool.and(sp.pc.own(t0), Bool.not(S.prefix(sp.pc.tcmod(t0), S.b("HsPrelude")))), sp.pc.boxed(t0))
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => sp.pc.gm.some(own, n, ty), _ => None{}), sp.pc.gm.tab(t, k, ty))
    case PgkA{+q, n} <> t:
      Maybe.or(&2, Pgm, sp.if(Maybe<&2, Pgm>, sp.is(k, q), _ => Some{Pgm{n, ty}}, _ => None{}), sp.pc.gm.tab(t, k, ty))

# sortOn and comparing at a key that is a Down
def sp.pc.gm.down(d: Bool, +k: List<&2, U32>, +ty: List<&2, X.Sx>) -> Maybe<&2, Pgm>:
  match d:
    case True{}:
      Maybe.or(&2, Pgm, sp.pc.gm.some(sp.is(k, "GHC.Internal.Data.OldList.sortOn"), "sortOnOp", ty), sp.pc.gm.some(sp.is(k, "GHC.Internal.Data.Ord.comparing"), "comparingOp", ty))
    case False{}:
      None{}

def sp.pc.gm(+k: List<&2, U32>, +ty: List<&2, X.Sx>) -> Maybe<&2, Pgm>:
  +t0 = sp.first(ty)
  +h = sp.tckey(t0)
  +x = sp.at(t0, 3n)
  +y = sp.at(t0, 4n)
  +mb = sp.is(h, "GHC.Internal.Maybe.Maybe")
  +co = sp.is(h, "Control.Comonad.Cofree.Cofree")
  +fx = sp.is(h, "Data.Fix.Fix")
  +app = Bool.or(sp.is(k, "GHC.Internal.Base.<>"), sp.is(k, "GHC.Internal.Base.mappend"))
  +t1 = Maybe.default(&2, X.Sx, sp.nth(ty, 1n), X.SxNil{})
  +th = Bool.and(sp.is(k, "GHC.Internal.Exception.throw"), sp.pc.own(Maybe.default(&2, X.Sx, sp.nth(ty, 2n), X.SxNil{})))
  +uw = Bool.and(sp.is(k, "Control.Comonad.Cofree.Class.unwrap"), sp.is(sp.tckey(t1), "Control.Comonad.Cofree.Cofree"))
  Maybe.or(&2, Pgm, sp.pc.gm.down(sp.is(h, "Cata.Base.Down"), k, ty), Maybe.or(&2, Pgm, sp.pc.gm.some(Bool.and(mb, app), "maybeAppend", [x]), Maybe.or(&2, Pgm, sp.pc.gm.some(Bool.and(mb, sp.is(k, "GHC.Internal.Base.mempty")), "maybeMempty", [x]), Maybe.or(&2, Pgm, sp.pc.gm.some(Bool.and(co, sp.is(k, "Data.Functor.Foldable.ana")), "anaCofree", x <> y <> sp.pc.drop(1n, ty)), Maybe.or(&2, Pgm, sp.pc.gm.some(Bool.and(fx, sp.is(k, "Data.Functor.Foldable.ana")), "anaFix", x <> sp.pc.drop(1n, ty)), Maybe.or(&2, Pgm, sp.pc.gm.some(Bool.and(co, sp.is(k, "Control.Lens.Plated.transform")), "transformCofree", [x, y]), Maybe.or(&2, Pgm, sp.pc.gm.some(th, "throwOp", sp.pc.drop(1n, ty)), Maybe.or(&2, Pgm, sp.pc.gm.some(uw, "unwrapCofree", [sp.at(t1, 3n), Maybe.default(&2, X.Sx, sp.nth(ty, 2n), X.SxNil{})]), sp.pc.gm.tab(sp.pc.gtab(), k, ty)))))))))

def sp.strs0(xs: List<String>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      S.b(h) <> sp.strs0(t)

# how many types the model's def (n) takes
def sp.pc.gn(+n: String) -> Nat:
  +b = S.b(n)
  +one = S.mem(b, sp.strs0(["maybeAppend", "maybeMempty", "showsDefault", "maybeNull", "maybeAny", "maybeAll", "maybeElem", "maybeToListF", "maybeLength", "partition", "setPartition", "whenOp", "unlessOp", "orDefault", "andDefault"]))
  +two = Bool.or(S.prefix(b, S.b("listSequence")), S.mem(b, sp.strs0(["transformCofree", "unwrapCofree", "anaFix", "toListDefault", "sumDefault", "productDefault", "lengthDefault", "maybeSequenceA", "voidOp", "anyDefault", "allDefault", "mapPartition", "unionWithKeyOp", "nullDefault", "elemDefault", "returnOp", "maybeFoldMap", "throwOp"])))
  Bool.pick(Nat, one, 1n, Bool.pick(Nat, Bool.or(two, S.mem(b, sp.strs0(["maybeFoldr", "maybeConcatMap", "sortOnOp", "comparingOp"]))), 2n, Bool.pick(Nat, Bool.or(sp.is(b, "liftM2Op"), sp.is(b, "mapMOp")), 4n, 3n)))

def sp.pc.gput(m: Maybe<&2, Pgm>) -> Maybe<&2, X.Sx>:
  match m:
    case Some{Pgm{+n, +ts}}:
      Bool.pick(Maybe<&2, X.Sx>, Nat.is_eq(List.length(&2, X.Sx, ts), sp.pc.gn(n)), Some{sp.pc.tyapps(ts, sp.g(S.b("Cata.Base"), S.b(n), "var"))}, None{})
    case None{}:
      None{}

def sp.pc.gkeyed(ks: List<&2, Pgk>, +k: List<&2, U32>) -> Bool:
  match ks:
    case Nil{}:
      S.mem(k, sp.pc.gkeys())
    case PgkL{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))
    case PgkH{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))
    case PgkM{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))
    case PgkO{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))
    case PgkS{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))
    case PgkA{q, n} <> t:
      Bool.or(sp.is(k, q), sp.pc.gkeyed(t, k))

# whether the package has these (Cata.Base with listTraverse)
def sp.ix.hasgen(ix: Ix) -> Bool:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Maybe.is_some(&2, X.Sx, sp.df.find(fns, S.b("Cata.Base.listTraverse")))

def sp.pc.gen(chain: Bool, +k: List<&2, U32>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match chain:
    case True{}:
      sp.if(Maybe<&2, X.Sx>, sp.pc.gkeyed(sp.pc.gtab(), k), _ => sp.if(Maybe<&2, X.Sx>, sp.ix.hasgen(ix), _ => sp.pc.gput(sp.pc.gm(k, sp.norms(tys, ix))), _ => None{}), _ => None{})
    case False{}:
      None{}

# fmap g a <*> b at a package's own Applicative is liftA2 g a b, its
# instance's (its value then holds no function, which is no Data), and
# fmap g a <*> b <*> c the model's liftA3Op
def sp.pc.isap(+f: X.Sx) -> Bool:
  +sf = sp.pc.strip(f)
  +p = sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{})
  Bool.and(sp.head.is(sf, "app"), Bool.and(sp.is(sp.pc.key(p), "GHC.Internal.Base.<*>"), sp.pc.own(sp.first(sp.pc.tys(p)))))

def sp.pc.isola2(+f: X.Sx) -> Bool:
  +l = sp.pc.strip(sp.at(sp.pc.strip(f), 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  Bool.and(sp.pc.isap(f), Bool.and(Bool.and(sp.head.is(l, "app"), sp.head.is(i, "app")), sp.is(sp.pc.key(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{})), "Cata.Base.fmapOp")))

def sp.pc.nthty(+ts: List<&2, X.Sx>, n: Nat) -> X.Sx:
  Maybe.default(&2, X.Sx, sp.nth(ts, n), X.SxNil{})

def sp.pc.ola2(+f: X.Sx, +x: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +ta = sp.pc.tys(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{}))
  +tf = sp.pc.tys(sp.pc.peel(sp.at(i, 1n), Nil{}, Nil{}))
  +me = sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("g"), X.SxStr{S.b("GHC.Internal.Base")}, X.SxStr{S.b("liftA2")}, sp.l([sp.a("method"), X.SxStr{S.b("GHC.Internal.Base")}, X.SxStr{S.b("Applicative")}])]), sp.first(ta)]), sp.l([sp.a("l"), X.SxStr{S.b("$dApplicative")}, sp.a("0")])])
  +la = sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), me, sp.pc.nthty(tf, 1n)]), sp.pc.nthty(ta, 1n)]), sp.pc.nthty(ta, 2n)])
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), la, sp.at(i, 2n)]), sp.at(l, 2n)]), x])

# liftA2's own call, (app (app (app LIFTA2 g) a) b)
def sp.pc.isola3(+f: X.Sx) -> Bool:
  +l = sp.pc.strip(sp.at(sp.pc.strip(f), 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +j = sp.pc.strip(sp.at(i, 1n))
  Bool.and(sp.pc.isap(f), Bool.and(Bool.and(sp.head.is(l, "app"), Bool.and(sp.head.is(i, "app"), sp.head.is(j, "app"))), sp.is(sp.pc.key(sp.pc.peel(sp.at(j, 1n), Nil{}, Nil{})), "GHC.Internal.Base.liftA2")))

def sp.pc.ola3(+f: X.Sx, +x: X.Sx) -> X.Sx:
  +sf = sp.pc.strip(f)
  +l = sp.pc.strip(sp.at(sf, 2n))
  +i = sp.pc.strip(sp.at(l, 1n))
  +j = sp.pc.strip(sp.at(i, 1n))
  +ta = sp.pc.tys(sp.pc.peel(sp.at(sf, 1n), Nil{}, Nil{}))
  +tl = sp.pc.tys(sp.pc.peel(sp.at(j, 1n), Nil{}, Nil{}))
  +h = sp.pc.tyapps([sp.first(ta), sp.pc.nthty(tl, 1n), sp.pc.nthty(tl, 2n), sp.pc.nthty(ta, 1n), sp.pc.nthty(ta, 2n)], sp.g(S.b("Cata.Base"), S.b("liftA3Op"), "var"))
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), h, sp.at(j, 2n)]), sp.at(i, 2n)]), sp.at(l, 2n)]), x])

# a node (a f e), its parts f2 and e2 rewritten
def sp.pc.three(+a: List<&2, U32>, +f: X.Sx, +e: X.Sx, +f2: X.Sx, +e2: X.Sx, +hb: Bool, +ix: Ix) -> X.Sx:
  +x = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}} : X.Sx}
  +chain = Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp"))
  +p = sp.pc.peel(x, Nil{}, Nil{})
  +m = sp.pc.find(sp.pc.tab(), sp.pc.key(p))
  +mb = sp.pc.find(sp.pc.btab(), sp.pc.key(p))
  +tys = sp.pc.tys(p)
  +isb = Bool.and(hb, Bool.and(chain, Bool.and(Maybe.is_some(&2, Pcr, mb), sp.pc.atlist(tys))))
  +mp = sp.pc.find(sp.pc.ptab(), sp.pc.key(p))
  +isp = Bool.and(hb, Bool.and(chain, Bool.and(Maybe.is_some(&2, Pcr, mp), sp.pc.atpair(tys))))
  +mk = sp.pc.find(sp.pc.ktab(), sp.pc.key(p))
  +isk = Bool.and(hb, Bool.and(chain, Maybe.is_some(&2, Pcr, mk)))
  +mc = sp.pc.find(sp.pc.ctab(), sp.pc.key(p))
  +isc = Bool.and(hb, Bool.and(chain, Bool.and(Maybe.is_some(&2, Pcr, mc), sp.pc.atcofreef(tys))))
  +mf = sp.pc.find(sp.pc.ftab(), sp.pc.key(p))
  +isf = Bool.and(hb, Bool.and(chain, sp.if(Bool, Maybe.is_some(&2, Pcr, mf), _ => sp.pc.atfix(sp.norms(tys, ix)), _ => False{})))
  +mcs = sp.pc.find(sp.pc.ctabs(), sp.pc.key(p))
  +iscs = Bool.and(hb, Bool.and(chain, sp.if(Bool, Maybe.is_some(&2, Pcr, mcs), _ => sp.pc.atcof(sp.norms(tys, ix)), _ => False{})))
  +mm = sp.pc.find(sp.pc.mtab(), sp.pc.key(p))
  +ism = Bool.and(hb, Bool.and(chain, Maybe.is_some(&2, Pcr, mm)))
  +x2 = {X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}} : X.Sx}
  +mg = sp.pc.gen(Bool.and(hb, chain), sp.pc.key(p), tys, ix)
  sp.if(X.Sx, Maybe.is_some(&2, X.Sx, mg), _ => sp.or(mg, x), _ => sp.if(X.Sx, Bool.and(chain, Maybe.is_some(&2, Pcr, m)), _ => sp.pc.model(m, tys, x), _ => sp.if(X.Sx, isb, _ => sp.pc.bmodel(mb, tys, x), _ => sp.if(X.Sx, isp, _ => sp.pc.pmodel(mp, tys, x), _ => sp.if(X.Sx, isk, _ => sp.pc.bmodel(mk, tys, x), _ => sp.if(X.Sx, isc, _ => sp.pc.cmodel(mc, tys, x), _ => sp.if(X.Sx, isf, _ => sp.pc.fmodel(mf, sp.norms(tys, ix), x), _ => sp.if(X.Sx, iscs, _ => sp.pc.cofmodel(mcs, sp.norms(tys, ix), x), _ => sp.if(X.Sx, ism, _ => sp.pc.amodel(mm, tys, x), _ => sp.if(X.Sx, sp.is(a, "app"), _ => sp.if(X.Sx, Bool.and(hb, sp.pc.isiter(f2)), _ => sp.pc.iter(f2, e2), _ => sp.if(X.Sx, Bool.and(hb, sp.pc.isla2(f2)), _ => sp.pc.la2(f2, e2), _ => sp.if(X.Sx, Bool.and(hb, sp.pc.isola2(f2)), _ => sp.pc.ola2(f2, e2), _ => sp.if(X.Sx, Bool.and(hb, sp.pc.isola3(f2)), _ => sp.pc.ola3(f2, e2), _ => sp.pc.app(f2, e2))))), _ => x2))))))))))

# (hb: whether the package exports Base's model, Cata.Base, before the
# module; without it a call stays base's)
def sp.pc(x: X.Sx, +hb: Bool, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      sp.pc.three(a, f, e, sp.pc(f, hb, ix), sp.pc(e, hb, ix), hb, ix)
    case X.SxCons{h, t}:
      X.SxCons{sp.pc(h, hb, ix), sp.pc(t, hb, ix)}
    case y:
      y

def sp.ix.hasbase(ix: Ix) -> Bool:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Maybe.is_some(&2, X.Sx, sp.df.find(fns, S.b("Cata.Base.foldr")))

# Local bindings generalised over a type ---------------------------------------

# Haskell 2010 generalises a local binding over the type variables and
# classes it uses (`check x = if .. then fail .. else pure x`, in a where,
# is over its monad). A local abs whose one export is used, everywhere in
# its scope, at one list of types with no variable is the binding at those
# types: its type variables those types, its dictionary binders dropped,
# each use the local itself.

# a use's type arguments: x a chain of type and dictionary applications
# down to the local v
def sp.pl.peel(x: X.Sx, +v: X.Sx, +tys: List<&2, X.Sx>) -> Maybe<&2, List<&2, X.Sx>>:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+t, X.SxNil{}}}}:
      +ty = sp.is(a, "tyapp")
      +ev = sp.is(a, "evapp")
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{t, X.SxNil{}}}} : X.Sx}
      sp.if(Maybe<&2, List<&2, X.Sx>>, Bool.or(ty, ev), _ => sp.pl.peel(f, v, Bool.pick(List<&2, X.Sx>, ty, t <> tys, tys)), _ => Bool.pick(Maybe<&2, List<&2, X.Sx>>, sp.eq(y, v), Some{tys}, None{}))
    case y:
      Bool.pick(Maybe<&2, List<&2, X.Sx>>, sp.eq(y, v), Some{tys}, None{})

# the type arguments of each use of v in x, onto acc
def sp.pl.uses(x: X.Sx, +v: X.Sx, +acc: List<&2, List<&2, X.Sx>>) -> List<&2, List<&2, X.Sx>>:
  match x:
    case X.SxCons{+h, +t}:
      +m = sp.pl.peel(X.SxCons{h, t}, v, Nil{})
      sp.if(List<&2, List<&2, X.Sx>>, Maybe.is_some(&2, List<&2, X.Sx>, m), _ => Maybe.default(&2, List<&2, X.Sx>, m, Nil{}) <> acc, _ => sp.pl.uses(h, v, sp.pl.uses(t, v, acc)))
    case _:
      acc

def sp.pl.uses.all(xs: List<&2, X.Sx>, +v: X.Sx, +acc: List<&2, List<&2, X.Sx>>) -> List<&2, List<&2, X.Sx>>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      sp.pl.uses.all(t, v, sp.pl.uses(x, v, acc))

# x, each use of v the local itself
def sp.pl.strip(x: X.Sx, +v: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      sp.if(X.Sx, Maybe.is_some(&2, List<&2, X.Sx>, sp.pl.peel(X.SxCons{h, t}, v, Nil{})), _ => v, _ => X.SxCons{sp.pl.strip(h, v), sp.pl.strip(t, v)})
    case y:
      y

def sp.pl.strips(xs: List<&2, X.Sx>, +v: X.Sx) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.pl.strip(x, v) <> sp.pl.strips(t, v)

def sp.pl.same(us: List<&2, List<&2, X.Sx>>, +u: X.Sx) -> Bool:
  match us:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(sp.eq(sp.l(x), u), sp.pl.same(t, u))

# a group (nonrec (abs TVS EVBS ((export V TY)) EVBINDS BINDS SPAN)) over
# type variables: its local V, else none; a recursive group (rec (abs ..))
# with one export too (`go` in `findB (BVar i) = go i where go j = ..
# go p ..`): its own calls inside are to the binding itself, (self V),
# with no type arguments, so only its uses in the scope are read
def sp.pl.cand(+g: X.Sx) -> Maybe<&2, X.Sx>:
  +ab = sp.at(g, 1n)
  +xps = sp.els(sp.at(ab, 3n))
  +one = Nat.is_eq(List.length(&2, X.Sx, xps), 1n)
  +ex = sp.first(xps)
  +ok = Bool.and(Bool.and(Bool.or(sp.head.is(g, "nonrec"), sp.head.is(g, "rec")), sp.head.is(ab, "abs")), Bool.and(Bool.not(sp.eq(sp.at(ab, 1n), X.SxNil{})), Bool.and(one, sp.head.is(sp.at(ex, 1n), "l"))))
  Bool.pick(Maybe<&2, X.Sx>, ok, Some{sp.at(ex, 1n)}, None{})

def sp.pl.export(+e: X.Sx, +sbs: List<&2, Sb>, +ix: Ix) -> X.Sx:
  sp.l([sp.at(e, 0n), sp.at(e, 1n), sp.norm(sp.strip(sp.subst(sp.at(e, 2n), sbs)), ix)])

def sp.pl.exports(es: List<&2, X.Sx>, +sbs: List<&2, Sb>, +ix: Ix) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      sp.pl.export(e, sbs, ix) <> sp.pl.exports(t, sbs, ix)

# the group at the types us (one use's)
def sp.pl.at(+g: X.Sx, +u: List<&2, X.Sx>, +ix: Ix) -> X.Sx:
  +ab = sp.at(g, 1n)
  +sbs = sp.zip(sp.strs(sp.at(ab, 1n)), u)
  sp.l([sp.at(g, 0n), sp.l([sp.at(ab, 0n), X.SxNil{}, X.SxNil{}, sp.l(sp.pl.exports(sp.els(sp.at(ab, 3n)), sbs, ix)), sp.norm(sp.subst(sp.at(ab, 4n), sbs), ix), sp.norm(sp.subst(sp.at(ab, 5n), sbs), ix), sp.at(ab, 6n)])])

# A scope: its body (a grhss's guarded right-hand sides, a let's
# expression) and its groups, the ones before in pre (reversed), the ones
# after in post; n is post's length
type Pls is Data:
  Pls{body: X.Sx, pre: List<&2, X.Sx>}

def sp.pl.first(us: List<&2, List<&2, X.Sx>>) -> X.Sx:
  match us:
    case u <> t:
      sp.l(u)
    case Nil{}:
      X.SxNil{}

# the type variables of x (each (tv V)'s V), onto acc
def sp.pl.tvs(x: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+v}, X.SxNil{}}}:
      Bool.pick(List<&2, List<&2, U32>>, sp.is(a, "tv"), v <> acc, acc)
    case X.SxCons{h, t}:
      sp.pl.tvs(h, sp.pl.tvs(t, acc))
    case _:
      acc

# whether each of vs is one of tvs
def sp.pl.inscope(vs: List<&2, List<&2, U32>>, +tvs: List<&2, List<&2, U32>>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> t:
      Bool.and(S.mem(v, tvs), sp.pl.inscope(t, tvs))

# the type variables a top is generalised over (its exports' foralls): in
# scope everywhere in it, so a local used at them (i2t's coalg, over its
# Num and the top's l and v, used at Int, l and v) is the binding at those
# types as well as at types with no variable
def sp.pl.extvs(es: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      List.append(&2, List<&2, U32>, sp.foralls(sp.at(e, 2n)), sp.pl.extvs(t))

def sp.pl.toptvs(+x: X.Sx) -> List<&2, List<&2, U32>>:
  Bool.pick(List<&2, List<&2, U32>>, sp.head.is(x, "top"), sp.pl.extvs(sp.els(sp.at(sp.at(x, 1n), 3n))), Nil{})

def sp.pl.step(m: Maybe<&2, X.Sx>, +g: X.Sx, +body: X.Sx, +pre: List<&2, X.Sx>, +post: List<&2, X.Sx>, +tvs: List<&2, List<&2, U32>>, +ix: Ix) -> Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>:
  match m:
    case Some{+v}:
      +us = sp.pl.uses.all(body <> List.append(&2, X.Sx, pre, post), v, Nil{})
      +u0 = sp.pl.first(us)
      +ok = Bool.and(Bool.not(List.is_empty(&2, List<&2, X.Sx>, us)), Bool.and(sp.pl.same(us, u0), Bool.and(Bool.not(sp.eq(u0, X.SxNil{})), sp.pl.inscope(sp.pl.tvs(u0, Nil{}), tvs))))
      sp.if(Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>, ok, _ => (Pls{sp.pl.strip(body, v), sp.pl.at(g, sp.els(u0), ix) <> sp.pl.strips(pre, v)}, sp.pl.strips(post, v)), _ => (Pls{body, g <> pre}, post))
    case None{}:
      (Pls{body, g <> pre}, post)

def sp.pl.fst(st: Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>) -> Pls:
  (s, r) = st
  s

def sp.pl.go(n: Nat, st: Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>, +tvs: List<&2, List<&2, U32>>, +ix: Ix) -> Pls:
  match n:
    case 1n+k:
      match st:
        case (Pls{+body, +pre}, +g <> t):
          sp.pl.go(k, sp.pl.step(sp.pl.cand(g), g, body, pre, t, tvs, ix), tvs, ix)
        case (s, r):
          s
    case 0n:
      sp.pl.fst(st)

def sp.pl.tail(x: X.Sx) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{h, t}:
      sp.els(t)
    case _:
      Nil{}

def sp.pl.scope(+body: X.Sx, +binds: X.Sx, +tvs: List<&2, List<&2, U32>>, +ix: Ix) -> Pls:
  +gs = sp.pl.tail(binds)
  sp.pl.go(List.length(&2, X.Sx, gs), (Pls{body, Nil{}}, gs), tvs, ix)

def sp.pl.grhss(s: Pls) -> X.Sx:
  match s:
    case Pls{b, pre}:
      sp.l([sp.a("grhss"), b, X.SxCons{sp.a("binds"), sp.l(List.reverse(&2, X.Sx, pre))}])

def sp.pl.let(s: Pls) -> X.Sx:
  match s:
    case Pls{b, pre}:
      sp.l([sp.a("let"), X.SxCons{sp.a("binds"), sp.l(List.reverse(&2, X.Sx, pre))}, b])

# (grhss GRHSS (binds G..)) and (let (binds G..) E), their scopes done
def sp.pl.node(+a: List<&2, U32>, +x: X.Sx, +tvs: List<&2, List<&2, U32>>, +ix: Ix) -> X.Sx:
  +gr = Bool.and(sp.is(a, "grhss"), sp.head.is(sp.at(x, 2n), "binds"))
  +lt = Bool.and(sp.is(a, "let"), sp.head.is(sp.at(x, 1n), "binds"))
  sp.if(X.Sx, gr, _ => sp.pl.grhss(sp.pl.scope(sp.at(x, 1n), sp.at(x, 2n), tvs, ix)), _ => sp.if(X.Sx, lt, _ => sp.pl.let(sp.pl.scope(sp.at(x, 2n), sp.at(x, 1n), tvs, ix)), _ => x))

# bottom up: a scope's parts first
def sp.pl(x: X.Sx, +tvs: List<&2, List<&2, U32>>, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      sp.pl.node(a, X.SxCons{X.SxAtom{a}, sp.pl(t, tvs, ix)}, tvs, ix)
    case X.SxCons{h, t}:
      X.SxCons{sp.pl(h, tvs, ix), sp.pl(t, tvs, ix)}
    case y:
      y

# A lambda applied ------------------------------------------------------------------

# (\x -> e) a is e with a for x (a lambda of one clause, one variable, no
# guard and no local binding): a copy at a known function argument applies
# it (lineFold sc (\sc' -> p `sepBy1` try sc') calls the lambda with sc' a
# parser), and the parser it is given is known there, for the copies inside
# it. The locals are numbered apart, so nothing is captured.
def sp.beta.sub(+x: X.Sx, +v: X.Sx, +a: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      sp.if(X.Sx, sp.eq(X.SxCons{h, t}, v), _ => a, _ => X.SxCons{sp.beta.sub(h, v, a), sp.beta.sub(t, v, a)})
    case y:
      Bool.pick(X.Sx, sp.eq(y, v), a, y)

# Copies -------------------------------------------------------------------------------

# where a copy's binding is: a global def (M.N) or a module's top local
type Lo is Data:
  LoG{k: List<&2, U32>}
  LoL{m: List<&2, U32>, i: List<&2, U32>}
  LoF{k: List<&2, U32>, fas: List<&2, Fa>, fvt: List<&2, X.Sx>, rg: List<&2, X.Sx>}
  LoFl{k: List<&2, U32>, fas: List<&2, Fa>, fvt: List<&2, X.Sx>, gv: X.Sx, rg: List<&2, X.Sx>}
  LoFm{n: List<&2, U32>, m: List<&2, U32>, i: List<&2, U32>, mtys: List<&2, X.Sx>, fas: List<&2, Fa>, fvt: List<&2, X.Sx>, rg: List<&2, X.Sx>}
  LoFlm{n: List<&2, U32>, m: List<&2, U32>, i: List<&2, U32>, mtys: List<&2, X.Sx>, fas: List<&2, Fa>, fvt: List<&2, X.Sx>, gv: X.Sx, rg: List<&2, X.Sx>}

# a copy asked for: its name, its binding, its type variables' values
type Rq is Data:
  Rq{n: List<&2, U32>, lo: Lo, tys: List<&2, X.Sx>}

# a rewritten tree and the copies it asks for
type Rw is Data:
  Rw{x: X.Sx, rq: List<&2, Rq>}

def sp.rw.cat(a: List<&2, Rq>, b: List<&2, Rq>) -> List<&2, Rq>:
  List.append(&2, Rq, a, b)

def sp.rw.cons(a: Rw, b: Rw) -> Rw:
  match a b:
    case Rw{x, p} Rw{y, q}:
      Rw{X.SxCons{x, y}, sp.rw.cat(p, q)}

def sp.rw.cons3(a: Rw, b: Rw, c: Rw) -> Rw:
  match a b c:
    case Rw{x, p} Rw{y, q} Rw{z, r}:
      Rw{X.SxCons{x, X.SxCons{y, z}}, sp.rw.cat(p, sp.rw.cat(q, r))}

# a def's type variables, in its type's foralls' order
def sp.df.tvs(m: Maybe<&2, X.Sx>) -> Maybe<&2, Nat>:
  match m:
    case Some{top}:
      Maybe.map(&2, X.Sx, Nat, f => List.length(&2, List<&2, U32>, sp.foralls(sp.at(f, 2n))), sp.fun.of(top))
    case None{}:
      None{}

def sp.ask(+cur: List<&2, U32>, +n: List<&2, U32>, lo: Lo, +tys: List<&2, X.Sx>) -> Maybe<&2, Rw>:
  Some{Rw{sp.g(cur, n, "var"), [Rq{n, lo, tys}]}}

# a call of a global def that takes dictionaries, all its type arguments
# given
def sp.ask.def(+cur: List<&2, U32>, +h: X.Sx, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Rw>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +k = sp.gkey(h)
      +nt = sp.df.tvs(sp.df.find(dfs, k))
      Bool.pick(Maybe<&2, Rw>, Bool.and(Maybe.is_some(&2, Nat, nt), Nat.is_eq(Maybe.default(&2, Nat, nt, 0n), List.length(&2, X.Sx, tys))), sp.ask(cur, sp.name(sp.sat(h, 2n), tys), LoG{k}, tys), None{})

# the derived methods copied as hand-written ones: Show's (showsPrec, show,
# showList), and Functor's, Foldable's and Traversable's (GHC's generated
# fmap, <$, foldr, foldMap, null and traverse: constructors, lambdas and
# the fields' own methods)
def sp.derived.ok(+n: List<&2, U32>) -> Bool:
  +fo = Bool.or(S.prefix(n, S.b("$cfoldr")), Bool.or(S.prefix(n, S.b("$cfoldMap")), S.eq(n, S.b("$cnull"))))
  Bool.or(Bool.or(S.prefix(n, S.b("$cshow")), S.eq(n, S.b("$ctraverse"))), Bool.or(Bool.or(S.eq(n, S.b("$cfmap")), S.eq(n, S.b("$c<$"))), fo))

# a method at an instance the package wrote by hand: a copy of the
# instance's method (a default method: a copy of it)
def sp.ask.impl(+impl: X.Sx, +m: List<&2, U32>, +sbs: List<&2, Sb>, +ntv: Nat, +cur: List<&2, U32>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Rw>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +h = sp.vhead(impl)
      +itys = sp.norms(List.append(&2, X.Sx, sp.els(sp.subst(sp.l(sp.spine.tys(impl, Nil{})), sbs)), sp.dropn(tys, ntv)), Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts})
      +i = X.tsx.atom.of(sp.at(h, 2n))
      +top = sp.lc.find(lcs, m, i)
      +tt = Maybe.default(&2, X.Sx, top, X.SxNil{})
      +derived = Bool.and(sp.has(tt, S.b("generated")), Bool.not(Bool.or(sp.has.str(tt, S.b("coerce")), sp.derived.ok(sp.sat(h, 1n)))))
      Bool.pick(Maybe<&2, Rw>, Bool.and(sp.head.is(h, "l"), Bool.and(Maybe.is_some(&2, X.Sx, top), Bool.not(derived))), sp.ask(cur, sp.name(sp.sat(h, 1n), tys), LoL{m, i}, itys), Bool.pick(Maybe<&2, Rw>, sp.head.is(h, "g"), sp.ask.def(cur, h, itys, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}), None{}))

# Traversable's default sequence, sequenceA (t (f a) -> f (t a)) and mapM
# are traverse (at f, f a and a; at m, a and b): its copy, sequence's given id
def sp.wrap.id(r: Maybe<&2, Rw>, +ma: X.Sx) -> Maybe<&2, Rw>:
  match r:
    case Some{Rw{x, q}}:
      Some{Rw{sp.l([sp.a("app"), x, sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Internal.Base"), S.b("id"), "var"), ma])]), q}}
    case None{}:
      None{}

# Show's default show and showList (base's $dmshow, $dmshowList) at a type:
# HsPrelude.Z's showVia and showListVia given the instance's showsPrec (its
# first method)
def sp.wrap.via(r: Maybe<&2, Rw>, +n: List<&2, U32>, +t: X.Sx) -> Maybe<&2, Rw>:
  match r:
    case Some{Rw{x, q}}:
      Some{Rw{sp.l([sp.a("app"), sp.l([sp.a("tyapp"), sp.g(S.b("HsPrelude.Z"), n, "var"), t]), x]), q}}
    case None{}:
      None{}

# Show's default showsPrec (base's $dmshowsPrec): Base's model's
# showsPrecDefault given the instance's show (its second method)
def sp.wrap.sp(r: Maybe<&2, Rw>, +t: X.Sx) -> Maybe<&2, Rw>:
  match r:
    case Some{Rw{x, q}}:
      Some{Rw{sp.l([sp.a("app"), sp.l([sp.a("tyapp"), sp.g(S.b("Cata.Base"), S.b("showsPrecDefault"), "var"), t]), x]), q}}
    case None{}:
      None{}

def sp.ix.hasgen2(ix: Ix) -> Bool:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Maybe.is_some(&2, X.Sx, sp.df.find(fns, S.b("Cata.Base.showsPrecDefault")))

def sp.ask.meth(mi: Maybe<&2, Mi>, +cur: List<&2, U32>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Rw>:
  match mi:
    case Some{Mi{+impl, +m, +sbs, +ntv, +first, +snd}}:
      +k0 = sp.gkey(sp.vhead(impl))
      +k = Bool.pick(List<&2, U32>, sp.is(sp.hd(sp.vhead(impl)), "l"), sp.gkey(sp.vhead(sp.or(sp.impl.body(Some{Mi{impl, m, sbs, ntv, first, snd}}, tys, ix), X.SxNil{}))), k0)
      +seq = Bool.or(sp.is(k, "GHC.Internal.Data.Traversable.$dmsequence"), sp.is(k, "GHC.Internal.Data.Traversable.$dmsequenceA"))
      +mapm = sp.is(k, "GHC.Internal.Data.Traversable.$dmmapM")
      +shw = sp.is(k, "GHC.Internal.Show.$dmshow")
      +shl = sp.is(k, "GHC.Internal.Show.$dmshowList")
      +shp = Bool.and(sp.is(k, "GHC.Internal.Show.$dmshowsPrec"), sp.ix.hasgen2(ix))
      +t0 = Maybe.default(&2, X.Sx, sp.nth(tys, 0n), X.SxNil{})
      +f1 = Maybe.default(&2, X.Sx, sp.nth(tys, 1n), X.SxNil{})
      +a2 = Maybe.default(&2, X.Sx, sp.nth(tys, 2n), X.SxNil{})
      +fa = sp.norm(sp.l([sp.a("tapp"), f1, a2]), ix)
      sp.if(Maybe<&2, Rw>, shp, _ => sp.wrap.sp(sp.ask.impl(snd, m, sbs, ntv, cur, tys, ix), t0), _ => Bool.pick(Maybe<&2, Rw>, Bool.or(shw, shl), sp.wrap.via(sp.ask.impl(first, m, sbs, ntv, cur, tys, ix), Bool.pick(List<&2, U32>, shw, S.b("showVia"), S.b("showListVia")), t0),       Bool.pick(Maybe<&2, Rw>, seq, sp.wrap.id(sp.ask.impl(first, m, sbs, ntv, cur, [t0, f1, fa, a2], ix), fa), Bool.pick(Maybe<&2, Rw>, mapm, sp.ask.impl(first, m, sbs, ntv, cur, tys, ix), sp.ask.impl(impl, m, sbs, ntv, cur, tys, ix)))))
    case None{}:
      None{}

# a (tyapp)/(evapp) spine at types with no variable left: a copy's call,
# or none
# which asking a spine is
type Dk is Data:
  DkMeth{}
  DkDef{}
  DkNo{}

def sp.p4.ask(k: Dk, +h: X.Sx, +tys: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, Rw>:
  match k:
    case DkMeth{}:
      sp.ask.meth(sp.method(h, tys, ix), cur, tys, ix)
    case DkDef{}:
      sp.ask.def(cur, h, tys, ix)
    case DkNo{}:
      None{}

# Show at a list, Maybe, a pair, a Map or a Set that holds one of the
# package's types (base's instance, given theirs): the prelude's HsShow at
# the parts' showsPrec (HsPrelude.Z's spList, spMaybe, spPair, spMap,
# spSet, each the showsPrec of its type), a part's the copy of its
# instance's, or base's where no type of the package is in it.  showsPrec
# is that; show and showList showVia and showListVia of it.
def sp.shw.prec() -> X.Sx:
  sp.l([sp.a("g"), X.SxStr{S.b("GHC.Internal.Show")}, X.SxStr{S.b("showsPrec")}, sp.l([sp.a("method"), X.SxStr{S.b("GHC.Internal.Show")}, X.SxStr{S.b("Show")}])])

# whether a type holds one of the package's that shows itself
def sp.shw.any(x: X.Sx, +ix: Ix) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +own = sp.if(Bool, sp.is(X.tsx.atom.of(h), "tc"), _ => Bool.or(Bool.or(sp.pc.atfix([n]), sp.pc.atcof([n])), Maybe.is_some(&2, Mi, sp.method(sp.shw.prec(), [n], ix))), _ => False{})
      Bool.or(own, Bool.or(sp.shw.any(h, ix), sp.shw.any(t, ix)))
    case _:
      False{}

# base's instances at these: the name of the prelude's showsPrec, how many
# parts
type Sw is Data:
  Sw{k: String, f: String, n: Nat, g: String}

def sp.shw.tab() -> List<&2, Sw>:
  [Sw{"GHC.Types.List", "spList", 1n, "showListWith"}, Sw{"GHC.Internal.Maybe.Maybe", "spMaybe", 1n, "showMaybeWith"}, Sw{"GHC.Tuple.Tuple2", "spPair", 2n, "showPairWith"}, Sw{"Data.Map.Internal.Map", "spMap", 2n, ""}, Sw{"Data.Set.Internal.Set", "spSet", 1n, ""}]

def sp.shw.find(ws: List<&2, Sw>, +k: List<&2, U32>) -> Maybe<&2, Sw>:
  match ws:
    case Nil{}:
      None{}
    case Sw{+q, f, n, g} <> t:
      sp.if(Maybe<&2, Sw>, sp.is(k, q), _ => Some{Sw{q, f, n, g}}, _ => sp.shw.find(t, k))

# F applied to its parts' showsPrecs
def sp.shw.args(ms: List<&2, Maybe<&2, Rw>>, f: X.Sx, rq: List<&2, Rq>) -> Maybe<&2, Rw>:
  match ms:
    case Nil{}:
      Some{Rw{f, rq}}
    case Some{Rw{x, q}} <> t:
      sp.shw.args(t, sp.l([sp.a("app"), f, x]), sp.rw.cat(rq, q))
    case None{} <> t:
      None{}

def sp.shw.tyapps(ts: List<&2, X.Sx>, f: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      f
    case t <> r:
      sp.shw.tyapps(r, sp.l([sp.a("tyapp"), f, t]))

# whether the package has the model of base's showsPrecs (Cata.Base)
def sp.ix.hasbase2(ix: Ix) -> Bool:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      Maybe.is_some(&2, X.Sx, sp.df.find(fns, S.b("Cata.Base.showMaybeWith")))

# base's instance at its parts' showsPrecs
# (the model's, Cata.Base, when the package has it)
def sp.shw.head(hb: Bool, +f: String, +g: String) -> X.Sx:
  sp.if(X.Sx, Bool.and(hb, Bool.not(List.is_empty(&2, U32, S.b(g)))), _ => sp.g(S.b("Cata.Base"), S.b(g), "var"), _ => sp.g(S.b("HsPrelude.Z"), S.b(f), "var"))

def sp.shw.at(w: Maybe<&2, Sw>, +hb: Bool, +parts: List<&2, X.Sx>, ms: List<&2, Maybe<&2, Rw>>) -> Maybe<&2, Rw>:
  match w:
    case Some{Sw{k, f, n, g}}:
      sp.if(Maybe<&2, Rw>, Nat.is_eq(List.length(&2, X.Sx, parts), n), _ => sp.shw.args(ms, sp.shw.tyapps(parts, sp.shw.head(hb, f, g)), Nil{}), _ => None{})
    case None{}:
      None{}

# showsPrec at each type of ts, as a term (fuel: their depth and number)
def sp.shw.all(fuel: Nat, ts: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> List<&2, Maybe<&2, Rw>>:
  match fuel ts:
    case 1n+(+p) +ty <> t:
      +m = sp.method(sp.shw.prec(), [ty], ix)
      +w = sp.shw.find(sp.shw.tab(), sp.tckey(ty))
      +parts = sp.dropn(sp.els(ty), 3n)
      +base = {Some{Rw{sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.shw.prec(), ty]), sp.l([sp.a("l"), X.SxStr{S.b("$dShow")}, sp.a("0")])]), Nil{}}} : Maybe<&2, Rw>}
      +r = {sp.if(Maybe<&2, Rw>, Maybe.is_some(&2, Mi, m), _ => sp.ask.meth(m, cur, [ty], ix), _ => sp.if(Maybe<&2, Rw>, sp.pc.atcof([ty]), _ => sp.ask.def(cur, sp.g(S.b("Cata.Base"), S.b("cofreeShowsPrec"), "var"), [sp.at(ty, 3n), sp.at(ty, 4n)], ix), _ => sp.if(Maybe<&2, Rw>, sp.pc.atfix([ty]), _ => sp.ask.def(cur, sp.g(S.b("Cata.Base"), S.b("fixShowsPrec"), "var"), [sp.at(ty, 3n)], ix), _ => sp.if(Maybe<&2, Rw>, Bool.not(sp.shw.any(ty, ix)), _ => base, _ => sp.shw.at(w, sp.ix.hasbase2(ix), parts, sp.shw.all(p, parts, cur, ix)))))) : Maybe<&2, Rw>}
      r <> sp.shw.all(p, t, cur, ix)
    case _ _:
      Nil{}

def sp.shw.hd(ms: List<&2, Maybe<&2, Rw>>) -> Maybe<&2, Rw>:
  match ms:
    case m <> t:
      m
    case Nil{}:
      None{}

# show and showList by a showsPrec
def sp.shw.meth(+n: List<&2, U32>, +ty: X.Sx, +m: Maybe<&2, Rw>) -> Maybe<&2, Rw>:
  sp.if(Maybe<&2, Rw>, sp.is(n, "showsPrec"), _ => m, _ => sp.wrap.via(m, Bool.pick(List<&2, U32>, sp.is(n, "show"), S.b("showVia"), S.b("showListVia")), ty))

# Show's method h at a type of base's that holds one of the package's
def sp.shw(+h: X.Sx, +ty: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, Rw>:
  +w = sp.shw.find(sp.shw.tab(), sp.tckey(ty))
  +ok = Bool.and(sp.is(sp.method.cls(h), "GHC.Internal.Show.Show"), Maybe.is_some(&2, Sw, w))
  sp.if(Maybe<&2, Rw>, ok, _ => sp.if(Maybe<&2, Rw>, sp.shw.any(ty, ix), _ => sp.shw.meth(sp.sat(h, 2n), ty, sp.shw.hd(sp.shw.all(64n, [ty], cur, ix))), _ => None{}), _ => None{})

def sp.p4.decide(isp: Bool, +x: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, Rw>:
  match isp:
    case True{}:
      +h = sp.vhead(x)
      +tys = sp.norms(sp.spine.tys(x, Nil{}), ix)
      +meth = Bool.not(S.eq(sp.method.cls(h), Nil{}))
      +cl = sp.all.closed(tys)
      +sh = {sp.if(Maybe<&2, Rw>, Bool.and(meth, cl), _ => sp.shw(h, sp.first(tys), cur, ix), _ => None{}) : Maybe<&2, Rw>}
      sp.if(Maybe<&2, Rw>, Maybe.is_some(&2, Rw, sh), _ => sh, _ => sp.p4.ask(Bool.pick(Dk, Bool.not(cl), DkNo{}, Bool.pick(Dk, meth, DkMeth{}, Bool.pick(Dk, sp.head.is(h, "g"), DkDef{}, DkNo{}))), h, tys, cur, ix))
    case False{}:
      None{}

def sp.rw.or(m: Maybe<&2, Rw>, d: Rw) -> Rw:
  match m:
    case Some{r}:
      r
    case None{}:
      d

# each call of a def or method that takes dictionaries, at known types, as
# its copy's; top: x is not a spine's function (so a spine is judged whole)
def sp.p4(x: X.Sx, top: Bool, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match x:
    case X.SxCons{+h, X.SxCons{+e, +r}}:
      +a = X.tsx.atom.of(h)
      +isp = Bool.and(top, Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp")))
      +inner = Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp"))
      sp.rw.or(sp.p4.decide(isp, X.SxCons{h, X.SxCons{e, r}}, cur, ix), sp.rw.cons3(sp.p4(h, True{}, cur, ix), sp.p4(e, Bool.not(inner), cur, ix), sp.p4(r, True{}, cur, ix)))
    case X.SxCons{+h, X.SxNil{}}:
      sp.rw.cons(sp.p4(h, True{}, cur, ix), Rw{X.SxNil{}, Nil{}})
    case y:
      Rw{y, Nil{}}

# a variable inside (self ..) wrappers
def sp.var.of(v: X.Sx) -> X.Sx:
  match v:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+inner, X.SxNil{}}}:
      Bool.pick(X.Sx, sp.is(a, "self"), sp.var.of(inner), X.SxCons{X.SxAtom{a}, X.SxCons{inner, X.SxNil{}}})
    case y:
      y

# each (self X) whose X is the copied binding's var orig, as (self var)
def sp.selfs(x: X.Sx, +orig: X.Sx, +var: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(X.Sx, Bool.and(sp.is(X.tsx.atom.of(h), "self"), sp.eq(sp.var.of(X.SxCons{h, t}), orig)), sp.l([sp.a("self"), var]), X.SxCons{sp.selfs(h, orig, var), sp.selfs(t, orig, var)})
    case y:
      y

# a copy's top: the binding's fun at the types, its foralls and contexts
# gone, its recursive references the copy's
def sp.copy.of(f: Maybe<&2, X.Sx>, +tvs0: List<&2, List<&2, U32>>, +n: List<&2, U32>, +tys: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match f:
    case Some{+fun}:
      +sbs = sp.zip(List.append(&2, List<&2, U32>, tvs0, sp.foralls(sp.at(fun, 2n))), tys)
      +var = sp.g(cur, n, "var")
      +ty = sp.norm(sp.subst(sp.strip(sp.at(fun, 2n)), sbs), ix)
      +ms = sp.norm(sp.selfs(sp.subst(sp.at(fun, 4n), sbs), sp.var.of(sp.at(fun, 1n)), var), ix)
      Some{sp.l([sp.a("top"), sp.l([sp.a("abs"), X.SxNil{}, X.SxNil{}, sp.l([sp.l([sp.a("export"), var, ty])]), sp.l([sp.l([sp.a("evbinds")])]), sp.l([sp.l([sp.a("fun"), sp.l([sp.a("self"), var]), ty, sp.at(fun, 3n), ms, sp.a("hole")])]), sp.a("nospan")])])}
    case None{}:
      None{}

def sp.copy(+rq: Rq, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match rq ix:
    case Rq{n, LoG{k}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      sp.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.df.find(dfs, k), t => sp.fun.of(t)), Nil{}, n, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts})
    case Rq{n, LoL{m, i}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      +top = sp.lc.find(lcs, m, i)
      sp.copy.of(Maybe.bind(&2, X.Sx, X.Sx, top, t => sp.fun.of(t)), sp.strs(sp.at(sp.at(Maybe.default(&2, X.Sx, top, X.SxNil{}), 1n), 1n)), n, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts})
    case Rq{n, LoF{k, fas, fvt, rg}, tys} i:
      None{}
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys} i:
      None{}
    case Rq{n, LoFm{nm, m, j, mtys, fas, fvt, rg}, tys} i:
      None{}
    case Rq{n, LoFlm{nm, m, j, mtys, fas, fvt, gv, rg}, tys} i:
      None{}

# As-patterns ---------------------------------------------------------------

# A clause's x@p is p, its wildcards under it named, and each use of x in
# the clause (its guards, bodies and where-bindings) the term p builds: the
# constructor at the pattern's types applied to its fields, a tuple, a
# list, a literal (Bend matches a parameter and hands out its fields, not
# the whole as well). A clause with an x@p this cannot rebuild (record
# fields, a negative literal, a view) is left as it is.

# a use of an as-pattern's variable: the var (l NAME ID), the term
type Asb is Data:
  Asb{v: X.Sx, e: X.Sx}

# a pattern rebuilt: the pattern, its term, the uses to replace, whether it
# could be (for a sequence of patterns, p and e are the lists)
type Ap is Data:
  Ap{p: X.Sx, e: X.Sx, s: List<&2, Asb>, ok: Bool}

type Pk is Data:
  PkVar{}
  PkWild{}
  PkWrap{}
  PkAs{}
  PkCon{}
  PkTuple{}
  PkList{}
  PkLit{}
  PkNlit{}
  PkSeq{}
  PkBad{}

def sp.as.kind.of(+a: List<&2, U32>, +x: X.Sx) -> Pk:
  +con = Bool.and(sp.is(a, "pcon"), sp.head.is(sp.at(x, 3n), "args"))
  +nlit = Bool.and(sp.is(a, "pnlit"), sp.is(X.tsx.atom.of(sp.at(x, 2n)), "pos"))
  Bool.pick(Pk, sp.is(a, "pvar"), PkVar{}, Bool.pick(Pk, sp.is(a, "pwild"), PkWild{}, Bool.pick(Pk, Bool.or(sp.is(a, "pbang"), sp.is(a, "plazy")), PkWrap{}, Bool.pick(Pk, sp.is(a, "pas"), PkAs{}, Bool.pick(Pk, con, PkCon{}, Bool.pick(Pk, sp.is(a, "ptuple"), PkTuple{}, Bool.pick(Pk, sp.is(a, "plist"), PkList{}, Bool.pick(Pk, sp.is(a, "plit"), PkLit{}, Bool.pick(Pk, nlit, PkNlit{}, PkBad{})))))))))

# what a pattern node is
def sp.as.kind(+x: X.Sx) -> Pk:
  sp.as.kind.of(X.tsx.atom.of(sp.at(x, 0n)), x)

def sp.as.one(p: X.Sx, e: X.Sx) -> Ap:
  Ap{p, e, Nil{}, True{}}

def sp.as.bad(p: X.Sx) -> Ap:
  Ap{p, X.SxNil{}, Nil{}, False{}}

# (pbang P'), (plazy P')
def sp.as.wrap(+h: X.Sx, a: Ap) -> Ap:
  match a:
    case Ap{p, e, s, ok}:
      Ap{X.SxCons{h, X.SxCons{p, X.SxNil{}}}, e, s, ok}

# x@p inside: p's term for x
def sp.as.as(+v: X.Sx, a: Ap) -> Ap:
  match a:
    case Ap{p, +e, s, ok}:
      Ap{p, e, Asb{v, e} <> s, ok}

# a constructor at its types, applied to the fields' terms
def sp.as.tyapps(tys: List<&2, X.Sx>, c: X.Sx) -> X.Sx:
  match tys:
    case Nil{}:
      c
    case t <> r:
      sp.as.tyapps(r, sp.l([sp.a("tyapp"), c, t]))

def sp.as.apps(es: List<&2, X.Sx>, f: X.Sx) -> X.Sx:
  match es:
    case Nil{}:
      f
    case e <> r:
      sp.as.apps(r, sp.l([sp.a("app"), f, e]))

def sp.as.con(+h: X.Sx, +con: X.Sx, +tys: X.Sx, +args: X.Sx, a: Ap) -> Ap:
  match a:
    case Ap{ps, es, s, ok}:
      Ap{sp.l([h, con, tys, X.SxCons{args, ps}]), sp.as.apps(sp.els(es), sp.as.tyapps(sp.els(tys), con)), s, ok}

def sp.as.tuple(+h: X.Sx, a: Ap) -> Ap:
  match a:
    case Ap{ps, es, s, ok}:
      Ap{sp.l([h, ps]), X.SxCons{sp.a("tuple"), es}, s, ok}

def sp.as.list(+h: X.Sx, +t: X.Sx, a: Ap) -> Ap:
  match a:
    case Ap{ps, es, s, ok}:
      Ap{sp.l([h, t, ps]), sp.l([sp.a("list"), t, es]), s, ok}

def sp.as.seq(a: Ap, b: Ap) -> Ap:
  match a b:
    case Ap{p, e, s, ok} Ap{ps, es, s2, ok2}:
      Ap{X.SxCons{p, ps}, X.SxCons{e, es}, List.append(&2, Asb, s, s2), Bool.and(ok, ok2)}

# a wildcard under an x@p, named by its place
def sp.as.wvar(+path: List<&2, U32>) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("as_w"), path)}, sp.a("0")])

# the pattern x (of kind k) rebuilt, the wildcards under it named from path
def sp.as.go(x: X.Sx, k: Pk, +path: List<&2, U32>) -> Ap:
  match x k:
    case X.SxCons{+h, X.SxCons{+bv, X.SxNil{}}} PkVar{}:
      sp.as.one(sp.l([h, bv]), sp.at(bv, 1n))
    case X.SxCons{_, X.SxCons{+t, X.SxNil{}}} PkWild{}:
      +v = sp.as.wvar(path)
      sp.as.one(sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, t])]), v)
    case X.SxCons{+h, X.SxCons{+p, X.SxNil{}}} PkWrap{}:
      sp.as.wrap(h, sp.as.go(p, sp.as.kind(p), path))
    case X.SxCons{_, X.SxCons{+bv, X.SxCons{+p, X.SxNil{}}}} PkAs{}:
      sp.as.as(sp.at(bv, 1n), sp.as.go(p, sp.as.kind(p), path))
    case X.SxCons{+h, X.SxCons{+con, X.SxCons{+tys, X.SxCons{X.SxCons{+args, ps}, X.SxNil{}}}}} PkCon{}:
      sp.as.con(h, con, tys, args, sp.as.go(ps, PkSeq{}, path))
    case X.SxCons{+h, X.SxCons{ps, X.SxNil{}}} PkTuple{}:
      sp.as.tuple(h, sp.as.go(ps, PkSeq{}, path))
    case X.SxCons{+h, X.SxCons{+t, X.SxCons{ps, X.SxNil{}}}} PkList{}:
      sp.as.list(h, t, sp.as.go(ps, PkSeq{}, path))
    case X.SxCons{+h, X.SxCons{+lit, X.SxNil{}}} PkLit{}:
      sp.as.one(sp.l([h, lit]), lit)
    case X.SxCons{+h, X.SxCons{+ol, +r}} PkNlit{}:
      sp.as.one(X.SxCons{h, X.SxCons{ol, r}}, ol)
    case X.SxCons{+p, rest} PkSeq{}:
      sp.as.seq(sp.as.go(p, sp.as.kind(p), sp.cat(path, S.b("a"))), sp.as.go(rest, PkSeq{}, sp.cat(path, S.b("b"))))
    case X.SxNil{} PkSeq{}:
      sp.as.one(X.SxNil{}, X.SxNil{})
    case y _:
      sp.as.bad(y)

# the as-patterns of a clause's patterns rebuilt, the rest kept
def sp.as.find.at(isas: Bool, +x: X.Sx, a: Ap, b: Ap, +path: List<&2, U32>) -> Ap:
  match isas:
    case True{}:
      sp.as.go(x, PkAs{}, path)
    case False{}:
      sp.as.seq(a, b)

def sp.as.isas(+x: X.Sx) -> Bool:
  sp.head.is(x, "pas")

def sp.as.find(x: X.Sx, isas: Bool, +path: List<&2, U32>) -> Ap:
  match x:
    case X.SxCons{+h, +t}:
      sp.as.find.at(isas, X.SxCons{h, t}, sp.as.find(h, sp.as.isas(h), sp.cat(path, S.b("a"))), sp.as.find(t, False{}, sp.cat(path, S.b("b"))), path)
    case y:
      sp.as.one(y, X.SxNil{})

# the term a use of an as-pattern's variable stands for
def sp.as.look(+x: X.Sx, s: List<&2, Asb>) -> Maybe<&2, X.Sx>:
  match s:
    case Nil{}:
      None{}
    case Asb{v, +e} <> t:
      Bool.pick(Maybe<&2, X.Sx>, sp.eq(x, v), Some{e}, sp.as.look(x, t))

# each use of an as-pattern's variable as its term (m: what x is, its caller
# says)
def sp.as.sub(x: X.Sx, m: Maybe<&2, X.Sx>, +s: List<&2, Asb>) -> X.Sx:
  match x m:
    case _ Some{e}:
      e
    case X.SxCons{+h, t} None{}:
      X.SxCons{sp.as.sub(h, sp.as.look(h, s), s), sp.as.sub(t, None{}, s)}
    case y None{}:
      y

def sp.as.clause.of(a: Ap, +ps: X.Sx, +rest: X.Sx) -> X.Sx:
  match a:
    case Ap{ps2, e, +s, ok}:
      +any = Bool.not(Nat.is_eq(List.length(&2, Asb, s), 0n))
      Bool.pick(X.Sx, Bool.and(ok, any), X.SxCons{ps2, sp.as.sub(rest, None{}, s)}, X.SxCons{ps, rest})

# (match PATS GRHSS) with its as-patterns rebuilt
def sp.as.clause(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, X.SxCons{+ps, +rest}}:
      X.SxCons{h, sp.as.clause.of(sp.as.find(ps, False{}, Nil{}), ps, rest)}
    case y:
      y

def sp.p8.at(ism: Bool, x: X.Sx) -> X.Sx:
  match ism:
    case True{}:
      sp.as.clause(x)
    case False{}:
      x

# each clause's as-patterns, inner clauses first (ism: x is a clause)
def sp.p8(x: X.Sx, ism: Bool) -> X.Sx:
  match x:
    case X.SxCons{+h, t}:
      sp.p8.at(ism, X.SxCons{sp.p8(h, sp.head.is(h, "match")), sp.p8(t, False{})})
    case y:
      y

# Recursive references as values ---------------------------------------------

# A recursive reference (self X, or X by its global name) that is not called with all its arguments
# (passed to >>=, maybe, fmap, ..., or applied to fewer) is the lambda that
# takes the rest and calls X: \eta_0 .. eta_m -> X a1 .. ak eta_0 .. eta_m,
# their types X's binder's. The survey and the fold take a call of a def's
# own name; a value of it is rec-value.

# a recursive group of local bindings: (rec (fun (l V N) TYPE ..) ..)
def sp.eta.recs(xs: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match xs:
    case X.SxCons{+b, t}:
      +ok = Bool.and(sp.head.is(b, "fun"), sp.head.is(sp.at(b, 1n), "l"))
      sp.eta.recs(t, Bool.pick(List<&2, Asb>, ok, Asb{sp.at(b, 1n), sp.at(b, 2n)} <> acc, acc))
    case _:
      acc

def sp.eta.recs.if(r: Bool, +x: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match r:
    case True{}:
      sp.eta.recs(x, acc)
    case False{}:
      acc

# the binders' types of the recursive defs in x: (fun (self V) TYPE ..)
def sp.eta.fun(+x: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  +ok = Bool.and(sp.head.is(x, "fun"), sp.head.is(sp.at(x, 1n), "self"))
  Bool.pick(List<&2, Asb>, ok, Asb{sp.at(sp.at(x, 1n), 1n), sp.at(x, 2n)} <> acc, sp.eta.recs.if(sp.head.is(x, "rec"), x, acc))

def sp.eta.tys(x: X.Sx, acc: List<&2, Asb>) -> List<&2, Asb>:
  match x:
    case X.SxCons{+h, +t}:
      sp.eta.tys(t, sp.eta.tys(h, sp.eta.fun(X.SxCons{h, t}, acc)))
    case _:
      acc

# a type under its foralls and its context: (tforall V T), (tctx C T)
def sp.eta.strip(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+v, X.SxCons{+r, X.SxNil{}}}}:
      Bool.pick(X.Sx, Bool.or(sp.is(a, "tforall"), sp.is(a, "tctx")), sp.eta.strip(r), X.SxCons{X.SxAtom{a}, X.SxCons{v, X.SxCons{r, X.SxNil{}}}})
    case y:
      y

# a function type's parameters' types
def sp.eta.params(t: X.Sx) -> List<&2, X.Sx>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{r, X.SxNil{}}}}:
      +rest = sp.eta.params(r)
      Bool.pick(List<&2, X.Sx>, sp.is(a, "tfun"), p <> rest, Nil{})
    case _:
      Nil{}

# the type after n arrows
def sp.eta.res(n: Nat, t: X.Sx) -> X.Sx:
  match n t:
    case Succ{p} X.SxCons{_, X.SxCons{_, X.SxCons{r, X.SxNil{}}}}:
      sp.eta.res(p, r)
    case _ y:
      y

def sp.eta.drop(n: Nat, xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match n xs:
    case Succ{p} _ <> t:
      sp.eta.drop(p, t)
    case _ ys:
      ys

# an application chain's head, and how many arguments it is given
type Eh is Data:
  Eh{h: X.Sx, k: Nat}

# a type or dictionary application: the head's walk goes through it, the
# arguments it counts are app's
def sp.eta.iswrap(+a: List<&2, U32>) -> Bool:
  Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp"))

def sp.eta.head(x: X.Sx, +n: Nat) -> Eh:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +app = sp.is(a, "app")
      +r = sp.eta.head(f, Bool.pick(Nat, app, 1n+n, n))
      Bool.pick(Eh, Bool.or(app, sp.eta.iswrap(a)), r, Eh{X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}}, n})
    case y:
      Eh{y, n}

# what the walk does with a node: keep it, take its parts, eta-expand it
# (an application of a recursive reference to too few, or the reference)
type Ek is Data:
  EkNode{}
  EkApp{}
  EkSkip{}
  EkBinders{}
  EkEtaApp{ps: List<&2, X.Sx>, res: X.Sx}
  EkEtaSelf{ps: List<&2, X.Sx>, res: X.Sx}

def sp.eta.of(m: Maybe<&2, X.Sx>, +k: Nat, +app: Bool) -> Ek:
  match m:
    case Some{t0}:
      +t = sp.eta.strip(t0)
      +ps = sp.eta.params(t)
      +n = List.length(&2, X.Sx, ps)
      +ps2 = sp.eta.drop(k, ps)
      +res = sp.eta.res(n, t)
      Bool.pick(Ek, Nat.is_lt(k, n), Bool.pick(Ek, app, EkEtaApp{ps2, res}, EkEtaSelf{ps2, res}), Bool.pick(Ek, app, EkApp{}, EkNode{}))
    case None{}:
      Bool.pick(Ek, app, EkApp{}, EkNode{})

def sp.eta.eh(e: Eh, +app: Bool, +tys: List<&2, Asb>) -> Ek:
  match e:
    case Eh{+h, +k}:
      +key = Bool.pick(X.Sx, sp.head.is(h, "self"), sp.at(h, 1n), h)
      Bool.pick(Ek, Bool.or(sp.head.is(h, "self"), Bool.or(sp.head.is(h, "g"), sp.head.is(h, "l"))), sp.eta.of(sp.as.look(key, tys), k, app), Bool.pick(Ek, app, EkApp{}, EkNode{}))

# x's mode, its parent's walk says
def sp.eta.mode(+x: X.Sx, +tys: List<&2, Asb>) -> Ek:
  +app = Bool.or(sp.head.is(x, "app"), Bool.or(sp.head.is(x, "tyapp"), sp.head.is(x, "evapp")))
  Bool.pick(Ek, Bool.or(app, Bool.or(sp.head.is(x, "self"), Bool.or(sp.head.is(x, "g"), sp.head.is(x, "l")))), sp.eta.eh(sp.eta.head(x, 0n), app, tys), EkNode{})

# an application's function part (through type and dictionary
# applications): its parts, or a recursive reference kept
def sp.eta.fmode(+f: X.Sx) -> Ek:
  Bool.pick(Ek, Bool.or(sp.head.is(f, "app"), Bool.or(sp.head.is(f, "tyapp"), sp.head.is(f, "evapp"))), EkApp{}, Bool.pick(Ek, Bool.or(sp.head.is(f, "self"), Bool.or(sp.head.is(f, "g"), sp.head.is(f, "l"))), EkSkip{}, EkNode{}))

def sp.eta.tmode(+h: X.Sx) -> Ek:
  +a = X.tsx.atom.of(h)
  Bool.pick(Ek, Bool.or(sp.is(a, "fun"), sp.is(a, "export")), EkBinders{}, EkNode{})

def sp.eta.var(+i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("eta_"), S.b(Nat.show(i)))}, sp.a("0")])

def sp.eta.pats(ps: List<&2, X.Sx>, +i: Nat) -> List<&2, X.Sx>:
  match ps:
    case Nil{}:
      Nil{}
    case t <> r:
      sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.eta.var(i), t])]) <> sp.eta.pats(r, 1n+i)

def sp.eta.call(n: Nat, +i: Nat, f: X.Sx) -> X.Sx:
  match n:
    case Zero{}:
      f
    case Succ{p}:
      sp.eta.call(p, 1n+i, sp.l([sp.a("app"), f, sp.eta.var(i)]))

# \eta_0 .. -> body eta_0 ..
def sp.eta.wrap(+ps: List<&2, X.Sx>, res: X.Sx, body: X.Sx) -> X.Sx:
  +grhss = sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, sp.eta.call(List.length(&2, X.Sx, ps), 0n, body)])]), sp.l([sp.a("binds")])])
  +ms = sp.l([sp.a("matches"), sp.l(ps), res, sp.a("source"), sp.l([sp.l([sp.a("match"), sp.l(sp.eta.pats(ps, 0n)), grhss])])])
  sp.l([sp.a("lam"), sp.a("single"), ms])

# each recursive reference not called with all its arguments, eta-expanded
def sp.p9(x: X.Sx, k: Ek, +tys: List<&2, Asb>) -> X.Sx:
  match x k:
    case y EkSkip{}:
      y
    case X.SxCons{h, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} EkApp{}:
      sp.l([h, sp.p9(f, sp.eta.fmode(f), tys), sp.p9(e, sp.eta.mode(e, tys), tys)])
    case X.SxCons{h, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} EkEtaApp{ps, res}:
      sp.eta.wrap(ps, res, sp.l([h, sp.p9(f, sp.eta.fmode(f), tys), sp.p9(e, sp.eta.mode(e, tys), tys)]))
    case y EkEtaSelf{ps, res}:
      sp.eta.wrap(ps, res, y)
    case X.SxCons{v, t} EkBinders{}:
      X.SxCons{v, sp.p9(t, EkNode{}, tys)}
    case X.SxCons{+h, t} _:
      X.SxCons{sp.p9(h, sp.eta.mode(h, tys), tys), sp.p9(t, sp.eta.tmode(h), tys)}
    case y _:
      y

def sp.rw.p9(r: Rw) -> Rw:
  match r:
    case Rw{+x, q}:
      Rw{sp.p9(x, EkNode{}, sp.eta.tys(x, Nil{})), q}

# Type arguments normal (synonyms expanded, families applied): the survey
# and the fold read a method's instance off its type argument, so cata at
# telomare's Term3 is cata at Cofree Term3F LocTag
def sp.p7.at(ty: Bool, +a: List<&2, U32>, f: X.Sx, t: X.Sx, +ix: Ix) -> X.Sx:
  match ty:
    case True{}:
      sp.l([sp.a("tyapp"), f, sp.norm(t, ix)])
    case False{}:
      X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{t, X.SxNil{}}}}

# a constructor pattern's type arguments too, (pcon CON (TYS...) ARGS)
def sp.p7.pcon(+c: X.Sx, tys: X.Sx, ps: X.Sx, +ix: Ix) -> X.Sx:
  sp.l([sp.a("pcon"), c, sp.l(sp.norms(sp.els(tys), ix)), ps])

def sp.p7(x: X.Sx, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{f, X.SxCons{t, X.SxNil{}}}}:
      sp.p7.at(sp.is(a, "tyapp"), a, sp.p7(f, ix), sp.p7(t, ix), ix)
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+c, X.SxCons{+tys, X.SxCons{+ps, X.SxNil{}}}}}:
      sp.if(X.Sx, sp.is(a, "pcon"), _ => sp.p7.pcon(c, tys, sp.p7(ps, ix), ix), _ => X.SxCons{X.SxAtom{a}, sp.p7(X.SxCons{c, X.SxCons{tys, X.SxCons{ps, X.SxNil{}}}}, ix)})
    case X.SxCons{h, t}:
      X.SxCons{sp.p7(h, ix), sp.p7(t, ix)}
    case y:
      y

def sp.rw.p7(r: Rw, +ix: Ix) -> Rw:
  match r:
    case Rw{x, q}:
      Rw{sp.p7(x, ix), q}

# Known function arguments ----------------------------------------------------

# A call of a package def at a function parameter whose argument is known
# (anything but a local variable: a def, a partial application, a lambda, a
# section) is a call of a copy of the def with the argument in the
# parameter's place, NAME__fHASH. The argument's free locals become the
# copy's first parameters (fv_0, fv_1, .., in the order the arguments name
# them), so a recursive call of the def with the same argument, inside the
# copy, is a call of the copy (the name's hash is of the arguments, their
# types normal: a String the original's lambda says and the copy's List
# Char are one). Bend calls a closure at most once and takes a
# template only closed: a function the def runs again (a parser, under
# many), or one recursion goes through (a grammar's, through many and
# sepBy), is then code in a first-order def, and the fold's fuel and groups
# take the recursion. The call must be at types with no variable (as the
# dictionaries' copies are), the arguments and their free locals' types
# too, and the def's clauses' patterns there variables or wildcards. Inside
# a copy of a def, a call of the def at another argument stays the def's
# (the arguments would grow without end: go (f . (x :))).

type Fa is Data:
  Fa{i: Nat, arg: X.Sx}

# the binders of a tree with their types: (bv V T), (export V T), (fun V T ..)
def sp.fa.binds(x: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +a = X.tsx.atom.of(h)
      +me = Bool.and(Bool.or(sp.is(a, "bv"), Bool.or(sp.is(a, "export"), sp.is(a, "fun"))), sp.head.is(sp.at(n, 1n), "l"))
      sp.fa.binds(t, sp.fa.binds(h, Bool.pick(List<&2, Asb>, me, Asb{sp.at(n, 1n), sp.at(n, 2n)} <> acc, acc)))
    case _:
      acc

def sp.fa.mem(+v: X.Sx, xs: List<&2, X.Sx>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +h <> t:
      Bool.or(sp.eq(h, v), sp.fa.mem(v, t))

def sp.fa.bound(+v: X.Sx, +bs: List<&2, Asb>) -> Bool:
  Maybe.is_some(&2, X.Sx, sp.as.look(v, bs))

# the locals x names and does not bind, after acc's, each once
def sp.fa.frees(x: X.Sx, +bs: List<&2, Asb>, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +isl = sp.is(X.tsx.atom.of(h), "l")
      +isd = S.prefix(sp.sat(n, 1n), S.b("$"))
      +add = Bool.not(Bool.or(Bool.or(isd, sp.fa.bound(n, bs)), sp.fa.mem(n, acc)))
      Bool.pick(List<&2, X.Sx>, isl, Bool.pick(List<&2, X.Sx>, add, List.append(&2, X.Sx, acc, [n]), acc), sp.fa.frees(t, bs, sp.fa.frees(h, bs, acc)))
    case _:
      acc

# (self V) as V, everywhere (V's walk once: Bend runs both of Bool.pick's
# arguments, and a walk in each doubles at each (A V) down a chain)
def sp.fa.unself(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{v, X.SxNil{}}}:
      +u = sp.fa.unself(v)
      Bool.pick(X.Sx, sp.is(a, "self"), u, X.SxCons{X.SxAtom{a}, X.SxCons{u, X.SxNil{}}})
    case X.SxCons{h, t}:
      X.SxCons{sp.fa.unself(h), sp.fa.unself(t)}
    case y:
      y

# (self V) whose V is the copied def's var orig, as orig
def sp.fa.unself.of(x: X.Sx, +orig: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      Bool.pick(X.Sx, Bool.and(sp.is(X.tsx.atom.of(h), "self"), sp.eq(sp.var.of(X.SxCons{h, t}), orig)), orig, X.SxCons{sp.fa.unself.of(h, orig), sp.fa.unself.of(t, orig)})
    case y:
      y

# A local function in a known argument -------------------------------------

# A nonrecursive let's or where's function with parameters (an abs that
# generalises nothing, or a bare fun) is, in a known argument, its lambda,
# applied ones reduced (sp.beta, so that a copy's self-call with the same
# arguments is the copy's): the copy's parameters are its free locals, not
# the function, a closure over them (Resolve's pruneBindings: until (\s ->
# expand s == s) expand seed, expand r = r <> fold (restrictKeys bmap r),
# is a copy of until whose parameter is bmap, a Map), and a copy takes no
# template for it (a recursion through the copy, as freeVarsDeep's through
# foldMap's, is then a group the fold writes with fuel). The lambda's own
# local functions are lambdas too, one round each.

# a fun's lambda: (lam single|case|cases MATCHES)
def sp.fa.lam.of(+fun: X.Sx) -> X.Sx:
  +ms = sp.at(fun, 4n)
  +one = Nat.is_eq(X.tsx.len(sp.at(ms, 4n)), 1n)
  +arg1 = Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 1n)
  sp.l([sp.a("lam"), Bool.pick(X.Sx, one, sp.a("single"), Bool.pick(X.Sx, arg1, sp.a("case"), sp.a("cases"))), ms])

# a local function's value in an argument: its lambda when it takes
# parameters; when it takes none but is a function (patternRefs = cata palg
# where palg ..), its one unguarded right-hand side, under a let of its
# where-bindings when it has any
def sp.fa.lf.val(+fun: X.Sx) -> Maybe<&2, X.Sx>:
  +ms = sp.at(fun, 4n)
  +cls = sp.els(sp.at(ms, 4n))
  +gr = sp.at(sp.first(cls), 2n)
  +gs = sp.els(sp.at(gr, 1n))
  +g0 = sp.first(gs)
  +lb = sp.at(gr, 2n)
  +e = sp.at(g0, 2n)
  +haspar = Bool.not(Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 0n))
  +isfn = sp.head.is(sp.strip(sp.at(fun, 2n)), "tfun")
  +one = Bool.and(Nat.is_eq(List.length(&2, X.Sx, cls), 1n), Bool.and(Nat.is_eq(List.length(&2, X.Sx, gs), 1n), sp.eq(sp.at(g0, 1n), X.SxNil{})))
  +v = Bool.pick(X.Sx, sp.eq(lb, sp.l([sp.a("binds")])), e, sp.l([sp.a("let"), lb, e]))
  Bool.pick(Maybe<&2, X.Sx>, haspar, Some{sp.fa.lam.of(fun)}, Bool.pick(Maybe<&2, X.Sx>, Bool.and(isfn, one), Some{v}, None{}))

def sp.fa.lf.fun.at(+v: X.Sx, m: Maybe<&2, X.Sx>, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match m:
    case Some{+val}:
      Asb{v, val} <> acc
    case None{}:
      acc

# a bind (fun V T SPAN MATCHES) that is a local function, with its value,
# before acc
def sp.fa.lf.fun(+b: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  +isf = Bool.and(sp.head.is(b, "fun"), sp.head.is(sp.var.of(sp.at(b, 1n)), "l"))
  sp.if(List<&2, Asb>, isf, _ => sp.fa.lf.fun.at(sp.var.of(sp.at(b, 1n)), sp.fa.lf.val(b), acc), _ => acc)

def sp.fa.lf.funs(bs: List<&2, X.Sx>, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match bs:
    case Nil{}:
      acc
    case +b <> t:
      sp.fa.lf.funs(t, sp.fa.lf.fun(b, acc))

# a nonrec's bind: an abs generalising nothing (no type variable, no
# dictionary) is its binds
def sp.fa.lf.bind(+b: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  +isabs = Bool.and(sp.head.is(b, "abs"), Bool.and(sp.eq(sp.at(b, 1n), X.SxNil{}), sp.eq(sp.at(b, 2n), X.SxNil{})))
  sp.if(List<&2, Asb>, isabs, _ => sp.fa.lf.funs(sp.els(sp.at(b, 5n)), acc), _ => sp.fa.lf.fun(b, acc))

def sp.fa.lf.binds(bs: List<&2, X.Sx>, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match bs:
    case Nil{}:
      acc
    case +b <> t:
      sp.fa.lf.binds(t, sp.fa.lf.bind(b, acc))

# the tree's local functions in nonrec groups, with their lambdas
def sp.fa.lfuns(x: X.Sx, +acc: List<&2, Asb>) -> List<&2, Asb>:
  match x:
    case X.SxCons{+h, +t}:
      +isn = sp.is(X.tsx.atom.of(h), "nonrec")
      +acc2 = sp.if(List<&2, Asb>, isn, _ => sp.fa.lf.binds(sp.els(t), acc), _ => acc)
      sp.fa.lfuns(t, sp.fa.lfuns(h, acc2))
    case _:
      acc

# x with its local functions' uses as their lambdas, fuel rounds
def sp.fa.inl(fuel: Nat, x: X.Sx, +lf: List<&2, Asb>) -> X.Sx:
  match fuel:
    case 0n:
      x
    case 1n+p:
      +u = sp.fa.unself(x)
      sp.fa.inl(p, sp.as.sub(u, sp.as.look(u, lf), lf), lf)

# whether x holds y
def sp.fa.names(x: X.Sx, +y: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      Bool.or(sp.eq(X.SxCons{h, t}, y), Bool.or(sp.fa.names(h, y), sp.fa.names(t, y)))
    case _:
      False{}

# A lambda of k plain variables applied to k arguments (a copy of foldr at a
# known function: `f x (foldr f z xs)` with f \v r -> ..) is its body with
# them: a variable's argument goes in its place where it is used at most
# once (and not under a lambda, where it would be computed again), or is a
# local, a literal or a constructor, and where no binder of the body has
# the name of a local of it (the fold names locals by their names); else
# it is a let of it, its name its own (NAME_ID).  Bend substitutes such an
# argument at each use ("consumed more than once"), and a strict let is
# computed once; float-in (Fold's fd.fi) takes it into the one branch that
# uses it, as Haskell's laziness would.  An argument of a function's type
# (a parser's, a State's) always goes in its place: it is no Data, and no
# let copies it.
type Bl is Data:
  Bl{ps: List<&2, X.Sx>, e: X.Sx}

type Bs is Data:
  Bs{h: X.Sx, xs: List<&2, X.Sx>}

def sp.beta.plain(ps: List<&2, X.Sx>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> t:
      Bool.and(Bool.or(sp.head.is(p, "pvar"), sp.head.is(p, "pwild")), sp.beta.plain(t))

def sp.beta.lamk(+f: X.Sx) -> Maybe<&2, Bl>:
  +cls = sp.els(sp.at(sp.at(f, 2n), 4n))
  +m0 = sp.first(cls)
  +ps = sp.els(sp.at(m0, 1n))
  +gr = sp.at(m0, 2n)
  +gs = sp.els(sp.at(gr, 1n))
  +g0 = sp.first(gs)
  +one = Bool.and(Nat.is_eq(List.length(&2, X.Sx, cls), 1n), Nat.is_eq(List.length(&2, X.Sx, gs), 1n))
  +ok = Bool.and(Bool.and(sp.head.is(f, "lam"), sp.is(X.tsx.atom.of(sp.at(f, 1n)), "single")), Bool.and(Bool.and(one, sp.beta.plain(ps)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")])))))
  Bool.pick(Maybe<&2, Bl>, ok, Some{Bl{ps, sp.at(g0, 2n)}}, None{})

# an application's function part (under wrappers) and arguments
def sp.beta.spine(x: X.Sx, +acc: List<&2, X.Sx>) -> Bs:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +ex = sp.is(a, "expanded")
      sp.if(Bs, sp.is(a, "app"), _ => sp.beta.spine(f, e <> acc), _ => sp.if(Bs, ex, _ => sp.beta.spine(e, acc), _ => Bs{X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}}, acc}))
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+e, X.SxNil{}}}:
      sp.if(Bs, sp.is(a, "cast"), _ => sp.beta.spine(e, acc), _ => Bs{X.SxCons{X.SxAtom{a}, X.SxCons{e, X.SxNil{}}}, acc})
    case u:
      Bs{u, acc}

# whether a value of the type is Bend's Data: a type's, not a function, nor
# a monad's action or a parser (functions in Bend), nor a type variable
def sp.beta.data(+t: X.Sx, +sys: List<&2, Sy>) -> Bool:
  +h = sp.pc.unsyn(4n, t, sys)
  +m = sp.sat(h, 1n)
  Bool.and(sp.head.is(h, "tc"), Bool.not(Bool.or(S.prefix(m, S.b("Control.Monad")), Bool.or(S.prefix(m, S.b("Text.Megaparsec")), sp.is(sp.tckey(h), "GHC.Types.IO")))))

# the times v is in x
def sp.beta.occ(x: X.Sx, +v: X.Sx) -> Nat:
  match x:
    case X.SxCons{+h, +t}:
      sp.if(Nat, sp.eq(X.SxCons{h, t}, v), _ => 1n, _ => Nat.add(sp.beta.occ(h, v), sp.beta.occ(t, v)))
    case _:
      0n

# whether v is under a lambda or a local binding of x
def sp.beta.inlam(x: X.Sx, +v: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      +a = X.tsx.atom.of(h)
      sp.if(Bool, Bool.or(sp.is(a, "lam"), sp.is(a, "fun")), _ => sp.fa.names(t, v), _ => Bool.or(sp.beta.inlam(h, v), sp.beta.inlam(t, v)))
    case _:
      False{}

# an argument that may be written at each use
def sp.beta.simple(+a0: X.Sx) -> Bool:
  +a = sp.pc.strip(a0)
  +h = sp.spine.head(a)
  Bool.or(sp.head.is(a, "l"), Bool.or(Bool.or(sp.head.is(a, "olit"), sp.head.is(a, "char")), Bool.and(Bool.and(sp.head.is(h, "g"), sp.is(X.tsx.atom.of(sp.at(h, 3n)), "con")), Bool.not(sp.head.is(a, "app")))))

def sp.beta.names(bs: List<&2, Asb>) -> List<&2, List<&2, U32>>:
  match bs:
    case Asb{+v, ty} <> t:
      sp.sat(v, 1n) <> sp.beta.names(t)
    case Nil{}:
      Nil{}

def sp.beta.lnames(vs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match vs:
    case +v <> t:
      sp.sat(v, 1n) <> sp.beta.lnames(t)
    case Nil{}:
      Nil{}

def sp.beta.apart(fs: List<&2, X.Sx>, +ns: List<&2, List<&2, U32>>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> t:
      Bool.and(Bool.not(S.mem(sp.sat(f, 1n), ns)), sp.beta.apart(t, ns))

# whether no binder of e has the name of a local of a
def sp.beta.safe(+a: X.Sx, +e: X.Sx) -> Bool:
  sp.beta.apart(sp.fa.frees(a, sp.fa.binds(a, Nil{}), Nil{}), sp.beta.names(sp.fa.binds(e, Nil{})))

# v as NAME_ID
def sp.beta.own(+v: X.Sx) -> X.Sx:
  +i = sp.at(v, 2n)
  sp.l([sp.a("l"), X.SxStr{List.concat(&2, U32, [sp.sat(v, 1n), S.b("_"), X.tsx.atom.of(i)])}, i])

# what a parameter becomes: nothing (_, or unused), the term t at each use,
# or a let of t
type Ba is Data:
  BaNone{}
  BaSub{v: X.Sx, t: X.Sx}
  BaLet{v: X.Sx, ty: X.Sx, t: X.Sx}

def sp.beta.var(data: Bool, +v: X.Sx, +ty: X.Sx, +a: X.Sx, +e: X.Sx) -> Maybe<&2, Ba>:
  match data:
    case True{}:
      +n = sp.beta.occ(e, v)
      +in = Bool.and(sp.beta.safe(a, e), Bool.or(sp.beta.simple(a), Bool.and(Nat.is_eq(n, 1n), Bool.not(sp.beta.inlam(e, v)))))
      Some{Bool.pick(Ba, Nat.is_eq(n, 0n), BaNone{}, Bool.pick(Ba, in, BaSub{v, a}, BaLet{v, ty, a}))}
    case False{}:
      Bool.pick(Maybe<&2, Ba>, sp.beta.safe(a, e), Some{BaSub{v, a}}, None{})

def sp.beta.one(+p: X.Sx, +a: X.Sx, +e: X.Sx, +sys: List<&2, Sy>) -> Maybe<&2, Ba>:
  +bv = sp.at(p, 1n)
  sp.if(Maybe<&2, Ba>, sp.head.is(p, "pvar"), _ => sp.beta.var(sp.beta.data(sp.at(bv, 2n), sys), sp.at(bv, 1n), sp.at(bv, 2n), a, e), _ => Some{BaNone{}})

def sp.beta.acts.put(m: Maybe<&2, Ba>, r: Maybe<&2, List<&2, Ba>>) -> Maybe<&2, List<&2, Ba>>:
  match m r:
    case Some{b} Some{bs}:
      Some{b <> bs}
    case _ _:
      None{}

def sp.beta.acts(ps: List<&2, X.Sx>, xs: List<&2, X.Sx>, +e: X.Sx, +sys: List<&2, Sy>) -> Maybe<&2, List<&2, Ba>>:
  match ps xs:
    case Nil{} Nil{}:
      Some{Nil{}}
    case +p <> t +a <> u:
      sp.beta.acts.put(sp.beta.one(p, a, e, sys), sp.beta.acts(t, u, e, sys))
    case _ _:
      None{}

def sp.beta.look(bs: List<&2, Ba>, +v: X.Sx) -> Maybe<&2, X.Sx>:
  match bs:
    case BaSub{w, t} <> r:
      Bool.pick(Maybe<&2, X.Sx>, sp.eq(w, v), Some{t}, sp.beta.look(r, v))
    case BaLet{+w, ty, t} <> r:
      Bool.pick(Maybe<&2, X.Sx>, sp.eq(w, v), Some{sp.beta.own(w)}, sp.beta.look(r, v))
    case _ <> r:
      sp.beta.look(r, v)
    case Nil{}:
      None{}

# e with every parameter's term in its place, all at once (an argument may
# hold the same lambda, its binders the same locals)
def sp.beta.put(x: X.Sx, +bs: List<&2, Ba>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      +m = Bool.pick(Maybe<&2, X.Sx>, sp.is(a, "l"), sp.beta.look(bs, X.SxCons{X.SxAtom{a}, t}), None{})
      sp.if(X.Sx, Maybe.is_some(&2, X.Sx, m), _ => sp.or(m, X.SxNil{}), _ => X.SxCons{X.SxAtom{a}, sp.beta.put(t, bs)})
    case X.SxCons{h, t}:
      X.SxCons{sp.beta.put(h, bs), sp.beta.put(t, bs)}
    case y:
      y

def sp.beta.let(+v: X.Sx, +ty: X.Sx, +a: X.Sx, +e: X.Sx) -> X.Sx:
  +grhss = {sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, a])]), sp.l([sp.a("binds")])]) : X.Sx}
  +ms = {sp.l([sp.a("matches"), X.SxNil{}, ty, sp.a("source"), sp.l([sp.l([sp.a("match"), X.SxNil{}, grhss])])]) : X.Sx}
  sp.l([sp.a("let"), sp.l([sp.a("binds"), sp.l([sp.a("nonrec"), sp.l([sp.a("fun"), sp.beta.own(v), ty, sp.a("nospan"), ms])])]), e])

def sp.beta.lets(bs: List<&2, Ba>, e: X.Sx) -> X.Sx:
  match bs:
    case BaLet{v, ty, t} <> r:
      sp.beta.let(v, ty, t, sp.beta.lets(r, e))
    case _ <> r:
      sp.beta.lets(r, e)
    case Nil{}:
      e

def sp.beta.done(m: Maybe<&2, List<&2, Ba>>, e: X.Sx, y: X.Sx) -> X.Sx:
  match m:
    case Some{+bs}:
      sp.beta.lets(bs, sp.beta.put(e, bs))
    case None{}:
      y

def sp.beta.k.of(m: Maybe<&2, Bl>, xs: List<&2, X.Sx>, +y: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  match m:
    case Some{Bl{ps, +e}}:
      sp.beta.done(sp.beta.acts(ps, xs, e, sys), e, y)
    case None{}:
      y

def sp.beta.k.at(s: Bs, +y: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  match s:
    case Bs{h, xs}:
      sp.beta.k.of(sp.beta.lamk(h), xs, y, sys)

# bottom up: (app F A), its parts done
def sp.beta(x: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +f2 = sp.beta(f, sys)
      +e2 = sp.beta(e, sys)
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}} : X.Sx}
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.beta.k.at(sp.beta.spine(y, Nil{}), y, sys), _ => y)
    case X.SxCons{h, t}:
      X.SxCons{sp.beta(h, sys), sp.beta(t, sys)}
    case y:
      y

# Ifs and lets out of arguments ---------------------------------------------------

# An if or a let that is an application's argument or function part goes
# out over it: f (if c then a else b) is if c then f a else f b, and f (let
# ds in e) is let ds in f e (the values are the same; a local of ds named
# as one of f's is renamed NAME_ID, sp.ifl.fresh: GHC numbers the locals
# apart, and the fold reads their names). The fold writes an if where its
# type is known, a body's or a branch's (an argument's is
# fold:if-in-argument), and a let there too (fold:let-in-argument). Not out
# over && and ||, lazy in their second argument; not out of a lambda or a
# case. Out of a tuple's element too (sp.ifl.tup). A module alone is read
# through it too (Survey's sv.read).
# Bend sees no subterm shrink here, so the depth is fuel (32).

# the names of xs's free locals
def sp.ifl.names(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      List.append(&2, List<&2, U32>, sp.beta.lnames(sp.fa.frees(x, sp.fa.binds(x, Nil{}), Nil{})), sp.ifl.names(t))

def sp.ifl.ren(bs: List<&2, Asb>, +ns: List<&2, List<&2, U32>>, x: X.Sx) -> X.Sx:
  match bs:
    case Asb{+v, ty} <> t:
      +y = x
      sp.ifl.ren(t, ns, sp.if(X.Sx, S.mem(sp.sat(v, 1n), ns), _ => sp.beta.sub(y, v, sp.beta.own(v)), _ => y))
    case Nil{}:
      x

# (let DS E) with the locals of DS named as a local of os renamed
def sp.ifl.fresh(+le: X.Sx, +os: List<&2, X.Sx>) -> X.Sx:
  sp.ifl.ren(sp.fa.binds(sp.at(le, 1n), Nil{}), sp.ifl.names(os), le)

def sp.ifl.lazy(+f: X.Sx) -> Bool:
  +h = sp.pc.strip(sp.spine.head(sp.pc.strip(f)))
  +k = sp.sat(h, 2n)
  Bool.and(sp.head.is(h, "g"), Bool.or(sp.is(k, "&&"), sp.is(k, "||")))

def sp.ifl.is(+x: X.Sx, s: String, n: Nat) -> Bool:
  Bool.and(sp.head.is(x, s), Nat.is_eq(X.tsx.len(x), n))

# (let DS E) with k's of E in its place
def sp.ifl.over(+le: X.Sx, k: X.Sx -> X.Sx) -> X.Sx:
  sp.l([sp.a("let"), sp.at(le, 1n), k(sp.at(le, 2n))])

# whether a let binds functions alone (a list function's recursion,
# sp.hf's): nothing is run where it stands, so it goes out over && and ||
# too
def sp.ifl.fnlet.bs(bs: List<&2, X.Sx>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> t:
      Bool.and(Bool.and(sp.head.is(b, "fun"), Nat.is_gt(X.tsx.len(sp.at(sp.at(b, 4n), 1n)), 0n)), sp.ifl.fnlet.bs(t))

def sp.ifl.fnlet.gs(gs: List<&2, X.Sx>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> t:
      Bool.and(sp.ifl.fnlet.bs(sp.dropn(sp.els(g), 1n)), sp.ifl.fnlet.gs(t))

def sp.ifl.fnlet(+le: X.Sx) -> Bool:
  sp.ifl.fnlet.gs(sp.dropn(sp.els(sp.at(le, 1n)), 1n))

# (if C A B), C a let: the let outside (C runs first anyway)
def sp.ifl.cond(+x: X.Sx) -> X.Sx:
  +c = sp.pc.strip(sp.at(x, 1n))
  sp.if(X.Sx, Bool.and(sp.ifl.is(x, "if", 4n), sp.ifl.is(c, "let", 3n)), _ => sp.ifl.over(sp.ifl.fresh(c, [sp.at(x, 2n), sp.at(x, 3n)]), k => sp.l([sp.a("if"), k, sp.at(x, 2n), sp.at(x, 3n)])), _ => x)

def sp.ifl.app(fuel: Nat, +a: List<&2, U32>, +f: X.Sx, +e: X.Sx) -> X.Sx:
  match fuel:
    case 0n:
      sp.l([X.SxAtom{a}, f, e])
    case 1n++p:
      +sf = sp.pc.strip(f)
      +se = sp.pc.strip(e)
      +lz = sp.ifl.lazy(f)
      sp.if(X.Sx, Bool.and(Bool.not(lz), sp.ifl.is(se, "if", 4n)), _ => sp.l([sp.a("if"), sp.at(se, 1n), sp.ifl.app(p, a, f, sp.at(se, 2n)), sp.ifl.app(p, a, f, sp.at(se, 3n))]), _ => sp.if(X.Sx, sp.ifl.is(sf, "if", 4n), _ => sp.l([sp.a("if"), sp.at(sf, 1n), sp.ifl.app(p, a, sp.at(sf, 2n), e), sp.ifl.app(p, a, sp.at(sf, 3n), e)]), _ => sp.if(X.Sx, Bool.and(sp.ifl.is(se, "let", 3n), Bool.or(Bool.not(lz), sp.ifl.fnlet(se))), _ => sp.ifl.over(sp.ifl.fresh(se, [f]), le => sp.ifl.app(p, a, f, le)), _ => sp.if(X.Sx, sp.ifl.is(sf, "let", 3n), _ => sp.ifl.over(sp.ifl.fresh(sf, [e]), lf => sp.ifl.app(p, a, lf, e)), _ => sp.l([X.SxAtom{a}, f, e])))))

# a tuple's elements (pre done, xs to go): the first let or if among them
# goes out over the tuple, (.., let ds in e, ..) as let ds in (.., e, ..),
# (.., if c then a else b, ..) as if c then (.., a, ..) else (.., b, ..);
# Bend builds a tuple's elements when it builds the tuple, so this is the
# same (depth 8: an if doubles the rest)
def sp.ifl.tup(fuel: Nat, +pre: List<&2, X.Sx>, xs: List<&2, X.Sx>) -> X.Sx:
  match fuel xs:
    case 0n _:
      sp.l(sp.a("tuple") <> List.append(&2, X.Sx, pre, xs))
    case 1n+p Nil{}:
      sp.l(sp.a("tuple") <> pre)
    case 1n+(+p) +e <> +t:
      +se = sp.pc.strip(e)
      sp.if(X.Sx, sp.ifl.is(se, "let", 3n), _ => sp.ifl.over(sp.ifl.fresh(se, List.append(&2, X.Sx, pre, t)), le => sp.ifl.tup(p, Nil{}, List.append(&2, X.Sx, pre, le <> t))), _ => sp.if(X.Sx, sp.ifl.is(se, "if", 4n), _ => sp.l([sp.a("if"), sp.at(se, 1n), sp.ifl.tup(p, Nil{}, List.append(&2, X.Sx, pre, sp.at(se, 2n) <> t)), sp.ifl.tup(p, Nil{}, List.append(&2, X.Sx, pre, sp.at(se, 3n) <> t))]), _ => sp.ifl.tup(p, List.append(&2, X.Sx, pre, [e]), t)))

# bottom up: (app F A) and (tuple E..), their parts done
def sp.ifl(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +f2 = sp.ifl(f)
      +e2 = sp.ifl(e)
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.ifl.app(32n, a, f2, e2), _ => sp.if(X.Sx, sp.is(a, "tuple"), _ => sp.ifl.tup(8n, Nil{}, [f2, e2]), _ => X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}}))
    case X.SxCons{X.SxAtom{+a}, t}:
      +t2 = sp.ifl(t)
      sp.if(X.Sx, sp.is(a, "tuple"), _ => sp.ifl.tup(8n, Nil{}, sp.els(t2)), _ => sp.ifl.cond(X.SxCons{X.SxAtom{a}, t2}))
    case X.SxCons{h, t}:
      X.SxCons{sp.ifl(h), sp.ifl(t)}
    case y:
      y

# what is in scope at a recursive local's group: the variables of the
# patterns around it, with their types. A copy put in the group (LoFl) sees
# them as the group's members do, so they are no parameters of it: a
# function the def takes (transformNoDefer's f, in its c') then stays one
# template of the group, not an argument each member hands the next.
type Og is Data:
  Og{v: X.Sx, vs: List<&2, Asb>}

# a top's local functions: all of them, those that name a local or the def
# (meg, its var), and the def
type Lf is Data:
  Lf{all: List<&2, Asb>, need: List<&2, Asb>, meg: X.Sx, rl: List<&2, X.Sx>, ol: List<&2, Og>, kn: List<&2, Rq>, rg: List<&2, X.Sx>}

# the recursive locals an Lf knows (sp.fl.recs)
def sp.lf.rl(lf: Lf) -> List<&2, X.Sx>:
  match lf:
    case Lf{all, need, meg, rl, ol, kn, rg}:
      rl

def sp.lf.ol(lf: Lf) -> List<&2, Og>:
  match lf:
    case Lf{all, need, meg, rl, ol, kn, rg}:
      ol

# a name under its (self ..) wrappers
def sp.lg.unself(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+y, X.SxNil{}}}:
      sp.if(X.Sx, sp.is(a, "self"), _ => sp.lg.unself(y), _ => X.SxCons{X.SxAtom{a}, X.SxCons{y, X.SxNil{}}})
    case y:
      y

# a member's name, its parameters' count
def sp.lg.key(+f: X.Sx) -> X.Sx:
  sp.lg.unself(sp.at(f, 1n))

# (f . g) x as f (g x), a chain f . g . h x as f (g (h x)) (8 deep at most;
# the parts under their (expanded ..) and (cast ..) wrappers)
def sp.lg.dot(n: Nat, +y: X.Sx) -> X.Sx:
  match n:
    case 0n:
      y
    case 1n+k:
      +f1 = sp.pc.strip(sp.at(y, 1n))
      +f2 = sp.pc.strip(sp.at(f1, 1n))
      +c = Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(f1, "app")), Bool.and(sp.head.is(f2, "app"), sp.is(sp.gkey(sp.vhead(sp.at(f2, 1n))), "GHC.Internal.Base..")))
      sp.if(X.Sx, c, _ => sp.l([sp.a("app"), sp.at(f2, 2n), sp.lg.dot(k, sp.l([sp.a("app"), sp.at(f1, 2n), sp.at(y, 2n)]))]), _ => y)

# A function whose right-hand sides are compositions (resolveItems modules
# stack = fmap concat . traverse resolveItem) takes its argument, the
# composition read as calls (fmap concat (traverse resolveItem x)): the
# list's and the monad's functions then have all their arguments, and a
# recursion through them is a call. Every fun, the top's and the locals';
# each right-hand side a call, a name or a lambda, one a composition.
def sp.lec.comp(+e: X.Sx) -> Bool:
  +y = sp.pc.strip(e)
  +f = sp.pc.strip(sp.at(y, 1n))
  Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(f, "app")), sp.is(sp.gkey(sp.vhead(sp.at(f, 1n))), "GHC.Internal.Base.."))

def sp.lec.ok(+e: X.Sx) -> Bool:
  +y = sp.pc.strip(e)
  Bool.or(Bool.or(sp.head.is(y, "app"), Bool.or(sp.head.is(y, "g"), sp.head.is(y, "l"))), Bool.or(sp.head.is(y, "tyapp"), sp.head.is(y, "evapp")))

# the right-hand sides of a clause's guards
def sp.lec.rhs(gs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      sp.at(g, 2n) <> sp.lec.rhs(t)

def sp.lec.rhss(ms: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> t:
      List.append(&2, X.Sx, sp.lec.rhs(sp.els(sp.at(sp.at(m, 2n), 1n))), sp.lec.rhss(t))

def sp.lec.any(es: List<&2, X.Sx>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(sp.lec.comp(e), sp.lec.any(t))

def sp.lec.all(es: List<&2, X.Sx>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(sp.lec.ok(e), sp.lec.all(t))

def sp.lec.guards(gs: List<&2, X.Sx>, +v: X.Sx) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case +g <> t:
      sp.l([sp.a("grhs"), sp.at(g, 1n), sp.lg.dot(8n, sp.l([sp.a("app"), sp.at(g, 2n), v]))]) <> sp.lec.guards(t, v)

def sp.lec.clauses(ms: List<&2, X.Sx>, +v: X.Sx, +ty: X.Sx) -> List<&2, X.Sx>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> t:
      +gr = sp.at(m, 2n)
      +ps = sp.l(List.append(&2, X.Sx, sp.els(sp.at(m, 1n)), [sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, ty])])]))
      sp.l([sp.a("match"), ps, sp.l([sp.a("grhss"), sp.l(sp.lec.guards(sp.els(sp.at(gr, 1n)), v)), sp.at(gr, 2n)])]) <> sp.lec.clauses(t, v, ty)

# the parameter, named after the function (its name's letters and digits)
def sp.lec.alnum(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(Bool.not(U32.is_lt(c, 48)), U32.is_lt(c, 58)), Bool.and(Bool.not(U32.is_lt(c, 65)), U32.is_lt(c, 91))), Bool.or(Bool.and(Bool.not(U32.is_lt(c, 97)), U32.is_lt(c, 123)), U32.is_eq(c, 95)))

def sp.lec.keep(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      +rest = sp.lec.keep(t)
      Bool.pick(List<&2, U32>, sp.lec.alnum(c), c <> rest, rest)

def sp.lec.v(+f: X.Sx) -> X.Sx:
  +k = sp.lg.key(f)
  +n = Bool.pick(List<&2, U32>, sp.head.is(k, "g"), sp.sat(k, 2n), sp.sat(k, 1n))
  sp.l([sp.a("l"), X.SxStr{List.concat(&2, U32, [S.b("c_"), sp.lec.keep(n), S.b("_x")])}, sp.a("0")])

def sp.lec.fun(+f: X.Sx) -> X.Sx:
  +ms = sp.at(f, 4n)
  +ty = sp.at(ms, 2n)
  +cs = sp.els(sp.at(ms, 4n))
  +es = sp.lec.rhss(cs)
  +v = sp.lec.v(f)
  +ms2 = sp.l([sp.a("matches"), sp.l(List.append(&2, X.Sx, sp.els(sp.at(ms, 1n)), [sp.at(ty, 1n)])), sp.at(ty, 2n), sp.at(ms, 3n), sp.l(sp.lec.clauses(cs, v, sp.at(ty, 1n)))])
  sp.if(X.Sx, Bool.and(Bool.and(sp.head.is(f, "fun"), sp.head.is(ty, "tfun")), Bool.and(sp.lec.any(es), sp.lec.all(es))), _ => sp.l([sp.at(f, 0n), sp.at(f, 1n), sp.at(f, 2n), sp.at(f, 3n), ms2, sp.at(f, 5n)]), _ => f)

# a local function whose one right-hand side is a lambda (resolveItem =
# \case .., relabel base = \case ..: variable patterns, no guard, no where)
# has the lambda's clauses as its own
def sp.lec.vars(ps: List<&2, X.Sx>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(sp.head.is(p, "pvar"), sp.lec.vars(t))

def sp.lec.pre(ms: List<&2, X.Sx>, +ps: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> t:
      sp.l([sp.a("match"), sp.l(List.append(&2, X.Sx, ps, sp.els(sp.at(m, 1n)))), sp.at(m, 2n)]) <> sp.lec.pre(t, ps)

def sp.lec.lam(+f: X.Sx) -> X.Sx:
  +ms = sp.at(f, 4n)
  +cs = sp.els(sp.at(ms, 4n))
  +m0 = sp.first(cs)
  +ps = sp.els(sp.at(m0, 1n))
  +gr = sp.at(m0, 2n)
  +g0 = sp.first(sp.els(sp.at(gr, 1n)))
  +e = sp.pc.strip(sp.at(g0, 2n))
  +lm = sp.at(e, 2n)
  +one = Bool.and(Bool.and(Nat.is_eq(List.length(&2, X.Sx, cs), 1n), Nat.is_eq(X.tsx.len(sp.at(gr, 1n)), 1n)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")]))))
  +loc = Bool.and(sp.head.is(f, "fun"), sp.head.is(sp.lg.key(f), "l"))
  +ok = Bool.and(Bool.and(loc, one), Bool.and(Bool.and(sp.head.is(e, "lam"), sp.head.is(lm, "matches")), sp.lec.vars(ps)))
  +ms2 = sp.l([sp.a("matches"), sp.l(List.append(&2, X.Sx, sp.els(sp.at(ms, 1n)), sp.els(sp.at(lm, 1n)))), sp.at(lm, 2n), sp.at(lm, 3n), sp.l(sp.lec.pre(sp.els(sp.at(lm, 4n)), ps))])
  sp.if(X.Sx, ok, _ => sp.l([sp.at(f, 0n), sp.at(f, 1n), sp.at(f, 2n), sp.at(f, 3n), ms2, sp.at(f, 5n)]), _ => f)

# (f . g) x, and (f . g) $ x, is f (g x): the chain read as calls
def sp.lec.app(+x: X.Sx) -> X.Sx:
  +f = sp.pc.strip(sp.at(x, 1n))
  +d = Bool.and(sp.head.is(f, "app"), sp.is(sp.gkey(sp.vhead(sp.pc.strip(sp.at(f, 1n)))), "GHC.Internal.Base.$"))
  +g = sp.if(X.Sx, d, _ => sp.at(f, 2n), _ => f)
  sp.if(X.Sx, sp.lec.comp(g), _ => sp.lg.dot(8n, sp.l([sp.a("app"), g, sp.at(x, 2n)])), _ => x)

# bottom up
def sp.lec(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, t}:
      +n = {X.SxCons{X.SxAtom{a}, sp.lec(t)} : X.Sx}
      sp.if(X.Sx, sp.is(a, "fun"), _ => sp.lec.lam(sp.lec.fun(n)), _ => sp.if(X.Sx, Bool.and(sp.is(a, "app"), Nat.is_eq(X.tsx.len(n), 3n)), _ => sp.lec.app(n), _ => n))
    case X.SxCons{h, t}:
      X.SxCons{sp.lec(h), sp.lec(t)}
    case y:
      y

def sp.fa.hash(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case c <> t:
      sp.fa.hash(t, (h * 33 + c : U32))

# a composition as a value, at a known argument: id . f is f, another the
# lambda over its argument (f . g is \x -> f (g x), x's type the third of
# (.)'s)
def sp.lec.val(fuel: Nat, +e: X.Sx) -> X.Sx:
  match fuel:
    case 0n:
      e
    case 1n+p:
      +y = sp.pc.strip(e)
      +f = sp.pc.strip(sp.at(y, 1n))
      +pp = sp.pc.peel(sp.at(f, 1n), Nil{}, Nil{})
      +ts = sp.pc.tys(pp)
      +ty = Maybe.default(&2, X.Sx, sp.nth(ts, 2n), X.SxNil{})
      +rs = Maybe.default(&2, X.Sx, sp.nth(ts, 1n), X.SxNil{})
      +v = sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("cv_"), S.b(U32.show(sp.fa.hash(X.tsx.show(y), 5381))))}, sp.a("0")])
      +g = sp.pc.strip(sp.at(f, 2n))
      +isid = sp.is(sp.gkey(sp.vhead(g)), "GHC.Internal.Base.id")
      +m = {sp.l([sp.a("match"), sp.l([sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, ty])])]), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, sp.lg.dot(8n, sp.l([sp.a("app"), y, v]))])]), sp.l([sp.a("binds")])])]) : X.Sx}
      +lam = {sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([ty]), rs, sp.a("source"), sp.l([m])])]) : X.Sx}
      sp.if(X.Sx, Bool.not(sp.lec.comp(e)), _ => e, _ => sp.if(X.Sx, isid, _ => sp.lec.val(p, sp.at(y, 2n)), _ => sp.if(X.Sx, Nat.is_eq(List.length(&2, X.Sx, ts), 3n), _ => lam, _ => e)))

# an argument with its applied lambdas reduced and its ifs and lets out of
# arguments, until that changes nothing (three rounds): the copy's own call
# of itself at it, read by the copy's passes, then has the same name
def sp.fa.norm1(x: X.Sx) -> X.Sx:
  sp.ifl(sp.beta(sp.lec(x), Nil{}))

def sp.fa.norm(x: X.Sx) -> X.Sx:
  sp.fa.norm1(sp.fa.norm1(sp.fa.norm1(x)))

# whether a names one of vs
def sp.rg.any(+a: X.Sx, vs: List<&2, X.Sx>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case v <> t:
      Bool.or(sp.fa.names(a, v), sp.rg.any(a, t))

def sp.rg.fas(fas: List<&2, Fa>, +v: X.Sx) -> Bool:
  match fas:
    case Nil{}:
      False{}
    case Fa{i, a} <> t:
      Bool.or(sp.fa.names(a, v), sp.rg.fas(t, v))

# those of vs the arguments name
def sp.rg.named(vs: List<&2, X.Sx>, +fas: List<&2, Fa>) -> List<&2, X.Sx>:
  match vs:
    case Nil{}:
      Nil{}
    case +v <> t:
      +rest = sp.rg.named(t, fas)
      Bool.pick(List<&2, X.Sx>, sp.rg.fas(fas, v), v <> rest, rest)

# the defs a top's recursion may go through: itself, and (a copy's) the defs
# that asked for it and its known argument names (rg): positionsIn's foldMap
# at positionsIn, whose own foldMap at a list is at a lambda that calls it
def sp.lf.megs(lf: Lf) -> List<&2, X.Sx>:
  match lf:
    case Lf{all, need, meg, rl, ol, kn, rg}:
      meg <> rg

def sp.fa.inl.vars(fs: List<&2, Asb>) -> List<&2, X.Sx>:
  match fs:
    case Nil{}:
      Nil{}
    case Asb{v, e} <> t:
      v <> sp.fa.inl.vars(t)

# whether one of xs is not in ys
def sp.fa.inl.rt(xs: List<&2, X.Sx>, +ys: List<&2, X.Sx>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Bool.not(sp.fa.mem(x, ys)), sp.fa.inl.rt(t, ys))

# a tree's nodes, counted to n at most
def sp.fa.count(x: X.Sx, n: Nat) -> Nat:
  match x n:
    case _ 0n:
      0n
    case X.SxCons{h, t} 1n+p:
      sp.fa.count(t, sp.fa.count(h, p))
    case y k:
      k

# a small closed local function (Size's barrier = deferredEE . BarrierF) is
# its lambda in every argument, no template beside it
def sp.fa.small(+e: X.Sx) -> Bool:
  +ms = sp.at(e, 2n)
  +cs = sp.els(sp.at(ms, 4n))
  +gr = sp.at(sp.first(cs), 2n)
  Bool.and(Bool.and(sp.head.is(e, "lam"), Nat.is_eq(List.length(&2, X.Sx, cs), 1n)), Bool.and(sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")])), Nat.is_gt(sp.fa.count(e, 200n), 0n)))

def sp.fa.smalls(fs: List<&2, Asb>, +need: List<&2, Asb>) -> List<&2, Asb>:
  match fs:
    case Nil{}:
      need
    case Asb{+v, +e} <> t:
      +rest = sp.fa.smalls(t, need)
      Bool.pick(List<&2, Asb>, Bool.and(sp.fa.small(e), Bool.not(sp.fa.mem(v, sp.fa.inl.vars(need)))), Asb{v, e} <> rest, rest)

# an argument that names the def (a recursion through the copy) has all
# its local functions as their values, so the copy takes no template; any
# other, those that name a local or the def; and, when the copy then has a
# parameter that is none of them (a run-time local), the closed ones too
# (IC's instantiate: newNode (relabel base k), base a parameter and relabel
# else a template beside it)
def sp.fa.inl.one(+a: X.Sx, +lf: Lf) -> X.Sx:
  match lf:
    case Lf{+all, +need0, +meg, rl, ol, kn, +rg}:
      +need = sp.fa.smalls(all, need0)
      +a2 = sp.fa.unself(sp.fa.inl(List.length(&2, Asb, need), a, need))
      +fr = sp.fa.frees(a2, sp.fa.binds(a2, Nil{}), Nil{})
      +rt = sp.fa.inl.rt(fr, sp.fa.inl.vars(all))
      +fs = Bool.pick(List<&2, Asb>, Bool.or(sp.rg.any(a, meg <> rg), rt), all, need)
      sp.fa.norm(sp.lec.val(8n, sp.fa.inl(List.length(&2, Asb, fs), a, fs)))

def sp.fa.inl.all(xs: List<&2, X.Sx>, +lf: Lf) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> t:
      sp.fa.inl.one(a, lf) <> sp.fa.inl.all(t, lf)

# the free locals of the arguments, in order
def sp.fa.frees.all(fas: List<&2, Fa>, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match fas:
    case Nil{}:
      acc
    case Fa{i, +a} <> t:
      +u = sp.fa.unself(a)
      sp.fa.frees.all(t, sp.fa.frees(u, sp.fa.binds(u, Nil{}), acc))

def sp.fa.tys.cons(a: Maybe<&2, X.Sx>, b: Maybe<&2, List<&2, X.Sx>>) -> Maybe<&2, List<&2, X.Sx>>:
  match a b:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

# the free locals' types, from the binding's binders
def sp.fa.tys(vs: List<&2, X.Sx>, +env: List<&2, Asb>) -> Maybe<&2, List<&2, X.Sx>>:
  match vs:
    case Nil{}:
      Some{Nil{}}
    case +v <> t:
      sp.fa.tys.cons(sp.as.look(v, env), sp.fa.tys(t, env))

def sp.fa.tys.ok(m: Maybe<&2, List<&2, X.Sx>>) -> Bool:
  match m:
    case Some{ts}:
      sp.all.closed(ts)
    case None{}:
      False{}

def sp.fa.tys.get(m: Maybe<&2, List<&2, X.Sx>>) -> List<&2, X.Sx>:
  match m:
    case Some{ts}:
      ts
    case None{}:
      Nil{}

# whether a local is a dictionary ($dOrd ..)
def sp.fa.anydict(vs: List<&2, X.Sx>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case +v <> t:
      Bool.or(S.prefix(sp.sat(v, 1n), S.b("$")), sp.fa.anydict(t))

# the copy's parameter i: (l "fv_i" 0)
def sp.fa.fv(+i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("fv_"), S.b(Nat.show(i)))}, sp.a("0")])

def sp.fa.canon.map(vs: List<&2, X.Sx>, +i: Nat) -> List<&2, Asb>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      Asb{v, sp.fa.fv(i)} <> sp.fa.canon.map(t, 1n+i)

# the arguments with their free locals as the copy's parameters
def sp.fa.canon(fas: List<&2, Fa>, +cm: List<&2, Asb>) -> List<&2, Fa>:
  match fas:
    case Nil{}:
      Nil{}
    case Fa{i, a} <> t:
      +u = sp.fa.unself(a)
      Fa{i, sp.as.sub(u, sp.as.look(u, cm), cm)} <> sp.fa.canon(t, cm)

def sp.fa.key(fas: List<&2, Fa>) -> X.Sx:
  match fas:
    case Nil{}:
      X.SxNil{}
    case Fa{i, a} <> t:
      X.SxCons{sp.l([X.SxAtom{S.b(Nat.show(i))}, a]), sp.fa.key(t)}

# A known argument whose free locals include a recursive local, a member of
# a where's or a let's (rec ..) group, is copied into that group (sp.fl):
# the member's reference is kept, the other free locals are the copy's
# parameters.
# the locals a rec group of x binds (an abs's exports, a bare fun's var),
# after acc's
def sp.fl.recs.es(es: List<&2, X.Sx>, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      acc
    case +e <> t:
      +v = sp.at(e, 1n)
      sp.fl.recs.es(t, Bool.pick(List<&2, X.Sx>, Bool.and(sp.head.is(e, "export"), sp.head.is(v, "l")), v <> acc, acc))

def sp.fl.recs.b(+b: X.Sx, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  +v = sp.var.of(sp.at(b, 1n))
  +isfun = Bool.and(sp.head.is(b, "fun"), sp.head.is(v, "l"))
  sp.if(List<&2, X.Sx>, sp.head.is(b, "abs"), _ => sp.fl.recs.es(sp.els(sp.at(b, 3n)), acc), _ => Bool.pick(List<&2, X.Sx>, isfun, v <> acc, acc))

def sp.fl.recs.bs(bs: List<&2, X.Sx>, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match bs:
    case Nil{}:
      acc
    case +b <> t:
      sp.fl.recs.bs(t, sp.fl.recs.b(b, acc))

def sp.fl.recs(x: X.Sx, +acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      +isr = sp.is(X.tsx.atom.of(h), "rec")
      +acc2 = sp.if(List<&2, X.Sx>, isr, _ => sp.fl.recs.bs(sp.els(t), acc), _ => acc)
      sp.fl.recs(t, sp.fl.recs(h, acc2))
    case _:
      acc

def sp.og.put(vs: List<&2, X.Sx>, +sc: List<&2, Asb>, acc: List<&2, Og>) -> List<&2, Og>:
  match vs:
    case Nil{}:
      acc
    case v <> t:
      Og{v, sc} <> sp.og.put(t, sc, acc)

# the locals a group binds, with their types
def sp.og.exps(es: List<&2, X.Sx>) -> List<&2, Asb>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      +rest = sp.og.exps(t)
      Bool.pick(List<&2, Asb>, Bool.and(sp.head.is(e, "export"), sp.head.is(sp.at(e, 1n), "l")), Asb{sp.at(e, 1n), sp.at(e, 2n)} <> rest, rest)

def sp.og.grp(bs: List<&2, X.Sx>) -> List<&2, Asb>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> t:
      +rest = sp.og.grp(t)
      +v = sp.fa.unself(sp.at(b, 1n))
      sp.if(List<&2, Asb>, sp.head.is(b, "abs"), _ => List.append(&2, Asb, sp.og.exps(sp.els(sp.at(b, 3n))), rest), _ => Bool.pick(List<&2, Asb>, Bool.and(sp.head.is(b, "fun"), sp.head.is(v, "l")), Asb{v, sp.at(b, 2n)} <> rest, rest))

def sp.og.groups(gs: List<&2, X.Sx>) -> List<&2, Asb>:
  match gs:
    case Nil{}:
      Nil{}
    case +g <> t:
      List.append(&2, Asb, sp.og.grp(sp.dropn(sp.els(g), 1n)), sp.og.groups(t))

# (binds G..)'s locals
def sp.og.binds(+b: X.Sx) -> List<&2, Asb>:
  sp.if(List<&2, Asb>, sp.head.is(b, "binds"), _ => sp.og.groups(sp.dropn(sp.els(b), 1n)), _ => Nil{})

# each recursive local of x, its group's scope (sc: x's own): the patterns'
# variables around it, the locals of the lets and wheres around it, and of
# its own let the groups before it (ib: x is a binds' groups)
def sp.og.of(x: X.Sx, +sc: List<&2, Asb>, +acc: List<&2, Og>, +ib: Bool) -> List<&2, Og>:
  match x ib:
    case X.SxCons{+g, +t} True{}:
      sp.og.of(t, List.append(&2, Asb, sp.og.grp(sp.dropn(sp.els(g), 1n)), sc), sp.og.of(g, sc, acc, False{}), True{})
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, +t}} False{}:
      +isb = sp.is(a, "binds")
      +acc2 = sp.if(List<&2, Og>, sp.is(a, "rec"), _ => sp.og.put(sp.fl.recs.bs(p <> sp.els(t), Nil{}), sc, acc), _ => acc)
      +sp2 = sp.if(List<&2, Asb>, sp.is(a, "grhss"), _ => List.append(&2, Asb, sp.og.binds(sp.at(t, 0n)), sc), _ => sc)
      +st = sp.if(List<&2, Asb>, sp.is(a, "match"), _ => List.append(&2, Asb, sp.fa.binds(p, Nil{}), sc), _ => sp.if(List<&2, Asb>, sp.is(a, "let"), _ => List.append(&2, Asb, sp.og.binds(p), sc), _ => sp.if(List<&2, Asb>, isb, _ => List.append(&2, Asb, sp.og.grp(sp.dropn(sp.els(p), 1n)), sc), _ => sc)))
      sp.og.of(t, st, sp.og.of(p, sp2, acc2, False{}), isb)
    case X.SxCons{h, t} False{}:
      sp.og.of(t, sc, sp.og.of(h, sc, acc, False{}), False{})
    case _ _:
      acc

def sp.og.find(os: List<&2, Og>, +v: X.Sx) -> List<&2, Asb>:
  match os:
    case Nil{}:
      Nil{}
    case Og{+w, vs} <> t:
      Bool.pick(List<&2, Asb>, sp.eq(w, v), vs, sp.og.find(t, v))

# the scopes with a copy's own first, its group's (gv's)
def sp.og.at(+os: List<&2, Og>, +gv: X.Sx) -> List<&2, Og>:
  Og{X.SxNil{}, sp.og.find(os, gv)} <> os

def sp.og.base(os: List<&2, Og>) -> List<&2, Asb>:
  sp.og.find(os, X.SxNil{})

def sp.og.vars(vs: List<&2, Asb>) -> List<&2, X.Sx>:
  match vs:
    case Nil{}:
      Nil{}
    case Asb{v, e} <> t:
      v <> sp.og.vars(t)

# xs without those in ys
def sp.fa.minus(xs: List<&2, X.Sx>, +ys: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      +rest = sp.fa.minus(t, ys)
      Bool.pick(List<&2, X.Sx>, sp.fa.mem(x, ys), rest, x <> rest)

# xs that are in ys
def sp.fa.both(xs: List<&2, X.Sx>, +ys: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      +rest = sp.fa.both(t, ys)
      Bool.pick(List<&2, X.Sx>, sp.fa.mem(x, ys), x <> rest, rest)

# a local copy's local: (l N 0)
def sp.fl.var(+n: List<&2, U32>) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{n}, sp.a("0")])

def sp.fa.isat(fas: List<&2, Fa>, +i: Nat) -> Bool:
  match fas:
    case Nil{}:
      False{}
    case Fa{+j, a} <> t:
      Bool.or(Nat.is_eq(i, j), sp.fa.isat(t, i))

def sp.fa.argat(fas: List<&2, Fa>, +i: Nat) -> X.Sx:
  match fas:
    case Nil{}:
      X.SxNil{}
    case Fa{+j, +a} <> t:
      Bool.pick(X.Sx, Nat.is_eq(i, j), a, sp.fa.argat(t, i))

# xs without the places of fas
def sp.fa.drop.at(xs: List<&2, X.Sx>, +fas: List<&2, Fa>, +i: Nat) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      +rest = sp.fa.drop.at(t, fas, 1n+i)
      Bool.pick(List<&2, X.Sx>, sp.fa.isat(fas, i), rest, h <> rest)

# a function type's parameters' types
def sp.fa.params(t: X.Sx) -> List<&2, X.Sx>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{+r, X.SxNil{}}}}:
      Bool.pick(List<&2, X.Sx>, sp.is(a, "tfun"), p <> sp.fa.params(r), Nil{})
    case _:
      Nil{}

# whether each clause's pattern i is a variable or a wildcard
def sp.fa.pats.ok(cs: List<&2, X.Sx>, +i: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> t:
      +p = sp.or(sp.nth(sp.els(sp.at(c, 1n)), i), X.SxNil{})
      Bool.and(Bool.or(sp.head.is(p, "pvar"), sp.head.is(p, "pwild")), sp.fa.pats.ok(t, i))

# the arguments to put in their parameters' places: a function parameter,
# not a local variable, no type variable in it, a pattern that takes it
def sp.fa.pick(args: List<&2, X.Sx>, ptys: List<&2, X.Sx>, +cls: List<&2, X.Sx>, +i: Nat, +n: Nat, +sys: List<&2, Sy>) -> List<&2, Fa>:
  match args ptys:
    case +a <> at +p <> pt:
      +u = sp.fa.unself(a)
      +ok = Bool.and(Nat.is_lt(i, n), Bool.and(sp.fnp.isfn(p, sys), Bool.and(Bool.not(sp.head.is(u, "l")), Bool.and(Bool.not(sp.has(a, S.b("tv"))), sp.fa.pats.ok(cls, i)))))
      +rest = sp.fa.pick(at, pt, cls, 1n+i, n, sys)
      Bool.pick(List<&2, Fa>, ok, Fa{i, a} <> rest, rest)
    case _ _:
      Nil{}

# whether a call's argument i is one pick may take by its parameter alone:
# among the clauses' first n, a function parameter, each clause's pattern
# there a variable or a wildcard (the argument's own tests wait for its
# local functions' values)
def sp.fa.cand(+p: X.Sx, +cls: List<&2, X.Sx>, +i: Nat, +n: Nat, +sys: List<&2, Sy>) -> Bool:
  Bool.and(Nat.is_lt(i, n), Bool.and(sp.fnp.isfn(p, sys), sp.fa.pats.ok(cls, i)))

# whether any argument is one pick may take
def sp.fa.cands(args: List<&2, X.Sx>, ptys: List<&2, X.Sx>, +cls: List<&2, X.Sx>, +i: Nat, +n: Nat, +sys: List<&2, Sy>) -> Bool:
  match args ptys:
    case a <> at +p <> pt:
      Bool.or(sp.fa.cand(p, cls, i, n, sys), sp.fa.cands(at, pt, cls, 1n+i, n, sys))
    case _ _:
      False{}

# the arguments with their local functions' values (sp.fa.inl.one) where
# pick may take them; any other pick does not take, so it stays as it is
def sp.fa.inl.at(args: List<&2, X.Sx>, ptys: List<&2, X.Sx>, +cls: List<&2, X.Sx>, +i: Nat, +n: Nat, +sys: List<&2, Sy>, +lf: Lf) -> List<&2, X.Sx>:
  match args ptys:
    case +a <> at +p <> pt:
      sp.if(X.Sx, sp.fa.cand(p, cls, i, n, sys), _ => sp.fa.inl.one(a, lf), _ => a) <> sp.fa.inl.at(at, pt, cls, 1n+i, n, sys, lf)
    case rest _:
      rest

# an (app) spine's function part, under its apps
def sp.fa.fn(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      Bool.pick(X.Sx, sp.is(a, "app"), sp.fa.fn(f), X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}})
    case y:
      y

# whether the function part holds a dictionary's application
def sp.fa.hasev(x: X.Sx) -> Bool:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{e, X.SxNil{}}}}:
      Bool.or(sp.is(a, "evapp"), Bool.and(Bool.or(sp.is(a, "app"), sp.is(a, "tyapp")), sp.fa.hasev(f)))
    case _:
      False{}

def sp.fa.apps(xs: List<&2, X.Sx>, f: X.Sx) -> X.Sx:
  match xs:
    case Nil{}:
      f
    case a <> t:
      sp.fa.apps(t, sp.l([sp.a("app"), f, a]))

# a call's decision: the copy's function part (its name applied to the free
# locals), the places of the arguments that go, the copy asked for
type Fd is Data:
  Fd{hd: X.Sx, fas: List<&2, Fa>, q: List<&2, Rq>}

# the decision once pick has the arguments that go (Bend runs a call's
# arguments first: what is only for a copy waits for sp.if)
def sp.fa.at.go(fas0: List<&2, Fa>, +h: X.Sx, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +tys: List<&2, X.Sx>, +tyok: Bool, +rl: List<&2, X.Sx>, +ol: List<&2, Og>, +megs: List<&2, X.Sx>) -> Maybe<&2, Fd>:
  match fas0:
    case Nil{}:
      None{}
    case +f0 <> +ft:
      +fas0 = {f0 <> ft : List<&2, Fa>}
      +fr0 = sp.fa.frees.all(fas0, Nil{})
      +sl = sp.fa.both(fr0, rl)
      +loc = Bool.not(List.is_empty(&2, X.Sx, sl))
      +outs = Bool.pick(List<&2, X.Sx>, loc, sp.og.vars(sp.og.find(ol, sp.or(sp.nth(sl, 0n), X.SxNil{}))), Nil{})
      +frees = sp.fa.minus(sp.fa.minus(fr0, sl), outs)
      +fvt = sp.fa.tys(frees, env)
      +fas = sp.fa.canon(fas0, sp.fa.canon.map(frees, 0n))
      +base = sp.cat(sp.name(sp.sat(h, 2n), tys), S.b("_f"))
      +n = sp.cat(base, S.b(U32.show(sp.fa.hash(X.tsx.show(sp.norm(sp.fa.key(fas), ix)), 5381))))
      +inself = Bool.or(S.eq(me, sp.sat(h, 2n)), Bool.and(S.prefix(me, base), Bool.not(S.eq(me, n))))
      +ok = Bool.and(tyok, Bool.and(Bool.not(List.is_empty(&2, Fa, fas0)), Bool.and(sp.fa.tys.ok(fvt), Bool.not(Bool.or(inself, sp.fa.hasev(sp.fa.fn(x)))))))
      +hd = sp.fa.apps(frees, Bool.pick(X.Sx, loc, sp.l([sp.a("self"), sp.fl.var(n)]), sp.g(cur, n, "var")))
      +rg = sp.rg.named(megs, fas)
      +lo = Bool.pick(Lo, loc, LoFl{sp.gkey(h), fas, sp.fa.tys.get(fvt), sp.or(sp.nth(sl, 0n), X.SxNil{}), rg}, LoF{sp.gkey(h), fas, sp.fa.tys.get(fvt), rg})
      Bool.pick(Maybe<&2, Fd>, ok, Some{Fd{hd, fas, [Rq{n, lo, tys}]}}, None{})

# the decision on a call x of the def fun: its copy's call and the copy
# asked for, or none
def sp.fa.at(m: Maybe<&2, X.Sx>, +h: X.Sx, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf, +otys: Maybe<&2, List<&2, X.Sx>>) -> Maybe<&2, Fd>:
  match m:
    case Some{+fun}:
      +tys = Maybe.default(&2, List<&2, X.Sx>, otys, sp.norms(sp.spine.tys(sp.fa.fn(x), Nil{}), ix))
      +tvs = sp.foralls(sp.at(fun, 2n))
      +tyok = Bool.and(Nat.is_eq(List.length(&2, List<&2, U32>, tvs), List.length(&2, X.Sx, tys)), sp.all.closed(tys))
      +sbs = sp.zip(tvs, tys)
      +ptys = sp.fa.params(sp.subst(sp.strip(sp.at(fun, 2n)), sbs))
      +ms = sp.at(fun, 4n)
      +raw = sp.spine.args(x, Nil{})
      +cls = sp.els(sp.at(ms, 4n))
      +np = X.tsx.len(sp.at(ms, 1n))
      +sys = sp.ix.sys(ix)
      +pre = Bool.and(tyok, Bool.and(sp.fa.cands(raw, ptys, cls, 0n, np, sys), Bool.not(Bool.or(S.eq(me, sp.sat(h, 2n)), sp.fa.hasev(sp.fa.fn(x))))))
      sp.if(Maybe<&2, Fd>, pre, _ => sp.fa.at.go(sp.fa.pick(sp.fa.inl.at(raw, ptys, cls, 0n, np, sys, lf), ptys, cls, 0n, np, sys), h, x, me, cur, ix, env, tys, tyok, sp.lf.rl(lf), sp.lf.ol(lf), sp.lf.megs(lf)), _ => None{})
    case None{}:
      None{}


# A call of a def's dictionary copy (p4 has asked for it in this top, at
# the call's types) is the def's call at the copy's types: a def with a
# class (Base's model's foldMapMonoid, at Foldable t and Monoid m) is
# copied at its known function argument too, its dictionaries' methods
# then at the types (as a dictionary copy's are)
def sp.rq.k(r: Rq) -> List<&2, U32>:
  match r:
    case Rq{n, LoG{k}, tys}:
      k
    case _:
      Nil{}

def sp.rq.tys(r: Rq) -> List<&2, X.Sx>:
  match r:
    case Rq{n, lo, tys}:
      tys

def sp.rq.n(r: Rq) -> List<&2, U32>:
  match r:
    case Rq{n, lo, tys}:
      n

def sp.rq.isg(r: Rq) -> Bool:
  match r:
    case Rq{n, LoG{k}, tys}:
      True{}
    case _:
      False{}

def sp.rq.isl(r: Rq) -> Bool:
  match r:
    case Rq{n, LoL{m, i}, tys}:
      True{}
    case _:
      False{}

# the request of the dictionary copy h calls, if p4 made it
def sp.fa.dq.find(dq: List<&2, Rq>, +h: X.Sx, +cur: List<&2, U32>) -> Maybe<&2, Rq>:
  match dq:
    case Nil{}:
      None{}
    case +r <> t:
      +hit = Bool.and(Bool.or(sp.rq.isg(r), sp.rq.isl(r)), Bool.and(S.eq(sp.rq.n(r), sp.sat(h, 2n)), S.eq(cur, sp.sat(h, 1n))))
      Bool.pick(Maybe<&2, Rq>, hit, Some{r}, sp.fa.dq.find(t, h, cur))

def sp.ix.fns(ix: Ix) -> List<&2, Df>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}:
      fns

# whether an argument names v inside it (a lambda over the def, not the def)
def sp.fa.inside(fas: List<&2, Fa>, +v: X.Sx) -> Bool:
  match fas:
    case Nil{}:
      False{}
    case Fa{i, +a} <> t:
      Bool.or(Bool.and(Bool.not(sp.eq(sp.pc.strip(a), v)), sp.fa.names(a, v)), sp.fa.inside(t, v))

# whether an argument names one of vs inside it
def sp.fa.insides(vs: List<&2, X.Sx>, +fas: List<&2, Fa>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case v <> t:
      Bool.or(sp.fa.inside(fas, v), sp.fa.insides(t, fas))

# a dictionary copy's call is the def's copy's only when its dictionary
# copy would not do: an argument that names a local (the copy then has
# parameters) or the def the call is in, inside a lambda (a template Bend
# takes closed, and a recursive def's fuel is not; the def itself is a
# closed template)
def sp.fa.need(d: Maybe<&2, Fd>, +megs: List<&2, X.Sx>) -> Maybe<&2, Fd>:
  match d:
    case Some{Fd{+hd, +fas, q}}:
      +need = Bool.or(sp.head.is(hd, "app"), sp.fa.insides(megs, fas))
      Bool.pick(Maybe<&2, Fd>, need, Some{Fd{hd, fas, q}}, None{})
    case None{}:
      None{}

# an instance's method's copy at a known function: the copy p4 asked for
# (r), its own copy with the function in it. Only a lambda's, that names a
# local or the def the call is in (sp.fa.need)
def sp.fa.tom.lo(lo: Lo, +r: Rq) -> Maybe<&2, Lo>:
  match lo r:
    case LoF{k, fas, fvt, rg} Rq{nm, LoL{m, i}, mtys}:
      Some{LoFm{nm, m, i, mtys, fas, fvt, rg}}
    case LoFl{k, fas, fvt, gv, rg} Rq{nm, LoL{m, i}, mtys}:
      Some{LoFlm{nm, m, i, mtys, fas, fvt, gv, rg}}
    case _ _:
      None{}

def sp.fa.tom.q(q: List<&2, Rq>, +r: Rq) -> List<&2, Rq>:
  match q:
    case Nil{}:
      Nil{}
    case Rq{n, +lo, tys} <> t:
      Rq{n, Maybe.default(&2, Lo, sp.fa.tom.lo(lo, r), lo), tys} <> sp.fa.tom.q(t, r)

def sp.fa.tom.ok(q: List<&2, Rq>) -> Bool:
  match q:
    case Rq{n, LoF{k, fas, fvt, rg}, tys} <> t:
      True{}
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys} <> t:
      True{}
    case _:
      False{}

def sp.fa.tom(d: Maybe<&2, Fd>, +r: Rq) -> Maybe<&2, Fd>:
  match d:
    case Some{Fd{hd, fas, +q}}:
      Bool.pick(Maybe<&2, Fd>, sp.fa.tom.ok(q), Some{Fd{hd, fas, sp.fa.tom.q(q, r)}}, None{})
    case None{}:
      None{}

# a lambda, or one applied (`traverse (f []) t` with f known), or a
# recursive local (rl), applied or not (`traverse goPattern p`)
def sp.fa.islam(+x: X.Sx, +rl: List<&2, X.Sx>) -> Bool:
  +y = sp.pc.strip(x)
  +h = sp.pc.strip(sp.spine.head(y))
  Bool.or(Bool.or(sp.head.is(y, "lam"), Bool.or(sp.lec.comp(x), Bool.and(sp.head.is(y, "app"), sp.head.is(h, "lam")))), sp.fa.mem(sp.fa.unself(h), rl))

def sp.fa.haslam(xs: List<&2, X.Sx>, +rl: List<&2, X.Sx>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(sp.fa.islam(x, rl), sp.fa.haslam(t, rl))

# sp.fa.need, and a copy in a group (its argument names the group's
# function: as a template it would be a closure over the group's locals)
def sp.fa.ingroup(q: List<&2, Rq>) -> Bool:
  match q:
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys} <> t:
      True{}
    case _:
      False{}

def sp.fa.needm(+d: Maybe<&2, Fd>, +megs: List<&2, X.Sx>) -> Maybe<&2, Fd>:
  match d:
    case Some{Fd{+hd, +fas, +q}}:
      Bool.pick(Maybe<&2, Fd>, sp.fa.ingroup(q), Some{Fd{hd, fas, q}}, sp.fa.need(Some{Fd{hd, fas, q}}, megs))
    case None{}:
      None{}

def sp.fa.meth(+r: Rq, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf) -> Maybe<&2, Fd>:
  +h = sp.g(cur, sp.rq.n(r), "var")
  sp.if(Maybe<&2, Fd>, sp.fa.haslam(sp.spine.args(x, Nil{}), sp.lf.rl(lf)), _ => sp.fa.tom(sp.fa.needm(sp.fa.at(Maybe.bind(&2, X.Sx, X.Sx, sp.copy(r, cur, ix), t => sp.fun.of(t)), h, x, me, cur, ix, env, lf, Some{Nil{}}), sp.lf.megs(lf)), r), _ => None{})

def sp.fa.decide.at(dc: Maybe<&2, Rq>, +top0: Maybe<&2, X.Sx>, +h0: X.Sx, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf) -> Maybe<&2, Fd>:
  match dc:
    case Some{+r}:
      +top = sp.df.find(sp.ix.fns(ix), sp.rq.k(r))
      +h = sp.at(sp.or(sp.nth(sp.exports(Maybe.default(&2, X.Sx, top, X.SxNil{})), 0n), X.SxNil{}), 1n)
      sp.if(Maybe<&2, Fd>, sp.rq.isl(r), _ => sp.fa.meth(r, x, me, cur, ix, env, lf), _ => sp.fa.needm(sp.fa.at(Maybe.bind(&2, X.Sx, X.Sx, top, t => sp.fun.of(t)), h, x, me, cur, ix, env, lf, Some{sp.rq.tys(r)}), sp.lf.megs(lf)))
    case None{}:
      sp.fa.at(Maybe.bind(&2, X.Sx, X.Sx, top0, t => sp.fun.of(t)), h0, x, me, cur, ix, env, lf, None{})

# the request of a copy an argument calls, when its call has a lambda
def sp.fa.kn(+h: X.Sx, +x: X.Sx, +cur: List<&2, U32>, lf: Lf) -> Maybe<&2, Rq>:
  match lf:
    case Lf{all, need, meg, +rl, ol, +kn, rg}:
      sp.if(Maybe<&2, Rq>, sp.fa.haslam(sp.spine.args(x, Nil{}), rl), _ => sp.fa.dq.find(kn, h, cur), _ => None{})

def sp.fa.decide(+x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf, +dq: List<&2, Rq>) -> Maybe<&2, Fd>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, +fns, cts}:
      +h = sp.fa.unself(sp.spine.head(x))
      +isg = sp.head.is(h, "g")
      +top = Bool.pick(Maybe<&2, X.Sx>, isg, sp.df.find(fns, sp.gkey(h)), None{})
      +dc = sp.if(Maybe<&2, Rq>, Bool.and(isg, Bool.not(Maybe.is_some(&2, X.Sx, top))), _ => Maybe.or(&2, Rq, sp.fa.dq.find(dq, h, cur), sp.fa.kn(h, x, cur, lf)), _ => None{})
      sp.fa.decide.at(dc, top, h, x, me, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}, env, lf)

def sp.rw.addq(r: Rw, q: List<&2, Rq>) -> Rw:
  match r:
    case Rw{x, p}:
      Rw{x, sp.rw.cat(p, q)}

# the walk's mode at a node: a node (top: no spine's function part), or a
# copy's call's spine (hd: the copy's function part; i: the place of the
# node's argument, the first argument's 0; fas: the places that go)
type Pm is Data:
  PmNode{top: Bool}
  PmArgs{hd: X.Sx, i: Nat, fas: List<&2, Fa>}

def sp.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def sp.fa.decide.if(isapp: Bool, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf, +dq: List<&2, Rq>) -> Maybe<&2, Fd>:
  match isapp:
    case True{}:
      sp.fa.decide(x, me, cur, ix, env, lf, dq)
    case False{}:
      None{}

# the mode for the function part f of a node (a f e) with k arguments: the
# copy's spine when the node's call is a copy's (f's argument is k - 2's),
# else a node, top unless the node is an application
def sp.fd.mode(d: Maybe<&2, Fd>, +k: Nat, +inner: Bool) -> Pm:
  match d:
    case Some{Fd{hd, fas, q}}:
      PmArgs{hd, sp.pred(sp.pred(k)), fas}
    case None{}:
      PmNode{Bool.not(inner)}

# an application of a copy's call: f's walk alone when e's place goes
def sp.p10.arg(drop: Bool, +a: List<&2, U32>, fw: Rw, ew: Rw) -> Rw:
  match drop:
    case True{}:
      fw
    case False{}:
      sp.rw.cons3(Rw{X.SxAtom{a}, Nil{}}, fw, sp.rw.cons(ew, Rw{X.SxNil{}, Nil{}}))

# a node (a f e) from its parts' walks: the outer application of a copy's
# call (its argument's place k - 1), or the node
def sp.fd.fin(d: Maybe<&2, Fd>, +a: List<&2, U32>, fw: Rw, ew: Rw, +k: Nat) -> Rw:
  match d:
    case Some{Fd{hd, fas, q}}:
      sp.rw.addq(sp.p10.arg(sp.fa.isat(fas, sp.pred(k)), a, fw, ew), q)
    case None{}:
      sp.rw.cons3(Rw{X.SxAtom{a}, Nil{}}, fw, sp.rw.cons(ew, Rw{X.SxNil{}, Nil{}}))

# a node (a f e) of a copy's call's spine: an application keeps e unless its
# place goes, a type's or a dictionary's goes, anything else is the old
# function part, the copy's in its place
def sp.p10.spine(+a: List<&2, U32>, +i: Nat, +fas: List<&2, Fa>, +hd: X.Sx, +fw: Rw, ew: Rw) -> Rw:
  +isty = Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp"))
  Bool.pick(Rw, sp.is(a, "app"), sp.p10.arg(sp.fa.isat(fas, i), a, fw, ew), Bool.pick(Rw, isty, fw, Rw{hd, Nil{}}))

# the walk, structural: at a top application, the decision on its call
def sp.p10(x: X.Sx, m: Pm, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>, +lf: Lf, +dq: List<&2, Rq>) -> Rw:
  match x m:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} PmNode{top}:
      +n = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}} : X.Sx}
      +k = List.length(&2, X.Sx, sp.spine.args(n, Nil{}))
      +d = sp.fa.decide.if(Bool.and(top, sp.is(a, "app")), n, me, cur, ix, env, lf, dq)
      sp.fd.fin(d, a, sp.p10(f, sp.fd.mode(d, k, sp.isapp(n)), me, cur, ix, env, lf, dq), sp.p10(e, PmNode{True{}}, me, cur, ix, env, lf, dq), k)
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} PmArgs{+hd, +i, +fas}:
      +j = Bool.pick(Nat, sp.is(a, "app"), sp.pred(i), i)
      sp.p10.spine(a, i, fas, hd, sp.p10(f, PmArgs{hd, j, fas}, me, cur, ix, env, lf, dq), sp.p10(e, PmNode{True{}}, me, cur, ix, env, lf, dq))
    case X.SxCons{+h, +t} PmNode{top}:
      sp.rw.cons(sp.p10(h, PmNode{True{}}, me, cur, ix, env, lf, dq), sp.p10(t, PmNode{True{}}, me, cur, ix, env, lf, dq))
    case _ PmArgs{hd, i, fas}:
      Rw{hd, Nil{}}
    case y PmNode{top}:
      Rw{y, Nil{}}

# the name a top exports first (its def's)
def sp.fa.me(+x: X.Sx) -> List<&2, U32>:
  +es = sp.exports(x)
  sp.sat(sp.at(sp.or(sp.nth(es, 0n), X.SxNil{}), 1n), 2n)

# the local functions an argument has as their values: those that name a
# local or the def they are in (a closed one the fold lifts to a closed
# def, a template, as it was)
def sp.fa.lf.need(lf: List<&2, Asb>, +meg: X.Sx) -> List<&2, Asb>:
  match lf:
    case Nil{}:
      Nil{}
    case Asb{+v, +val} <> t:
      +fr = sp.fa.frees(val, sp.fa.binds(val, Nil{}), Nil{})
      +keep = Bool.or(Bool.not(List.is_empty(&2, X.Sx, fr)), sp.fa.names(val, meg))
      +rest = sp.fa.lf.need(t, meg)
      Bool.pick(List<&2, Asb>, keep, Asb{v, val} <> rest, rest)

def sp.rw.p10(r: Rw, +cur: List<&2, U32>, +ix: Ix, +rl0: List<&2, X.Sx>, +ol0: List<&2, Og>, +kn: List<&2, Rq>, +rg: List<&2, X.Sx>) -> Rw:
  match r:
    case Rw{+x, +q}:
      +env = List.append(&2, Asb, sp.fa.binds(x, Nil{}), sp.og.base(ol0))
      +lfa = sp.fa.lfuns(x, Nil{})
      +meg = sp.g(cur, sp.fa.me(x), "var")
      +lf = {Lf{lfa, sp.fa.lf.need(lfa, meg), meg, sp.fl.recs(x, rl0), sp.og.of(x, sp.og.base(ol0), ol0, False{}), kn, rg} : Lf}
      sp.rw.addq(sp.p10(x, PmNode{True{}}, sp.fa.me(x), cur, ix, env, lf, q), q)

# The copy: the def at the types, the arguments in their parameters' places
# (a variable pattern's uses are the argument), the free locals first

# a function type without the parameters at fas' places
def sp.fa.ty.drop(t: X.Sx, +fas: List<&2, Fa>, +i: Nat) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, X.SxCons{+r, X.SxNil{}}}}:
      +r2 = sp.fa.ty.drop(r, fas, 1n+i)
      Bool.pick(X.Sx, sp.is(a, "tfun"), Bool.pick(X.Sx, sp.fa.isat(fas, i), r2, sp.l([sp.a("tfun"), p, r2])), X.SxCons{X.SxAtom{a}, X.SxCons{p, X.SxCons{r, X.SxNil{}}}})
    case u:
      u

def sp.fa.ty.pre(ts: List<&2, X.Sx>, t: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      t
    case a <> r:
      sp.l([sp.a("tfun"), a, sp.fa.ty.pre(r, t)])

# a clause's variables at fas' places, as their arguments
def sp.fa.pats.subs(ps: List<&2, X.Sx>, +fas: List<&2, Fa>, +i: Nat) -> List<&2, Asb>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      +rest = sp.fa.pats.subs(t, fas, 1n+i)
      Bool.pick(List<&2, Asb>, Bool.and(sp.fa.isat(fas, i), sp.head.is(p, "pvar")), Asb{sp.at(sp.at(p, 1n), 1n), sp.fa.argat(fas, i)} <> rest, rest)

def sp.fa.fvpats(ts: List<&2, X.Sx>, +i: Nat) -> List<&2, X.Sx>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.fa.fv(i), t])]) <> sp.fa.fvpats(r, 1n+i)

def sp.fa.clause(+c: X.Sx, +fas: List<&2, Fa>, +fvt: List<&2, X.Sx>) -> X.Sx:
  +ps = sp.els(sp.at(c, 1n))
  +s = sp.fa.pats.subs(ps, fas, 0n)
  +g = sp.at(c, 2n)
  sp.l([sp.a("match"), sp.l(List.append(&2, X.Sx, sp.fa.fvpats(fvt, 0n), sp.fa.drop.at(ps, fas, 0n))), sp.as.sub(g, sp.as.look(g, s), s)])

def sp.fa.clauses(cs: List<&2, X.Sx>, +fas: List<&2, Fa>, +fvt: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      sp.fa.clause(c, fas, fvt) <> sp.fa.clauses(t, fas, fvt)

# (matches (ARGTYPE...) RES ORIGIN (MATCH...))
def sp.fa.ms(+ms: X.Sx, +fas: List<&2, Fa>, +fvt: List<&2, X.Sx>) -> X.Sx:
  sp.l([sp.a("matches"), sp.l(List.append(&2, X.Sx, fvt, sp.fa.drop.at(sp.els(sp.at(ms, 1n)), fas, 0n))), sp.at(ms, 2n), sp.at(ms, 3n), sp.l(sp.fa.clauses(sp.els(sp.at(ms, 4n)), fas, fvt))])

def sp.fa.copy.of(f: Maybe<&2, X.Sx>, +n: List<&2, U32>, +fas: List<&2, Fa>, +fvt: List<&2, X.Sx>, +tys: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match f:
    case Some{+fun}:
      +sbs = sp.zip(sp.foralls(sp.at(fun, 2n)), tys)
      +var = sp.g(cur, n, "var")
      +orig = sp.fa.unself(sp.var.of(sp.at(fun, 1n)))
      +ty = sp.fa.ty.pre(fvt, sp.fa.ty.drop(sp.norm(sp.subst(sp.strip(sp.at(fun, 2n)), sbs), ix), fas, 0n))
      +ms = sp.norm(sp.fa.unself.of(sp.subst(sp.fa.ms(sp.at(fun, 4n), fas, fvt), sbs), orig), ix)
      Some{sp.l([sp.a("top"), sp.l([sp.a("abs"), X.SxNil{}, X.SxNil{}, sp.l([sp.l([sp.a("export"), var, ty])]), sp.l([sp.l([sp.a("evbinds")])]), sp.l([sp.l([sp.a("fun"), sp.l([sp.a("self"), var]), ty, sp.at(fun, 3n), ms, sp.a("hole")])]), sp.a("nospan")])])}
    case None{}:
      None{}

def sp.copy.any(+rq: Rq, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match rq ix:
    case Rq{n, LoF{k, fas, fvt, rg}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, +fns, cts}:
      sp.fa.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.df.find(fns, k), t => sp.fun.of(t)), n, fas, fvt, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts})
    case Rq{n, LoFm{nm, m, j, mtys, fas, fvt, rg}, tys} +i:
      sp.fa.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.copy(Rq{nm, LoL{m, j}, mtys}, cur, i), t => sp.fun.of(t)), n, fas, fvt, Nil{}, cur, i)
    case r i:
      sp.copy(r, cur, i)

# List comprehensions ----------------------------------------------------------

# [e | Q] (do listcomp (List X) STMTS) as the Haskell 2010 report's
# translation (3.11): [e | b, Q] = if b then [e | Q] else []; [e | p <- l,
# Q] = concatMap (\p -> [e | Q]; _ -> []) l (the wildcard when p can fail);
# [e | let ds, Q] = let ds in [e | Q]; [e | ] = [e]. The lambda's argument
# type is l's element type when l is a local of known type, else p's: a
# variable's, a tuple's of its parts', a constructor's (base's list, Maybe,
# Either; a package's, the type of its name). concatMap at a list is Base's
# model's when the package has it (sp.pc), so the lambda is copied with its
# free locals (a generator's variables).

# a package's constructor's type: the data's that declares it (else the
# type of its name)
def sp.lc.cty.pkg(f: Maybe<&2, Ct>, +m: List<&2, U32>, +n: List<&2, U32>, +args: List<&2, X.Sx>) -> X.Sx:
  match f:
    case Some{Ct{k, tm, tn}}:
      sp.tc(tm, tn, args)
    case None{}:
      sp.tc(m, n, args)

# a constructor's type at its type arguments
def sp.lc.cty(+c: X.Sx, +args: List<&2, X.Sx>, +cts: List<&2, Ct>) -> X.Sx:
  +n = sp.sat(c, 2n)
  +lst = Bool.or(sp.is(n, ":"), sp.is(n, "[]"))
  +may = Bool.or(sp.is(n, "Just"), sp.is(n, "Nothing"))
  +eit = Bool.or(sp.is(n, "Left"), sp.is(n, "Right"))
  # free's :< , Cofree's (Control.Comonad.Cofree) and CofreeF's
  # (Control.Comonad.Trans.Cofree)
  +cof = Bool.and(sp.is(n, ":<"), Bool.or(sp.is(sp.sat(c, 1n), "Control.Comonad.Cofree"), sp.is(sp.sat(c, 1n), "Control.Comonad.Trans.Cofree")))
  +cofn = Bool.pick(List<&2, U32>, sp.is(sp.sat(c, 1n), "Control.Comonad.Cofree"), S.b("Cofree"), S.b("CofreeF"))
  Bool.pick(X.Sx, lst, sp.tc(S.b("GHC.Types"), S.b("List"), args), Bool.pick(X.Sx, may, sp.tc(S.b("GHC.Internal.Maybe"), S.b("Maybe"), args), Bool.pick(X.Sx, eit, sp.tc(S.b("GHC.Internal.Data.Either"), S.b("Either"), args), Bool.pick(X.Sx, cof, sp.tc(sp.sat(c, 1n), cofn, args), sp.lc.cty.pkg(sp.ct.find(cts, sp.key(sp.sat(c, 1n), n)), sp.sat(c, 1n), n, args)))))

# the types of a pattern (isl False) or of a list of patterns (isl True);
# an unknown one is ()
def sp.lc.ty(p: X.Sx, isl: Bool, +cts: List<&2, Ct>) -> List<&2, X.Sx>:
  match p isl:
    case X.SxCons{h, t} True{}:
      List.append(&2, X.Sx, sp.lc.ty(h, False{}, cts), sp.lc.ty(t, True{}, cts))
    case _ True{}:
      Nil{}
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+q, +r}} False{}:
      +bv = Bool.or(sp.is(a, "pvar"), sp.is(a, "pas"))
      +inner = Bool.or(sp.is(a, "pbang"), sp.is(a, "plazy"))
      +tup = sp.is(a, "ptuple")
      +con = sp.is(a, "pcon")
      +nlit = Bool.and(sp.is(a, "pnlit"), sp.head.is(q, "olit"))
      sp.if(List<&2, X.Sx>, bv, _ => [sp.at(q, 2n)], _ => sp.if(List<&2, X.Sx>, sp.is(a, "pwild"), _ => [q], _ => sp.if(List<&2, X.Sx>, inner, _ => sp.lc.ty(q, False{}, cts), _ => sp.if(List<&2, X.Sx>, tup, _ => [sp.tc(S.b("GHC.Tuple"), sp.cat(S.b("Tuple"), S.b(Nat.show(List.length(&2, X.Sx, sp.els(q))))), sp.lc.ty(q, True{}, cts))], _ => sp.if(List<&2, X.Sx>, con, _ => [sp.lc.cty(q, sp.els(sp.at(X.SxCons{X.SxAtom{a}, X.SxCons{q, r}}, 2n)), cts)], _ => sp.if(List<&2, X.Sx>, nlit, _ => [sp.at(q, 2n)], _ => [sp.l(Nil{})]))))))
    case _ False{}:
      [sp.l(Nil{})]

# whether a generator's pattern can fail: a constructor's (but a tuple's),
# a literal or a list pattern anywhere in it (`(h, Right g) <- xs` skips a
# Left: the lambda's second match answers [])
def sp.lc.fails(+p: X.Sx) -> Bool:
  Bool.or(sp.has(p, S.b("pcon")), Bool.or(sp.has(p, S.b("plit")), Bool.or(sp.has(p, S.b("pnlit")), sp.has(p, S.b("plist")))))

# the element type of a generator's list l with pattern p
def sp.lc.elem(+l: X.Sx, +p: X.Sx, +env: List<&2, Asb>, +cts: List<&2, Ct>) -> X.Sx:
  +lt = Bool.pick(Maybe<&2, X.Sx>, sp.head.is(l, "l"), sp.as.look(l, env), None{})
  +ok = Bool.and(Maybe.is_some(&2, X.Sx, lt), sp.is(sp.tckey(Maybe.default(&2, X.Sx, lt, X.SxNil{})), "GHC.Types.List"))
  Bool.pick(X.Sx, ok, sp.at(Maybe.default(&2, X.Sx, lt, X.SxNil{}), 3n), sp.first(sp.lc.ty(p, False{}, cts)))

def sp.lc.nil(+x: X.Sx) -> X.Sx:
  sp.l([sp.a("list"), x, X.SxNil{}])

def sp.lc.lam(+a: X.Sx, +x: X.Sx, +p: X.Sx, +body: X.Sx) -> X.Sx:
  +ok = sp.l([sp.a("match"), sp.l([p]), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, body])]), sp.l([sp.a("binds")])])])
  +no = sp.l([sp.a("match"), sp.l([sp.l([sp.a("pwild"), a])]), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, sp.lc.nil(x)])]), sp.l([sp.a("binds")])])])
  +ms = Bool.pick(List<&2, X.Sx>, sp.lc.fails(p), [ok, no], [ok])
  sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([a]), sp.tc(S.b("GHC.Types"), S.b("List"), [x]), sp.a("generated"), sp.l(ms)])])

# concatMap f l at a list, from a to x
def sp.lc.cmap(+a: X.Sx, +x: X.Sx, +f: X.Sx, +l: X.Sx) -> X.Sx:
  +fo = S.b("GHC.Internal.Data.Foldable")
  +h = sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), sp.g(fo, S.b("concatMap"), "var"), sp.tc(S.b("GHC.Types"), S.b("List"), Nil{})]), a]), x]), sp.g(fo, S.b("$fFoldableList"), "dfun")])
  sp.l([sp.a("app"), sp.l([sp.a("app"), h, f]), l])

# [e | STMTS] at element type x
def sp.lc.stmts(ss: X.Sx, +x: X.Sx, +env: List<&2, Asb>, +cts: List<&2, Ct>) -> X.Sx:
  match ss:
    case X.SxCons{X.SxCons{X.SxAtom{+a}, X.SxCons{+e, +r}}, +t}:
      +s = {X.SxCons{X.SxAtom{a}, X.SxCons{e, r}} : X.Sx}
      +rest = sp.lc.stmts(t, x, env, cts)
      +l = sp.at(s, 2n)
      +el = sp.lc.elem(l, e, env, cts)
      sp.if(X.Sx, sp.is(a, "last"), _ => sp.l([sp.a("list"), x, sp.l([e])]), _ => sp.if(X.Sx, sp.is(a, "body"), _ => sp.l([sp.a("if"), e, rest, sp.lc.nil(x)]), _ => sp.if(X.Sx, sp.is(a, "letstmt"), _ => sp.l([sp.a("let"), e, rest]), _ => sp.lc.cmap(el, x, sp.lc.lam(el, x, e, rest), l))))
    case _:
      sp.lc.nil(x)

# every list comprehension, the innermost first
def sp.lc(x: X.Sx, +env: List<&2, Asb>, +cts: List<&2, Ct>) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      +y = {X.SxCons{sp.lc(h, env, cts), sp.lc(t, env, cts)} : X.Sx}
      +isl = Bool.and(sp.head.is(y, "do"), sp.is(X.tsx.atom.of(sp.at(y, 1n)), "listcomp"))
      sp.if(X.Sx, isl, _ => sp.lc.stmts(sp.at(y, 3n), sp.at(sp.at(y, 2n), 3n), env, cts), _ => y)
    case z:
      z

# A list function given a lambda over locals -----------------------------------------

# Bend takes a list function's function as a template, closed; a lambda that
# names a run-time local (`map (\x -> x + n) xs`) is not one, and the fold
# made n a template of the def, which then no run-time value calls, or left
# the def out (fold:closure-argument).  So the list function is written at
# the call as the recursion it is, a local function of the lambda's body,
#     let hfH [] = []; hfH (x : t) = (x + n) : hfH t in hfH xs
# which the fold lifts, its locals its first parameters: map (fmap, <$> at a
# list), filter, foldr, foldl, foldl', any, all, concatMap, takeWhile,
# dropWhile, find, mapMaybe and zipWith, with all their arguments.  A lambda
# that names no local but functions stays (a closed template, or a function
# parameter's).  H is the call's hash.  In a package foldr, foldl, concatMap
# and filter are the model's copies before this (sp.pc).

# the lambda's patterns and body, its one clause plain: no guard, no where,
# each pattern one every value matches
def sp.hf.irr(p: X.Sx) -> Bool:
  match p:
    case X.SxCons{X.SxAtom{+a}, +r}:
      +v = Bool.or(sp.is(a, "pvar"), sp.is(a, "pwild"))
      sp.if(Bool, v, _ => True{}, _ => sp.if(Bool, sp.is(a, "ptuple"), _ => sp.hf.irr(r), _ => False{}))
    case X.SxCons{X.SxCons{h, t}, r}:
      Bool.and(sp.hf.irr(X.SxCons{h, t}), sp.hf.irr(r))
    case X.SxNil{}:
      True{}
    case _:
      False{}

def sp.hf.irrs(ps: List<&2, X.Sx>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(sp.hf.irr(p), sp.hf.irrs(t))

def sp.hf.lam(+f: X.Sx, +n: Nat) -> Maybe<&2, Bl>:
  +cls = sp.els(sp.at(sp.at(f, 2n), 4n))
  +m0 = sp.first(cls)
  +ps = sp.els(sp.at(m0, 1n))
  +gr = sp.at(m0, 2n)
  +gs = sp.els(sp.at(gr, 1n))
  +g0 = sp.first(gs)
  +one = Bool.and(Nat.is_eq(List.length(&2, X.Sx, cls), 1n), Nat.is_eq(List.length(&2, X.Sx, gs), 1n))
  +ok = Bool.and(Bool.and(sp.head.is(f, "lam"), Nat.is_eq(List.length(&2, X.Sx, ps), n)), Bool.and(Bool.and(one, sp.hf.irrs(ps)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")])))))
  Bool.pick(Maybe<&2, Bl>, ok, Some{Bl{ps, sp.at(g0, 2n)}}, None{})

# a local of a lambda that is no function
def sp.hf.free(vs: List<&2, X.Sx>, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case +v <> t:
      +ty = Maybe.default(&2, X.Sx, sp.as.look(v, env), X.SxNil{})
      Bool.or(Bool.or(sp.beta.data(ty, sys), sp.head.is(ty, "tv")), sp.hf.free(t, env, sys))

# Terms
def sp.hf.list(+a: X.Sx) -> X.Sx:
  sp.tc(S.b("GHC.Types"), S.b("List"), [a])

def sp.hf.app(+f: X.Sx, +x: X.Sx) -> X.Sx:
  sp.l([sp.a("app"), f, x])

def sp.hf.nil(+a: X.Sx) -> X.Sx:
  sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Types"), S.b("[]"), "con"), a])

def sp.hf.cons(+a: X.Sx, +h: X.Sx, +t: X.Sx) -> X.Sx:
  sp.hf.app(sp.hf.app(sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Types"), S.b(":"), "con"), a]), h), t)

def sp.hf.bool(+s: String) -> X.Sx:
  sp.g(S.b("GHC.Types"), S.b(s), "con")

def sp.hf.if(+c: X.Sx, +a: X.Sx, +b: X.Sx) -> X.Sx:
  sp.l([sp.a("if"), c, a, b])

def sp.hf.v(+s: String, +h: List<&2, U32>) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b(s), h)}, X.SxAtom{sp.cat(S.b(s), h)}])

def sp.hf.pv(+v: X.Sx, +ty: X.Sx) -> X.Sx:
  sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, ty])])

def sp.hf.pnil(+a: X.Sx) -> X.Sx:
  sp.l([sp.a("pcon"), sp.g(S.b("GHC.Types"), S.b("[]"), "con"), sp.l([a]), sp.l([sp.a("args")])])

def sp.hf.pcons(+a: X.Sx, +p: X.Sx, +t: X.Sx) -> X.Sx:
  sp.l([sp.a("pcon"), sp.g(S.b("GHC.Types"), S.b(":"), "con"), sp.l([a]), sp.l([sp.a("args"), p, sp.hf.pv(t, sp.hf.list(a))])])

def sp.hf.match(+ps: List<&2, X.Sx>, +e: X.Sx) -> X.Sx:
  sp.l([sp.a("match"), sp.l(ps), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, e])]), sp.l([sp.a("binds")])])])

def sp.hf.fun(ts: List<&2, X.Sx>, +r: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      r
    case t <> u:
      sp.l([sp.a("tfun"), t, sp.hf.fun(u, r)])

# let GO of these clauses (its parameters' types ts, its answer's r) in e
def sp.hf.let(+go: X.Sx, +ts: List<&2, X.Sx>, +r: X.Sx, +ms: List<&2, X.Sx>, +e: X.Sx) -> X.Sx:
  +m = {sp.l([sp.a("matches"), sp.l(ts), r, sp.a("source"), sp.l(ms)]) : X.Sx}
  sp.l([sp.a("let"), sp.l([sp.a("binds"), sp.l([sp.a("rec"), sp.l([sp.a("fun"), go, sp.hf.fun(ts, r), sp.a("nospan"), m])])]), e])

# the element's pattern, the body, and the element as a term
type Hb is Data:
  Hb{p: X.Sx, b: X.Sx, x: X.Sx}

# (var: the element must be a variable)
def sp.hf.body(m: Maybe<&2, Bl>, +var: Bool, +f: X.Sx, +a: X.Sx, +x: X.Sx) -> Hb:
  match m:
    case Some{Bl{ps, +b}}:
      +p = sp.first(ps)
      +pv = sp.head.is(p, "pvar")
      Bool.pick(Hb, Bool.and(var, Bool.not(pv)), Hb{sp.hf.pv(x, a), sp.hf.app(f, x), x}, Hb{p, b, sp.at(sp.at(p, 1n), 1n)})
    case None{}:
      Hb{sp.hf.pv(x, a), sp.hf.app(f, x), x}

# one list, one element: its clauses' bodies by kind (gt: the recursion)
def sp.hf.one(+k: String, +b: X.Sx, +x: X.Sx, +t: X.Sx, +gt: X.Sx, +a: X.Sx, +r: X.Sx) -> X.Sx:
  +s = S.b(k)
  sp.if(X.Sx, sp.is(s, "map"), _ => sp.hf.cons(r, b, gt), _ => sp.if(X.Sx, sp.is(s, "filter"), _ => sp.hf.if(b, sp.hf.cons(a, x, gt), gt), _ => sp.if(X.Sx, sp.is(s, "any"), _ => sp.hf.if(b, sp.hf.bool("True"), gt), _ => sp.if(X.Sx, sp.is(s, "all"), _ => sp.hf.if(b, gt, sp.hf.bool("False")), _ => sp.if(X.Sx, sp.is(s, "concatMap"), _ => sp.hf.app(sp.hf.app(sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Internal.Base"), S.b("++"), "var"), r]), b), gt), _ => sp.if(X.Sx, sp.is(s, "takeWhile"), _ => sp.hf.if(b, sp.hf.cons(a, x, gt), sp.hf.nil(a)), _ => sp.if(X.Sx, sp.is(s, "dropWhile"), _ => sp.hf.if(b, gt, sp.hf.cons(a, x, t)), _ => sp.hf.if(b, sp.hf.app(sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Internal.Maybe"), S.b("Just"), "con"), a]), x), gt))))))))

# mapMaybe's: case B of Nothing -> gt; Just y -> y : gt
def sp.hf.may(+b: X.Sx, +y: X.Sx, +gt: X.Sx, +r: X.Sx) -> X.Sx:
  +mb = S.b("GHC.Internal.Maybe")
  +no = {sp.hf.match([sp.l([sp.a("pcon"), sp.g(mb, S.b("Nothing"), "con"), sp.l([r]), sp.l([sp.a("args")])])], gt) : X.Sx}
  +ju = {sp.hf.match([sp.l([sp.a("pcon"), sp.g(mb, S.b("Just"), "con"), sp.l([r]), sp.l([sp.a("args"), sp.hf.pv(y, r)])])], sp.hf.cons(r, y, gt)) : X.Sx}
  sp.l([sp.a("case"), b, sp.l([sp.a("matches"), sp.l([sp.tc(mb, S.b("Maybe"), [r])]), sp.hf.list(r), sp.a("source"), sp.l([no, ju])])])

# what the empty list answers, and the answer's type
def sp.hf.zero(+k: String, +a: X.Sx, +r: X.Sx) -> X.Sx:
  +s = S.b(k)
  sp.if(X.Sx, sp.is(s, "any"), _ => sp.hf.bool("False"), _ => sp.if(X.Sx, sp.is(s, "all"), _ => sp.hf.bool("True"), _ => sp.if(X.Sx, sp.is(s, "find"), _ => sp.l([sp.a("tyapp"), sp.g(S.b("GHC.Internal.Maybe"), S.b("Nothing"), "con"), a]), _ => sp.hf.nil(r))))

def sp.hf.ans(+k: String, +a: X.Sx, +r: X.Sx) -> X.Sx:
  +s = S.b(k)
  sp.if(X.Sx, Bool.or(sp.is(s, "any"), sp.is(s, "all")), _ => sp.tc(S.b("GHC.Types"), S.b("Bool"), Nil{}), _ => sp.if(X.Sx, sp.is(s, "find"), _ => sp.tc(S.b("GHC.Internal.Maybe"), S.b("Maybe"), [a]), _ => sp.hf.list(r)))

# a call of the kind k (element a, answer's element r) at f and the list l
def sp.hf.mk1(+k: String, +a: X.Sx, +r: X.Sx, +f: X.Sx, +l: X.Sx, +h: List<&2, U32>, w: Hb) -> X.Sx:
  match w:
    case Hb{+p, +b, +x}:
      +go = sp.hf.v("hf", h)
      +t = sp.hf.v("hft", h)
      +gt = sp.hf.app(go, t)
      +body = {sp.if(X.Sx, sp.is(S.b(k), "mapMaybe"), _ => sp.hf.may(b, sp.hf.v("hfy", h), gt, r), _ => sp.hf.one(k, b, x, t, gt, a, r)) : X.Sx}
      sp.hf.let(go, [sp.hf.list(a)], sp.hf.ans(k, a, r), [sp.hf.match([sp.hf.pnil(a)], sp.hf.zero(k, a, r)), sp.hf.match([sp.hf.pcons(a, p, t)], body)], sp.hf.app(go, l))

# whether the kind needs its element as a term
def sp.hf.needs(+k: String) -> Bool:
  +s = S.b(k)
  Bool.or(Bool.or(sp.is(s, "filter"), sp.is(s, "takeWhile")), Bool.or(sp.is(s, "dropWhile"), sp.is(s, "find")))

def sp.hf.k1(+k: String, +a: X.Sx, +r: X.Sx, +f: X.Sx, +l: X.Sx, +h: List<&2, U32>) -> X.Sx:
  sp.hf.mk1(k, a, r, f, l, h, sp.hf.body(sp.hf.lam(f, 1n), sp.hf.needs(k), f, a, sp.hf.v("hfx", h)))

def sp.hf.ty(+tys: List<&2, X.Sx>, n: Nat) -> X.Sx:
  Maybe.default(&2, X.Sx, sp.nth(tys, n), X.SxNil{})

# foldr f z l: hfH [] = z; hfH (x : t) = f x (hfH t)
def sp.hf.foldr.of(m: Maybe<&2, Bl>, +a: X.Sx, +f: X.Sx, +x: X.Sx, +gt: X.Sx, +sys: List<&2, Sy>) -> Hb:
  match m:
    case Some{Bl{+ps, +b}}:
      +e = sp.beta.done(sp.beta.acts([sp.hf.ty(ps, 1n)], [gt], b, sys), b, X.SxNil{})
      Bool.pick(Hb, Nat.is_gt(X.tsx.len(e), 0n), Hb{sp.first(ps), e, x}, Hb{sp.hf.pv(x, a), sp.hf.app(sp.hf.app(f, x), gt), x})
    case None{}:
      Hb{sp.hf.pv(x, a), sp.hf.app(sp.hf.app(f, x), gt), x}

def sp.hf.foldr.at(w: Hb, +a: X.Sx, +r: X.Sx, +z: X.Sx, +l: X.Sx, +go: X.Sx, +t: X.Sx) -> X.Sx:
  match w:
    case Hb{p, b, x}:
      sp.hf.let(go, [sp.hf.list(a)], r, [sp.hf.match([sp.hf.pnil(a)], z), sp.hf.match([sp.hf.pcons(a, p, t)], b)], sp.hf.app(go, l))

def sp.hf.foldr(+a: X.Sx, +r: X.Sx, +f: X.Sx, +z: X.Sx, +l: X.Sx, +h: List<&2, U32>, m: Maybe<&2, Bl>, +sys: List<&2, Sy>) -> X.Sx:
  +go = sp.hf.v("hf", h)
  +t = sp.hf.v("hft", h)
  sp.hf.foldr.at(sp.hf.foldr.of(m, a, f, sp.hf.v("hfx", h), sp.hf.app(go, t), sys), a, r, z, l, go, t)

# a clause of two parameters: the element's pattern, the other's, the body
type Hd2 is Data:
  Hd2{p: X.Sx, q: X.Sx, b: X.Sx}

def sp.hf.two(m: Maybe<&2, Bl>, +p: X.Sx, +q: X.Sx, +b: X.Sx) -> Hd2:
  match m:
    case Some{Bl{+ps, e}}:
      Hd2{sp.first(ps), sp.hf.ty(ps, 1n), e}
    case None{}:
      Hd2{p, q, b}

# foldl f z l: hfH [] acc = acc; hfH (x : t) acc = hfH t (f acc x)
def sp.hf.foldl.at(w: Hd2, +a: X.Sx, +r: X.Sx, +z: X.Sx, +l: X.Sx, +go: X.Sx, +t: X.Sx, +c: X.Sx) -> X.Sx:
  match w:
    case Hd2{p, q, b}:
      sp.hf.let(go, [sp.hf.list(a), r], r, [sp.hf.match([sp.hf.pnil(a), sp.hf.pv(c, r)], c), sp.hf.match([sp.hf.pcons(a, q, t), p], sp.hf.app(sp.hf.app(go, t), b))], sp.hf.app(sp.hf.app(go, l), z))

def sp.hf.foldl(+a: X.Sx, +r: X.Sx, +f: X.Sx, +z: X.Sx, +l: X.Sx, +h: List<&2, U32>, m: Maybe<&2, Bl>) -> X.Sx:
  +x = sp.hf.v("hfx", h)
  +c = sp.hf.v("hfa", h)
  sp.hf.foldl.at(sp.hf.two(m, sp.hf.pv(c, r), sp.hf.pv(x, a), sp.hf.app(sp.hf.app(f, c), x)), a, r, z, l, sp.hf.v("hf", h), sp.hf.v("hft", h), c)

# zipWith f l k
def sp.hf.zip.at(w: Hd2, +a: X.Sx, +b: X.Sx, +r: X.Sx, +l: X.Sx, +k: X.Sx, +go: X.Sx, +t: X.Sx, +u: X.Sx) -> X.Sx:
  match w:
    case Hd2{p, q, e}:
      sp.hf.let(go, [sp.hf.list(a), sp.hf.list(b)], sp.hf.list(r), [sp.hf.match([sp.hf.pcons(a, p, t), sp.hf.pcons(b, q, u)], sp.hf.cons(r, e, sp.hf.app(sp.hf.app(go, t), u))), sp.hf.match([sp.l([sp.a("pwild"), sp.hf.list(a)]), sp.l([sp.a("pwild"), sp.hf.list(b)])], sp.hf.nil(r))], sp.hf.app(sp.hf.app(go, l), k))

def sp.hf.zip(+a: X.Sx, +b: X.Sx, +r: X.Sx, +f: X.Sx, +l: X.Sx, +k: X.Sx, +h: List<&2, U32>, m: Maybe<&2, Bl>) -> X.Sx:
  +x = sp.hf.v("hfx", h)
  +y = sp.hf.v("hfy", h)
  sp.hf.zip.at(sp.hf.two(m, sp.hf.pv(x, a), sp.hf.pv(y, b), sp.hf.app(sp.hf.app(f, x), y)), a, b, r, l, k, sp.hf.v("hf", h), sp.hf.v("hft", h), sp.hf.v("hfu", h))

# which list function: one element's kind (its name; the places of the
# element's type and the answer's among the type arguments), foldr, foldl,
# zipWith; at: whether its first type argument must be the list
type Hk is Data:
  Hk1{k: String, at: Bool, a: Nat, r: Nat}
  HkFoldr{at: Bool}
  HkFoldl{at: Bool}
  HkZip{}
  HkMap{k: String, key: Bool, v: Nat, w: Nat, kt: Nat}
  HkMapFoldr{key: Bool, v: Nat, r: Nat, kt: Nat}
  HkFromSet{}

type Hke is Data:
  Hke{key: String, k: Hk}

def sp.hf.tab() -> List<&2, Hke>:
  +fo = {"GHC.Internal.Data.Foldable." : String}
  [Hke{"GHC.Internal.Base.map", Hk1{"map", False{}, 0n, 1n}}, Hke{"GHC.Internal.Base.fmap", Hk1{"map", True{}, 1n, 2n}}, Hke{"GHC.Internal.Data.Functor.<$>", Hk1{"map", True{}, 1n, 2n}}, Hke{"GHC.Internal.List.filter", Hk1{"filter", False{}, 0n, 0n}}, Hke{fo ++ "any", Hk1{"any", True{}, 1n, 1n}}, Hke{fo ++ "all", Hk1{"all", True{}, 1n, 1n}}, Hke{fo ++ "concatMap", Hk1{"concatMap", True{}, 1n, 2n}}, Hke{fo ++ "find", Hk1{"find", True{}, 1n, 1n}}, Hke{"GHC.Internal.List.takeWhile", Hk1{"takeWhile", False{}, 0n, 0n}}, Hke{"GHC.Internal.List.dropWhile", Hk1{"dropWhile", False{}, 0n, 0n}}, Hke{"GHC.Internal.Data.Maybe.mapMaybe", Hk1{"mapMaybe", False{}, 0n, 1n}}, Hke{fo ++ "foldr", HkFoldr{True{}}}, Hke{fo ++ "foldl", HkFoldl{True{}}}, Hke{fo ++ "foldl'", HkFoldl{True{}}}, Hke{"GHC.Internal.List.zipWith", HkZip{}}]

# the model's own (Cata.Base), where rule 15 made no copy (inside a copy, at
# another function): the fold reads them so in spec's output
def sp.hf.tab2() -> List<&2, Hke>:
  [Hke{"Cata.Base.foldr", HkFoldr{False{}}}, Hke{"Cata.Base.foldl", HkFoldl{False{}}}, Hke{"Cata.Base.foldl'", HkFoldl{False{}}}, Hke{"Cata.Base.concatMap", Hk1{"concatMap", False{}, 0n, 1n}}, Hke{"Cata.Base.filter", Hk1{"filter", False{}, 0n, 0n}}, Hke{"Data.Map.Internal.map", HkMap{"map", False{}, 0n, 1n, 2n}}, Hke{"Data.Map.Strict.Internal.map", HkMap{"map", False{}, 0n, 1n, 2n}}, Hke{"Data.Map.Internal.mapWithKey", HkMap{"map", True{}, 1n, 2n, 0n}}, Hke{"Data.Map.Strict.Internal.mapWithKey", HkMap{"map", True{}, 1n, 2n, 0n}}, Hke{"Data.Map.Internal.filter", HkMap{"filter", False{}, 0n, 0n, 1n}}, Hke{"Data.Map.Internal.filterWithKey", HkMap{"filter", True{}, 1n, 1n, 0n}}, Hke{"Data.Map.Internal.foldr", HkMapFoldr{False{}, 0n, 1n, 2n}}, Hke{"Data.Map.Internal.foldrWithKey", HkMapFoldr{True{}, 1n, 2n, 0n}}, Hke{"Data.Map.Internal.fromSet", HkFromSet{}}]

def sp.hf.find(hs: List<&2, Hke>, +k: List<&2, U32>) -> Maybe<&2, Hk>:
  match hs:
    case Nil{}:
      None{}
    case Hke{+q, h} <> t:
      sp.if(Maybe<&2, Hk>, sp.is(k, q), _ => Some{h}, _ => sp.hf.find(t, k))

def sp.hf.digits(+x: X.Sx) -> List<&2, U32>:
  S.b(U32.show(sp.fa.hash(X.tsx.show(x), 5381)))

# a list function without its list (`fmap res`, in `gets (fmap res . rows)`):
# a lambda over the list
def sp.hf.part(+s: String, +a: X.Sx, +r: X.Sx, +f: X.Sx, +h: List<&2, U32>) -> X.Sx:
  +l = sp.hf.v("hfl", h)
  +m = sp.hf.match([sp.hf.pv(l, sp.hf.list(a))], sp.hf.k1(s, a, r, f, l, h))
  sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([sp.hf.list(a)]), sp.hf.ans(s, a, r), sp.a("source"), sp.l([m])])])

# A Map's map, filter, mapWithKey, filterWithKey, foldr and foldrWithKey at
# such a lambda are the list's over its pairs, in order:
# fromDistinctAscList (hfH (toAscList m)), hfH the list function's recursion
# at the pairs' function (read time only: tab2's, when an IntMap is a Map)
def sp.hf.mg(+s: String, ts: List<&2, X.Sx>) -> X.Sx:
  sp.pc.tyapps(ts, sp.g(S.b("Data.Map.Internal"), S.b(s), "var"))

def sp.hf.tup(+k: X.Sx, +v: X.Sx) -> X.Sx:
  sp.tc(S.b("GHC.Tuple"), S.b("Tuple2"), [k, v])

# the function at a pair: \(k, v) -> (k, f v), f v, with the key f k v
def sp.hf.mapf(+pair: Bool, +key: Bool, +kt: X.Sx, +v: X.Sx, +ans: X.Sx, +f: X.Sx, +h: List<&2, U32>) -> X.Sx:
  +k = sp.hf.v("hfk", h)
  +e = sp.hf.v("hfv", h)
  +c = sp.hf.app(sp.if(X.Sx, key, _ => sp.hf.app(f, k), _ => f), e)
  +b = sp.if(X.Sx, pair, _ => sp.l([sp.a("tuple"), k, c]), _ => c)
  +p = sp.l([sp.a("ptuple"), sp.l([sp.hf.pv(k, kt), sp.hf.pv(e, v)])])
  sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([sp.hf.tup(kt, v)]), ans, sp.a("source"), sp.l([sp.hf.match([p], b)])])])

def sp.hf.map(+s: String, +key: Bool, +v: X.Sx, +w: X.Sx, +kt: X.Sx, +f: X.Sx, +m: X.Sx, +h: List<&2, U32>) -> X.Sx:
  +ism = sp.is(S.b(s), "map")
  +ans = sp.if(X.Sx, ism, _ => sp.hf.tup(kt, w), _ => sp.tc(S.b("GHC.Types"), S.b("Bool"), Nil{}))
  +l = sp.hf.app(sp.hf.mg("toAscList", [kt, v]), m)
  sp.hf.app(sp.hf.mg("fromDistinctAscList", [kt, w]), sp.hf.k1(s, sp.hf.tup(kt, v), sp.hf.tup(kt, w), sp.hf.mapf(ism, key, kt, v, ans, f, h), l, h))

# foldr's step at a pair: \(k, v) r -> f k v r
def sp.hf.mapfr(+key: Bool, +v: X.Sx, +r: X.Sx, +kt: X.Sx, +f: X.Sx, +z: X.Sx, +m: X.Sx, +h: List<&2, U32>, +sys: List<&2, Sy>) -> X.Sx:
  +l = sp.hf.app(sp.hf.mg("toAscList", [kt, v]), m)
  +k = sp.hf.v("hfk", h)
  +e = sp.hf.v("hfv", h)
  +a = sp.hf.v("hfr", h)
  +b = sp.hf.app(sp.hf.app(sp.if(X.Sx, key, _ => sp.hf.app(f, k), _ => f), e), a)
  +p = sp.l([sp.a("ptuple"), sp.l([sp.hf.pv(k, kt), sp.hf.pv(e, v)])])
  +g = {sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([sp.hf.tup(kt, v), r]), r, sp.a("source"), sp.l([sp.hf.match([p, sp.hf.pv(a, r)], b)])])]) : X.Sx}
  sp.hf.foldr(sp.hf.tup(kt, v), r, g, z, l, h, sp.hf.lam(g, 2n), sys)

# fromSet f s: fromDistinctAscList (hfH (toAscList s)), hfH at \k -> (k, f k)
def sp.hf.fromset(+k: X.Sx, +v: X.Sx, +f: X.Sx, +s: X.Sx, +h: List<&2, U32>) -> X.Sx:
  +x = sp.hf.v("hfk", h)
  +g = {sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l([k]), sp.hf.tup(k, v), sp.a("source"), sp.l([sp.hf.match([sp.hf.pv(x, k)], sp.l([sp.a("tuple"), x, sp.hf.app(f, x)]))])])]) : X.Sx}
  +l = sp.hf.app(sp.l([sp.a("tyapp"), sp.g(S.b("Data.Set.Internal"), S.b("toList"), "var"), k]), s)
  sp.hf.app(sp.hf.mg("fromDistinctAscList", [k, v]), sp.hf.k1("map", k, sp.hf.tup(k, v), g, l, h))

# Foldable's any, all, foldr, .. at a Set are the list's at its elements
def sp.hf.atset(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "Data.Set.Internal.Set"), Nat.is_eq(X.tsx.len(t), 3n))

def sp.hf.seq(at: Bool, +tys: List<&2, X.Sx>, +a: X.Sx, +l: X.Sx) -> X.Sx:
  sp.if(X.Sx, Bool.and(at, sp.hf.atset(tys)), _ => sp.hf.app(sp.l([sp.a("tyapp"), sp.g(S.b("Data.Set.Internal"), S.b("toList"), "var"), a]), l), _ => l)

# fmap and <$> at a Map
def sp.hf.atmap(+tys: List<&2, X.Sx>) -> Bool:
  +t = sp.first(tys)
  Bool.and(sp.is(sp.tckey(t), "Data.Map.Internal.Map"), Nat.is_eq(X.tsx.len(t), 4n))

def sp.hf.mk.of(k: Hk, +tys: List<&2, X.Sx>, +f: X.Sx, +x1: X.Sx, +x2: X.Sx, +n: Nat, +h: List<&2, U32>, +y: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  match k:
    case HkMap{+s, +key, +v, +w, +kt}:
      sp.if(X.Sx, Nat.is_eq(n, 2n), _ => sp.hf.map(s, key, sp.hf.ty(tys, v), sp.hf.ty(tys, w), sp.hf.ty(tys, kt), f, x1, h), _ => y)
    case HkFromSet{}:
      sp.if(X.Sx, Nat.is_eq(n, 2n), _ => sp.hf.fromset(sp.hf.ty(tys, 0n), sp.hf.ty(tys, 1n), f, x1, h), _ => y)
    case HkMapFoldr{+key, +v, +r, +kt}:
      sp.if(X.Sx, Nat.is_eq(n, 3n), _ => sp.hf.mapfr(key, sp.hf.ty(tys, v), sp.hf.ty(tys, r), sp.hf.ty(tys, kt), f, x1, x2, h, sys), _ => y)
    case Hk1{+s, +at, +a, +r}:
      +ls = Bool.or(Bool.not(at), Bool.or(sp.pc.atlist(tys), sp.hf.atset(tys)))
      sp.if(X.Sx, Bool.and(ls, Nat.is_eq(n, 2n)), _ => sp.hf.k1(s, sp.hf.ty(tys, a), sp.hf.ty(tys, r), f, sp.hf.seq(at, tys, sp.hf.ty(tys, a), x1), h), _ => sp.if(X.Sx, Bool.and(Bool.and(ls, Bool.not(Bool.and(at, sp.hf.atset(tys)))), Nat.is_eq(n, 1n)), _ => sp.hf.part(s, sp.hf.ty(tys, a), sp.hf.ty(tys, r), f, h), _ => sp.if(X.Sx, Bool.and(Bool.and(at, sp.is(S.b(s), "map")), Bool.and(Nat.is_eq(n, 2n), sp.hf.atmap(tys))), _ => sp.hf.map("map", False{}, sp.hf.ty(tys, 1n), sp.hf.ty(tys, 2n), sp.at(sp.first(tys), 3n), f, x1, h), _ => y)))
    case HkFoldr{+at}:
      +o = Bool.pick(Nat, at, 1n, 0n)
      sp.if(X.Sx, Bool.and(Nat.is_eq(n, 3n), Bool.or(Bool.not(at), Bool.or(sp.pc.atlist(tys), sp.hf.atset(tys)))), _ => sp.hf.foldr(sp.hf.ty(tys, o), sp.hf.ty(tys, 1n+o), f, x1, sp.hf.seq(at, tys, sp.hf.ty(tys, o), x2), h, sp.hf.lam(f, 2n), sys), _ => y)
    case HkFoldl{+at}:
      +o = Bool.pick(Nat, at, 1n, 0n)
      sp.if(X.Sx, Bool.and(Nat.is_eq(n, 3n), Bool.or(Bool.not(at), Bool.or(sp.pc.atlist(tys), sp.hf.atset(tys)))), _ => sp.hf.foldl(sp.hf.ty(tys, 1n+o), sp.hf.ty(tys, o), f, x1, sp.hf.seq(at, tys, sp.hf.ty(tys, 1n+o), x2), h, sp.hf.lam(f, 2n)), _ => y)
    case HkZip{}:
      sp.if(X.Sx, Nat.is_eq(n, 3n), _ => sp.hf.zip(sp.hf.ty(tys, 0n), sp.hf.ty(tys, 1n), sp.hf.ty(tys, 2n), f, x1, x2, h, sp.hf.lam(f, 2n)), _ => y)

def sp.hf.mk(k: Hk, +tys: List<&2, X.Sx>, +xs: List<&2, X.Sx>, +y: X.Sx, +sys: List<&2, Sy>) -> X.Sx:
  sp.hf.mk.of(k, tys, sp.pc.strip(sp.first(xs)), sp.hf.ty(xs, 1n), sp.hf.ty(xs, 2n), List.length(&2, X.Sx, xs), sp.hf.digits(y), y, sys)

def sp.hf.go(m: Maybe<&2, Hk>, +tys: List<&2, X.Sx>, +xs: List<&2, X.Sx>, +y: X.Sx, +fnp: Bool, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> X.Sx:
  match m:
    case Some{k}:
      +f = sp.pc.strip(sp.first(xs))
      +ok = {sp.if(Bool, Bool.or(sp.head.is(f, "lam"), sp.head.is(f, "app")), _ => sp.hf.free(sp.fa.frees(f, sp.fa.binds(f, Nil{}), Nil{}), env, sys), _ => sp.if(Bool, sp.head.is(f, "l"), _ => sp.hf.free([f], env, sys), _ => False{})) : Bool}
      sp.if(X.Sx, Bool.and(ok, Bool.not(Bool.and(fnp, Nat.is_eq(List.length(&2, X.Sx, xs), 1n)))), _ => sp.hf.mk(k, tys, xs, y, sys), _ => y)
    case None{}:
      y

def sp.hf.at(s: Bs, +y: X.Sx, +fnp: Bool, +env: List<&2, Asb>, +sys: List<&2, Sy>, +tab: List<&2, Hke>) -> X.Sx:
  match s:
    case Bs{+h, +xs}:
      +p = sp.pc.peel(h, Nil{}, Nil{})
      sp.hf.go(sp.hf.find(tab, sp.pc.key(p)), sp.pc.tys(p), xs, y, fnp, env, sys)

# bottom up: (app F A), its parts done (env: the top's binders with their
# types)
# (fnp: x is an application's function: the list comes after)
def sp.hf.w(x: X.Sx, +fnp: Bool, +env: List<&2, Asb>, +sys: List<&2, Sy>, +tab: List<&2, Hke>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{sp.hf.w(f, sp.is(a, "app"), env, sys, tab), X.SxCons{sp.hf.w(e, False{}, env, sys, tab), X.SxNil{}}}} : X.Sx}
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.hf.at(sp.beta.spine(y, Nil{}), y, fnp, env, sys, tab), _ => y)
    case X.SxCons{h, t}:
      X.SxCons{sp.hf.w(h, False{}, env, sys, tab), sp.hf.w(t, False{}, env, sys, tab)}
    case y:
      y

def sp.hf(+x: X.Sx, +env: List<&2, Asb>, +sys: List<&2, Sy>, +tab: List<&2, Hke>) -> X.Sx:
  sp.hf.w(x, False{}, env, sys, tab)

# the local functions (a let's, a where's) that use a value only the run
# has, each with a type variable for its type, as sp.hf.free reads one: a
# list function at one of them (`map render rows`) is the recursion too
def sp.hf.lets(x: X.Sx, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> List<&2, Asb>:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +rest = List.append(&2, Asb, sp.hf.lets(h, env, sys), sp.hf.lets(t, env, sys))
      +v = sp.if(X.Sx, sp.head.is(n, "fun"), _ => sp.fa.unself(sp.at(n, 1n)), _ => X.SxNil{})
      +m = sp.at(n, 4n)
      +use = sp.if(Bool, Bool.and(sp.head.is(v, "l"), Nat.is_gt(X.tsx.len(sp.at(m, 1n)), 0n)), _ => sp.hf.free(sp.fa.frees(m, sp.fa.binds(m, Nil{}), Nil{}), env, sys), _ => False{})
      Bool.pick(List<&2, Asb>, use, Asb{v, sp.l([sp.a("tv"), X.SxStr{S.b("%let")}])} <> rest, rest)
    case _:
      Nil{}

# (rounds, at most eight: a local function may use another that uses another
# ..: EAL's instantiateTemplate: shEq, shB, sh, shift)
def sp.hf.env.go(fuel: Nat, +x: X.Sx, +e0: List<&2, Asb>, +e: List<&2, Asb>, +sys: List<&2, Sy>) -> List<&2, Asb>:
  match fuel:
    case 0n:
      e
    case 1n+p:
      +e2 = List.append(&2, Asb, sp.hf.lets(x, e, sys), e0)
      sp.if(List<&2, Asb>, Nat.is_eq(List.length(&2, Asb, e2), List.length(&2, Asb, e)), _ => e, _ => sp.hf.env.go(p, x, e0, e2, sys))

def sp.hf.env(+x: X.Sx, +sys: List<&2, Sy>) -> List<&2, Asb>:
  +e0 = sp.fa.binds(x, Nil{})
  sp.hf.env.go(8n, x, e0, e0, sys)

# mapM, forM, traverse, for, mapM_, forM_, traverse_, for_ and foldM at a
# list and a function that uses a value only the run has (`forM xs (\x ->
# .. n ..)`, n a parameter): the prelude's (hs.state.mapm, hs.exs.mapm, ..)
# take a closed function, a template, so the call is cata's model's
# (Cata.Base's listForM, ..: sp.pc.gm's PgkH, at every monad), which rule 15
# copies with n a parameter. At a closed function it stays the prelude's.
type Hme is Data:
  Hme{key: String, i: Nat, n: Nat}

def sp.hm.tab() -> List<&2, Hme>:
  +tr = {"GHC.Internal.Data.Traversable." : String}
  +fo = {"GHC.Internal.Data.Foldable." : String}
  [Hme{tr ++ "traverse", 0n, 2n}, Hme{tr ++ "mapM", 0n, 2n}, Hme{tr ++ "for", 1n, 2n}, Hme{tr ++ "forM", 1n, 2n}, Hme{fo ++ "traverse_", 0n, 2n}, Hme{fo ++ "for_", 1n, 2n}, Hme{fo ++ "mapM_", 0n, 2n}, Hme{fo ++ "forM_", 1n, 2n}, Hme{"GHC.Internal.Control.Monad.foldM", 0n, 3n}]

def sp.hm.find(hs: List<&2, Hme>, +k: List<&2, U32>) -> Maybe<&2, Hme>:
  match hs:
    case Nil{}:
      None{}
    case Hme{+q, i, n} <> t:
      sp.if(Maybe<&2, Hme>, sp.is(k, q), _ => Some{Hme{q, i, n}}, _ => sp.hm.find(t, k))

# the head's global renamed to Cata.Hm's
def sp.hm.put(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+t, X.SxNil{}}}}:
      sp.if(X.Sx, Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp")), _ => sp.l([X.SxAtom{a}, sp.hm.put(f), t]), _ => sp.l([X.SxAtom{a}, f, t]))
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{+n}, X.SxCons{+k, X.SxNil{}}}}}:
      sp.l([X.SxAtom{a}, X.SxStr{S.b("Cata.Hm")}, X.SxStr{n}, sp.a("var")])
    case z:
      z

def sp.hm.apps(xs: List<&2, X.Sx>, f: X.Sx) -> X.Sx:
  match xs:
    case Nil{}:
      f
    case x <> t:
      sp.hm.apps(t, sp.l([sp.a("app"), f, x]))

def sp.hm.call(m: Maybe<&2, Hme>, +tys: List<&2, X.Sx>, +h: X.Sx, +xs: List<&2, X.Sx>, +y: X.Sx, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> X.Sx:
  match m:
    case Some{Hme{q, +i, n}}:
      +f = sp.pc.strip(sp.hf.ty(xs, i))
      +ok = {Bool.and(Bool.and(Nat.is_gt(List.length(&2, X.Sx, xs), i), Nat.is_le(List.length(&2, X.Sx, xs), n)), sp.pc.atlist(tys)) : Bool}
      +use = {sp.if(Bool, ok, _ => sp.if(Bool, Bool.or(sp.head.is(f, "lam"), Bool.or(sp.head.is(f, "app"), sp.head.is(f, "l"))), _ => sp.hf.free(sp.fa.frees(f, sp.fa.binds(f, Nil{}), Nil{}), env, sys), _ => False{}), _ => False{}) : Bool}
      sp.if(X.Sx, use, _ => sp.hm.apps(xs, sp.hm.put(h)), _ => y)
    case None{}:
      y

def sp.hm.at(s: Bs, +y: X.Sx, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> X.Sx:
  match s:
    case Bs{+h, +xs}:
      +p = sp.pc.peel(h, Nil{}, Nil{})
      sp.hm.call(sp.hm.find(sp.hm.tab(), sp.pc.key(p)), sp.pc.tys(p), h, xs, y, env, sys)

def sp.hm(x: X.Sx, +env: List<&2, Asb>, +sys: List<&2, Sy>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{sp.hm(f, env, sys), X.SxCons{sp.hm(e, env, sys), X.SxNil{}}}} : X.Sx}
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.hm.at(sp.beta.spine(y, Nil{}), y, env, sys), _ => y)
    case X.SxCons{h, t}:
      X.SxCons{sp.hm(h, env, sys), sp.hm(t, env, sys)}
    case y:
      y

# a binding's passes: pattern synonyms, views, copies' calls, normal type
# arguments
# A local named as one of the module's own defs that its top refers to
# (GHC's record update binds the new field's value to a local named as the
# field: freshInt's `st { esNextVar = esNextVar st + 1 }` then calls the
# selector esNextVar), which Bend would read as the local: renamed
# NAME_ID, its GHC unique after it, at each of its (l NAME ID).

# the names of cur's defs x refers to, (g CUR NAME ...)
def sp.lr.gs(x: X.Sx, +cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{+n}, rest}}}:
      +acc2 = sp.lr.gs(rest, cur, acc)
      Bool.pick(List<&2, List<&2, U32>>, Bool.and(sp.is(a, "g"), S.eq(m, cur)), n <> acc2, acc2)
    case X.SxCons{h, t}:
      sp.lr.gs(h, cur, sp.lr.gs(t, cur, acc))
    case _:
      acc

def sp.lr.id(i: X.Sx) -> List<&2, U32>:
  match i:
    case X.SxAtom{d}:
      d
    case _:
      S.b("l")

# x with each (l NAME ID) whose NAME is one of ns as (l NAME_ID ID), but a
# record construction's label, (field (l NAME ID) E) (FastMeter's <> builds
# one of the fields it selects)
def sp.lr.lab(isf: Bool, +l: X.Sx, l2: X.Sx) -> X.Sx:
  match isf:
    case True{}:
      l
    case False{}:
      l2

def sp.lr.rn(x: X.Sx, +ns: List<&2, List<&2, U32>>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxCons{+lh, +lt}, X.SxCons{e, X.SxNil{}}}}:
      X.SxCons{X.SxAtom{a}, X.SxCons{sp.lr.lab(sp.is(a, "field"), X.SxCons{lh, lt}, sp.lr.rn(X.SxCons{lh, lt}, ns)), X.SxCons{sp.lr.rn(e, ns), X.SxNil{}}}}
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+n}, X.SxCons{+i, X.SxNil{}}}}:
      Bool.pick(X.Sx, Bool.and(sp.is(a, "l"), S.mem(n, ns)), sp.l([X.SxAtom{a}, X.SxStr{List.concat(&2, U32, [n, S.b("_"), sp.lr.id(i)])}, i]), sp.l([X.SxAtom{a}, X.SxStr{n}, i]))
    case X.SxCons{h, t}:
      X.SxCons{sp.lr.rn(h, ns), sp.lr.rn(t, ns)}
    case u:
      u

def sp.lr(+x: X.Sx, +cur: List<&2, U32>) -> X.Sx:
  sp.lr.rn(x, sp.lr.gs(x, cur, Nil{}))

# Local groups ---------------------------------------------------------------------

# A group of local functions that call each other, as Machine's
# transformNoDefer writes its walk: c = f . c' . project, c' = \case s@(..)
# -> s; x -> fmap c x. The fold takes a local that calls itself, not a
# group. In a group of two or more, a member of no parameters whose type is
# a function takes its argument (c x = f (c' (project x)), the composition
# read as calls); then a member that does not name itself is written in the
# others' places (c' x as case x of its clauses, a bare c' as the lambda of
# them) and follows them as a group of its own, the others no longer
# calling it; until no such member is left. A group inside a local abs of
# no type variable and no dictionary (GHC's generalised group) keeps it,
# each part with the abs's exports of its members and its dictionaries'
# bindings.

# whether x is a reference to the local key
def sp.lg.isref(+x: X.Sx, +key: X.Sx) -> Bool:
  sp.eq(sp.lg.unself(x), key)

# whether x names the local key
def sp.lg.mentions(x: X.Sx, +key: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      Bool.or(sp.lg.isref(X.SxCons{h, t}, key), Bool.or(sp.lg.mentions(h, key), sp.lg.mentions(t, key)))
    case y:
      False{}

def sp.lg.np(+f: X.Sx) -> Nat:
  X.tsx.len(sp.at(sp.at(f, 4n), 1n))

# x with key's calls at one argument (one) case expressions of the clauses
# ms, its other uses the lambda of them
def sp.lg.sub(x: X.Sx, +key: X.Sx, +ms: X.Sx, +one: Bool) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}} : X.Sx}
      +call = Bool.and(Bool.and(sp.is(a, "app"), one), sp.lg.isref(f, key))
      sp.if(X.Sx, call, _ => sp.l([sp.a("case"), sp.lg.sub(e, key, ms, one), ms]), _ => sp.if(X.Sx, sp.lg.isref(y, key), _ => sp.l([sp.a("lam"), sp.a("single"), ms]), _ => X.SxCons{X.SxAtom{a}, X.SxCons{sp.lg.sub(f, key, ms, one), X.SxCons{sp.lg.sub(e, key, ms, one), X.SxNil{}}}}))
    case X.SxCons{+h, +t}:
      sp.if(X.Sx, sp.lg.isref(X.SxCons{h, t}, key), _ => sp.l([sp.a("lam"), sp.a("single"), ms]), _ => X.SxCons{sp.lg.sub(h, key, ms, one), sp.lg.sub(t, key, ms, one)})
    case y:
      y

def sp.lg.subs(xs: List<&2, X.Sx>, +key: X.Sx, +ms: X.Sx, +one: Bool) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      sp.lg.sub(h, key, ms, one) <> sp.lg.subs(t, key, ms, one)

# a member of no parameters, one bare right-hand side and a function type
# taking its argument: c = e is c eta_0 = e eta_0, a composition in e
# read as calls
def sp.lg.eta(+f: X.Sx) -> X.Sx:
  +ms = sp.at(f, 4n)
  +ty = sp.at(ms, 2n)
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +gs = sp.at(sp.at(m0, 2n), 1n)
  +g0 = sp.first(sp.els(gs))
  +one = Bool.and(Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 0n), Nat.is_eq(X.tsx.len(sp.at(ms, 4n)), 1n)), Bool.and(Nat.is_eq(X.tsx.len(gs), 1n), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(sp.at(m0, 2n), 2n), sp.l([sp.a("binds")])))))
  +fn = Bool.and(sp.head.is(ty, "tfun"), sp.head.is(f, "fun"))
  +v = sp.l([sp.a("l"), X.SxStr{S.b("eta_0")}, sp.a("0")])
  +body = sp.lg.dot(8n, sp.l([sp.a("app"), sp.at(g0, 2n), v]))
  +gr = sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, body])]), sp.l([sp.a("binds")])])
  +ms2 = sp.l([sp.a("matches"), sp.l([sp.at(ty, 1n)]), sp.at(ty, 2n), sp.at(ms, 3n), sp.l([sp.l([sp.a("match"), sp.l([sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, sp.at(ty, 1n)])])]), gr])])])
  Bool.pick(X.Sx, Bool.and(one, fn), sp.l([sp.at(f, 0n), sp.at(f, 1n), sp.at(f, 2n), sp.at(f, 3n), ms2, sp.at(f, 5n)]), f)

def sp.lg.etas(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      sp.lg.eta(h) <> sp.lg.etas(t)

# the first member (of two or more) with parameters that does not name
# itself, and the others
def sp.lg.pick(xs: List<&2, X.Sx>, +pre: List<&2, X.Sx>) -> Maybe<&2, Sigma<&2, &2, X.Sx, _ => List<&2, X.Sx>>>:
  match xs:
    case Nil{}:
      None{}
    case +h <> +t:
      +ok = Bool.and(sp.head.is(h, "fun"), Bool.and(Nat.is_gt(sp.lg.np(h), 0n), Bool.not(sp.lg.mentions(sp.at(h, 4n), sp.lg.key(h)))))
      sp.if(Maybe<&2, Sigma<&2, &2, X.Sx, _ => List<&2, X.Sx>>>, ok, _ => Some{(h, List.append(&2, X.Sx, pre, t))}, _ => sp.lg.pick(t, List.append(&2, X.Sx, pre, [h])))

def sp.lg.split.at(n: Nat, m: Maybe<&2, Sigma<&2, &2, X.Sx, _ => List<&2, X.Sx>>>, rest: List<&2, X.Sx>, outs: List<&2, X.Sx>) -> Sigma<&2, &2, List<&2, X.Sx>, _ => List<&2, X.Sx>>:
  match n m:
    case 1n+k Some{(+b, others)}:
      +key = sp.lg.key(b)
      +ms = sp.at(b, 4n)
      +one = Nat.is_eq(sp.lg.np(b), 1n)
      +rest2 = sp.lg.subs(others, key, ms, one)
      +big = Nat.is_gt(List.length(&2, X.Sx, rest2), 1n)
      sp.lg.split.at(k, Bool.pick(Maybe<&2, Sigma<&2, &2, X.Sx, _ => List<&2, X.Sx>>>, big, sp.lg.pick(rest2, Nil{}), None{}), rest2, List.append(&2, X.Sx, sp.lg.subs(outs, key, ms, one), [b]))
    case _ _:
      (rest, outs)

# the members left in the group and those out of it (in order), n at most
def sp.lg.split(n: Nat, +rest: List<&2, X.Sx>, outs: List<&2, X.Sx>) -> Sigma<&2, &2, List<&2, X.Sx>, _ => List<&2, X.Sx>>:
  +big = Nat.is_gt(List.length(&2, X.Sx, rest), 1n)
  sp.lg.split.at(n, Bool.pick(Maybe<&2, Sigma<&2, &2, X.Sx, _ => List<&2, X.Sx>>>, big, sp.lg.pick(rest, Nil{}), None{}), rest, outs)

def sp.lg.anykey(fs: List<&2, X.Sx>, +k: X.Sx) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> t:
      Bool.or(sp.eq(sp.lg.key(f), k), sp.lg.anykey(t, k))

# the exports of an abs that are the members'
def sp.lg.exps(es: List<&2, X.Sx>, +fs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      +k = sp.lg.unself(sp.at(e, 1n))
      +rest = sp.lg.exps(t, fs)
      Bool.pick(List<&2, X.Sx>, sp.lg.anykey(fs, k), e <> rest, rest)

# a part as a group: (rec ..) or (nonrec ..), in the abs when there is one
def sp.lg.part(+tag: String, +fs: List<&2, X.Sx>, +abs: Maybe<&2, X.Sx>) -> X.Sx:
  match abs:
    case Some{+a}:
      sp.l([sp.a(tag), sp.l([sp.at(a, 0n), sp.at(a, 1n), sp.at(a, 2n), sp.l(sp.lg.exps(sp.els(sp.at(a, 3n)), fs)), sp.at(a, 4n), sp.l(fs), sp.at(a, 6n)])])
    case None{}:
      sp.l(sp.a(tag) <> fs)

def sp.lg.nonrecs(fs: List<&2, X.Sx>, +abs: Maybe<&2, X.Sx>) -> List<&2, X.Sx>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> t:
      sp.lg.part("nonrec", [f], abs) <> sp.lg.nonrecs(t, abs)

def sp.lg.out(r: Sigma<&2, &2, List<&2, X.Sx>, _ => List<&2, X.Sx>>, +abs: Maybe<&2, X.Sx>, g: X.Sx) -> List<&2, X.Sx>:
  match r:
    case (rest, Nil{}):
      [g]
    case (rest, outs):
      sp.lg.part("rec", rest, abs) <> sp.lg.nonrecs(outs, abs)

# a group's members, and its abs when they are inside one (no type
# variable, no dictionary)
def sp.lg.abs(+g: X.Sx) -> Maybe<&2, X.Sx>:
  +a = sp.at(g, 1n)
  +ok = Bool.and(Bool.and(Nat.is_eq(X.tsx.len(g), 2n), sp.head.is(a, "abs")), Bool.and(Nat.is_eq(X.tsx.len(sp.at(a, 1n)), 0n), Nat.is_eq(X.tsx.len(sp.at(a, 2n)), 0n)))
  Bool.pick(Maybe<&2, X.Sx>, ok, Some{a}, None{})

def sp.lg.group.of(+g: X.Sx, +abs: Maybe<&2, X.Sx>) -> List<&2, X.Sx>:
  +fs = Bool.pick(List<&2, X.Sx>, Maybe.is_some(&2, X.Sx, abs), sp.els(sp.at(sp.or(abs, X.SxNil{}), 5n)), sp.dropn(sp.els(g), 1n))
  +n = List.length(&2, X.Sx, fs)
  sp.if(List<&2, X.Sx>, Nat.is_gt(n, 1n), _ => sp.lg.out(sp.lg.split(n, sp.lg.etas(fs), Nil{}), abs, g), _ => [g])

def sp.fl.snoc0(+xs: X.Sx, +y: X.Sx) -> X.Sx:
  sp.l(List.append(&2, X.Sx, sp.els(xs), [y]))

# xs with y sixth
def sp.le.at5(xs: List<&2, X.Sx>, +y: X.Sx) -> List<&2, X.Sx>:
  match xs:
    case a <> b <> c <> d <> e <> f <> t:
      a <> b <> c <> d <> e <> y <> t
    case u:
      u

# A local that is no group: one of no parameters whose type is a function
# and whose right-hand side is a call or a name (ind = indent 2, merge =
# Map.unionWith f), no where, takes its arguments (ind x = indent 2 x): a
# let of a closure, which Bend uses at most once and a template cannot name,
# is then a local function, lifted as any is. The parameters are named
# after it (NAME_e0, ..).
def sp.le.v(+f: X.Sx, +i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{List.concat(&2, U32, [sp.sat(sp.lg.key(f), 1n), S.b("_e"), S.b(Nat.show(i))])}, sp.a("0")])

# f (its one clause plain) with a parameter more
def sp.le.add(+f: X.Sx, +i: Nat) -> X.Sx:
  +ms = sp.at(f, 4n)
  +ty = sp.at(ms, 2n)
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +g0 = sp.first(sp.els(sp.at(sp.at(m0, 2n), 1n)))
  +v = sp.le.v(f, i)
  +y = sp.l([sp.a("app"), sp.at(g0, 2n), v])
  +body = sp.if(X.Sx, Nat.is_eq(i, 0n), _ => sp.lg.dot(8n, y), _ => y)
  +gr = sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, body])]), sp.l([sp.a("binds")])])
  +ps = sp.fl.snoc0(sp.at(m0, 1n), sp.l([sp.a("pvar"), sp.l([sp.a("bv"), v, sp.at(ty, 1n)])]))
  +ms2 = sp.l([sp.a("matches"), sp.fl.snoc0(sp.at(ms, 1n), sp.at(ty, 1n)), sp.at(ty, 2n), sp.at(ms, 3n), sp.l([sp.l([sp.a("match"), ps, gr])])])
  sp.l([sp.at(f, 0n), sp.at(f, 1n), sp.at(f, 2n), sp.at(f, 3n), ms2, sp.at(f, 5n)])

def sp.le.go(n: Nat, +i: Nat, +f: X.Sx) -> X.Sx:
  match n:
    case 0n:
      f
    case 1n+k:
      sp.if(X.Sx, sp.head.is(sp.at(sp.at(f, 4n), 2n), "tfun"), _ => sp.le.go(k, 1n+i, sp.le.add(f, i)), _ => f)

def sp.le.fun(+f: X.Sx) -> X.Sx:
  +ms = sp.at(f, 4n)
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +gr = sp.at(m0, 2n)
  +g0 = sp.first(sp.els(sp.at(gr, 1n)))
  +e = sp.pc.strip(sp.at(g0, 2n))
  +one = Bool.and(Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 0n), Nat.is_eq(X.tsx.len(sp.at(ms, 4n)), 1n)), Bool.and(Nat.is_eq(X.tsx.len(sp.at(gr, 1n)), 1n), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")])))))
  +hd = sp.pc.strip(sp.spine.head(e))
  +call = Bool.and(Bool.or(Bool.or(sp.head.is(e, "app"), sp.head.is(e, "g")), Bool.or(sp.head.is(e, "tyapp"), sp.head.is(e, "evapp"))), Bool.or(sp.head.is(hd, "g"), sp.head.is(hd, "l")))
  sp.if(X.Sx, Bool.and(Bool.and(sp.head.is(f, "fun"), sp.head.is(sp.at(ms, 2n), "tfun")), Bool.and(one, call)), _ => sp.le.go(3n, 0n, f), _ => f)

# (nonrec F), or (nonrec (abs () () EXPORTS EVBINDS (F) ..))
def sp.le(+g: X.Sx) -> X.Sx:
  +a = sp.at(g, 1n)
  +ab = Maybe.is_some(&2, X.Sx, sp.lg.abs(g))
  +fs = sp.at(a, 5n)
  +one = Bool.and(ab, Nat.is_eq(X.tsx.len(fs), 1n))
  sp.if(X.Sx, sp.head.is(a, "fun"), _ => sp.l([sp.a("nonrec"), sp.le.fun(a)]), _ => sp.if(X.Sx, one, _ => sp.l([sp.a("nonrec"), sp.l(sp.le.at5(sp.els(a), sp.l([sp.le.fun(sp.first(sp.els(fs)))])))]), _ => g))

def sp.lg.group(+g: X.Sx) -> List<&2, X.Sx>:
  sp.if(List<&2, X.Sx>, sp.head.is(g, "rec"), _ => sp.lg.group.of(g, sp.lg.abs(g)), _ => sp.if(List<&2, X.Sx>, Bool.and(sp.head.is(g, "nonrec"), Nat.is_eq(X.tsx.len(g), 2n)), _ => [sp.le(g)], _ => [g]))

def sp.lg.groups(gs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      List.append(&2, X.Sx, sp.lg.group(g), sp.lg.groups(t))

# bottom up: each (binds G..) with its groups split
def sp.lg(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, t}:
      +t2 = sp.lg(t)
      sp.if(X.Sx, sp.is(a, "binds"), _ => sp.l(X.SxAtom{a} <> sp.lg.groups(sp.els(t2))), _ => X.SxCons{X.SxAtom{a}, t2})
    case X.SxCons{h, t}:
      X.SxCons{sp.lg(h), sp.lg(t)}
    case y:
      y

# A local function of one plain clause that takes a class's dictionary
# (Meter's unhandled, Show's) is its lambda where it is used, at the types
# there, and so is one that takes a function (EAL's
# instantiateTemplate: shKV f (k, v) = (sh k, f v), polymorphic) is its
# lambda where it is used: a local function's function parameter is a
# template, which a function over run-time locals (shKV shTau) is not.
type Lh is Data:
  Lh{v: X.Sx, tvs: List<&2, List<&2, U32>>, ms: X.Sx}

def sp.lh.hasfn(ts: List<&2, X.Sx>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> r:
      Bool.or(sp.head.is(t, "tfun"), sp.lh.hasfn(r))

# a polymorphic one (EAL's blockOf :: Map Int a -> [(Int, a)]) whose body
# names a local of outside: lifted out of its def it would take both
def sp.lh.poly(tvs: List<&2, List<&2, U32>>, +ms: X.Sx) -> Bool:
  match tvs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.not(List.is_empty(&2, X.Sx, sp.fa.frees(ms, sp.fa.binds(ms, Nil{}), Nil{})))

# a fun as one of them
def sp.lh.fun(dict: Bool, +v: X.Sx, +tvs: List<&2, List<&2, U32>>, +f: X.Sx, +acc: List<&2, Lh>) -> List<&2, Lh>:
  +ms = sp.at(f, 4n)
  +cs = sp.els(sp.at(ms, 4n))
  +m0 = sp.first(cs)
  +gr = sp.at(m0, 2n)
  +g0 = sp.first(sp.els(sp.at(gr, 1n)))
  +one = Bool.and(Bool.and(Nat.is_eq(List.length(&2, X.Sx, cs), 1n), Nat.is_eq(X.tsx.len(sp.at(gr, 1n)), 1n)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")]))))
  +ok = Bool.and(Bool.and(sp.head.is(f, "fun"), sp.head.is(v, "l")), Bool.and(one, Bool.or(Bool.and(Bool.or(dict, sp.lh.poly(tvs, ms)), Nat.is_gt(X.tsx.len(sp.at(ms, 1n)), 0n)), sp.lh.hasfn(sp.els(sp.at(ms, 1n))))))
  Bool.pick(List<&2, Lh>, Bool.and(ok, Bool.not(sp.lg.mentions(ms, v))), Lh{v, tvs, ms} <> acc, acc)

# the type variables of a local function with a signature: its abs has none,
# its type says them (tforall "a" T)
def sp.lh.fas(t: X.Sx) -> List<&2, List<&2, U32>>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{v}, X.SxCons{r, _}}}:
      sp.if(List<&2, List<&2, U32>>, sp.is(a, "tforall"), _ => v <> sp.lh.fas(r), _ => Nil{})
    case u:
      Nil{}

def sp.lh.tvs(+a: X.Sx, +es: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  +ts = sp.strs(sp.at(a, 1n))
  Bool.pick(List<&2, List<&2, U32>>, List.is_empty(&2, List<&2, U32>, ts), sp.lh.fas(sp.at(sp.first(es), 2n)), ts)

def sp.lh.grp(+g: X.Sx, +acc: List<&2, Lh>) -> List<&2, Lh>:
  +a = sp.at(g, 1n)
  +fs = sp.els(sp.at(a, 5n))
  +es = sp.els(sp.at(a, 3n))
  +dict = Bool.not(sp.eq(sp.at(a, 2n), X.SxNil{}))
  +ev = Bool.and(Nat.is_eq(List.length(&2, X.Sx, fs), 1n), Nat.is_eq(List.length(&2, X.Sx, es), 1n))
  sp.if(List<&2, Lh>, Bool.not(Nat.is_eq(X.tsx.len(g), 2n)), _ => acc, _ => sp.if(List<&2, Lh>, sp.head.is(a, "fun"), _ => sp.lh.fun(False{}, sp.fa.unself(sp.at(a, 1n)), Nil{}, a, acc), _ => sp.if(List<&2, Lh>, Bool.and(sp.head.is(a, "abs"), ev), _ => sp.lh.fun(dict, sp.at(sp.first(es), 1n), sp.lh.tvs(a, es), sp.first(fs), acc), _ => acc)))

def sp.lh.of(x: X.Sx, +acc: List<&2, Lh>) -> List<&2, Lh>:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +acc2 = sp.if(List<&2, Lh>, sp.is(X.tsx.atom.of(h), "nonrec"), _ => sp.lh.grp(n, acc), _ => acc)
      sp.lh.of(t, sp.lh.of(h, acc2))
    case _:
      acc

def sp.lh.find(hs: List<&2, Lh>, +v: X.Sx) -> Maybe<&2, Lh>:
  match hs:
    case Nil{}:
      None{}
    case Lh{+w, tvs, ms} <> t:
      sp.if(Maybe<&2, Lh>, sp.eq(w, v), _ => Some{Lh{w, tvs, ms}}, _ => sp.lh.find(t, v))

def sp.lh.lam(m: Maybe<&2, Lh>, +tys: List<&2, X.Sx>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Lh{v, +tvs, ms}}:
      Bool.pick(X.Sx, Nat.is_eq(List.length(&2, X.Sx, tys), List.length(&2, List<&2, U32>, tvs)), sp.l([sp.a("lam"), sp.a("single"), sp.subst(ms, sp.zip(tvs, tys))]), x)
    case None{}:
      x

# a use's lambda given its function (shKV (fmap shInfo)): the lambda of its
# other parameters, the function in the first one's place (a variable), so
# that what the function is given is read in its body (fmap shInfo v)
def sp.lh.give(+lam: X.Sx, +a: X.Sx) -> Maybe<&2, X.Sx>:
  +ms = sp.at(lam, 2n)
  +ts = sp.els(sp.at(ms, 1n))
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +ps = sp.els(sp.at(m0, 1n))
  +p0 = sp.first(ps)
  +v = sp.at(sp.at(p0, 1n), 1n)
  +ok = Bool.and(Bool.and(sp.head.is(lam, "lam"), Nat.is_gt(List.length(&2, X.Sx, ts), 1n)), Bool.and(sp.head.is(p0, "pvar"), sp.head.is(sp.first(ts), "tfun")))
  +m = sp.l([sp.a("match"), sp.l(sp.dropn(ps, 1n)), sp.beta.sub(sp.at(m0, 2n), v, a)])
  +ms2 = sp.l([sp.a("matches"), sp.l(sp.dropn(ts, 1n)), sp.at(ms, 2n), sp.at(ms, 3n), sp.l([m])])
  Bool.pick(Maybe<&2, X.Sx>, ok, Some{sp.l([sp.a("lam"), sp.a("single"), ms2])}, None{})

def sp.lh.app(+f: X.Sx, +a: X.Sx) -> X.Sx:
  +m = sp.if(Maybe<&2, X.Sx>, sp.head.is(f, "lam"), _ => sp.lh.give(f, a), _ => None{})
  sp.or(m, sp.l([sp.a("app"), f, a]))

# the uses (a local, its type arguments around it) in x; a binder stays
def sp.lh.sub(x: X.Sx, +hs: List<&2, Lh>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+p, +t}}:
      +n = {X.SxCons{X.SxAtom{a}, X.SxCons{p, t}} : X.Sx}
      +isl = Bool.or(sp.is(a, "l"), Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp")))
      +hd = sp.if(X.Sx, isl, _ => sp.vhead(n), _ => X.SxNil{})
      +m = sp.if(Maybe<&2, Lh>, sp.head.is(hd, "l"), _ => sp.lh.find(hs, hd), _ => None{})
      +bind = Bool.or(sp.is(a, "fun"), Bool.or(sp.is(a, "export"), sp.is(a, "self")))
      +pu = sp.if(Bool, Bool.and(sp.is(a, "app"), sp.head.is(sp.vhead(p), "l")), _ => Maybe.is_some(&2, Lh, sp.lh.find(hs, sp.vhead(p))), _ => False{})
      sp.if(X.Sx, Maybe.is_some(&2, Lh, m), _ => sp.lh.lam(m, sp.spine.tys(n, Nil{}), n), _ => sp.if(X.Sx, bind, _ => X.SxCons{X.SxAtom{a}, X.SxCons{p, sp.lh.sub(t, hs)}}, _ => sp.if(X.Sx, pu, _ => sp.lh.app(sp.lh.sub(p, hs), sp.first(sp.els(sp.lh.sub(t, hs)))), _ => X.SxCons{X.SxAtom{a}, X.SxCons{sp.lh.sub(p, hs), sp.lh.sub(t, hs)}})))
    case X.SxCons{h, t}:
      X.SxCons{sp.lh.sub(h, hs), sp.lh.sub(t, hs)}
    case y:
      y

def sp.lh.go(n: Nat, +x: X.Sx, +hs: List<&2, Lh>) -> X.Sx:
  match n:
    case 0n:
      x
    case 1n+p:
      sp.lh.go(p, sp.lh.sub(x, hs), hs)

# a function all of whose uses are its lambda now goes
def sp.lh.isv(+g: X.Sx, +v: X.Sx) -> Bool:
  +a = sp.at(g, 1n)
  +w = sp.if(X.Sx, sp.head.is(a, "fun"), _ => sp.fa.unself(sp.at(a, 1n)), _ => sp.at(sp.first(sp.els(sp.at(a, 3n))), 1n))
  Bool.and(sp.head.is(g, "nonrec"), sp.eq(w, v))

def sp.lh.less(gs: List<&2, X.Sx>, +v: X.Sx) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case +g <> t:
      +rest = sp.lh.less(t, v)
      Bool.pick(List<&2, X.Sx>, sp.lh.isv(g, v), rest, g <> rest)

def sp.lh.drop(x: X.Sx, +v: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, t}:
      +t2 = sp.lh.drop(t, v)
      sp.if(X.Sx, sp.is(a, "binds"), _ => X.SxCons{X.SxAtom{a}, sp.l(sp.lh.less(sp.els(t2), v))}, _ => X.SxCons{X.SxAtom{a}, t2})
    case X.SxCons{h, t}:
      X.SxCons{sp.lh.drop(h, v), sp.lh.drop(t, v)}
    case y:
      y

def sp.lh.drops(hs: List<&2, Lh>, +x: X.Sx) -> X.Sx:
  match hs:
    case Nil{}:
      x
    case Lh{+v, tvs, ms} <> t:
      +y = sp.lh.drop(x, v)
      sp.lh.drops(t, sp.if(X.Sx, sp.lg.mentions(y, v), _ => x, _ => y))

# twice: one's body may use another
def sp.lh(+x: X.Sx) -> X.Sx:
  +hs = sp.lh.of(x, Nil{})
  sp.if(X.Sx, List.is_empty(&2, Lh, hs), _ => x, _ => sp.lh.drops(hs, sp.lh.go(2n, x, hs)))

# A local value that may fail (maximum .., head ..) used only inside local
# functions and lambdas (Certificate's width, used by what maps over the
# rows) is forced there, if at all: it is read at its uses, so that the
# fold's bind of it is there too.
type Lz is Data:
  Lz{v: X.Sx, e: X.Sx}

def sp.lz.part(x: X.Sx, +ns: List<&2, List<&2, U32>>) -> Bool:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      sp.if(Bool, sp.is(a, "g"), _ => S.mem(sp.sat(X.SxCons{X.SxAtom{a}, t}, 2n), ns), _ => sp.lz.part(t, ns))
    case X.SxCons{h, t}:
      Bool.or(sp.lz.part(h, ns), sp.lz.part(t, ns))
    case y:
      False{}

def sp.lz.names() -> List<&2, List<&2, U32>>:
  sp.strs0(["maximum", "minimum", "maximumBy", "minimumBy", "head", "last", "tail", "init", "foldr1", "foldl1", "fromJust", "!!", "!", "intMapAt", "error", "undefined"])

def sp.lz.evl(gs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      List.append(&2, X.Sx, sp.dropn(sp.els(g), 1n), sp.lz.evl(t))

# a value's dictionaries' terms in their places (twice: one may use another)
def sp.lz.evs(es: List<&2, X.Sx>, +e: X.Sx) -> X.Sx:
  match es:
    case Nil{}:
      e
    case +b <> t:
      sp.lz.evs(t, sp.beta.sub(e, sp.at(sp.at(b, 1n), 1n), sp.at(b, 2n)))

def sp.lz.fun(+v: X.Sx, +f: X.Sx, +evs: List<&2, X.Sx>, +acc: List<&2, Lz>) -> List<&2, Lz>:
  +ms = sp.at(f, 4n)
  +cs = sp.els(sp.at(ms, 4n))
  +m0 = sp.first(cs)
  +gr = sp.at(m0, 2n)
  +g0 = sp.first(sp.els(sp.at(gr, 1n)))
  +e0 = sp.at(g0, 2n)
  +one = Bool.and(Bool.and(Nat.is_eq(List.length(&2, X.Sx, cs), 1n), Nat.is_eq(X.tsx.len(sp.at(gr, 1n)), 1n)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")]))))
  +ok = Bool.and(Bool.and(sp.head.is(v, "l"), one), Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 1n)), 0n), sp.lz.part(e0, sp.lz.names())))
  sp.if(List<&2, Lz>, Bool.and(ok, Bool.not(sp.lg.mentions(e0, v))), _ => Lz{v, sp.lz.evs(evs, sp.lz.evs(evs, e0))} <> acc, _ => acc)

# (abs () () (exports) (evbinds..) (fun)): a value alone in its group
def sp.lz.grp(+a: X.Sx, +acc: List<&2, Lz>) -> List<&2, Lz>:
  +fs = sp.els(sp.at(a, 5n))
  +es = sp.els(sp.at(a, 3n))
  +evs = sp.lz.evl(sp.els(sp.at(a, 4n)))
  +mono = Bool.and(sp.eq(sp.at(a, 1n), X.SxNil{}), sp.eq(sp.at(a, 2n), X.SxNil{}))
  +one = Bool.and(Nat.is_eq(List.length(&2, X.Sx, fs), 1n), Nat.is_eq(List.length(&2, X.Sx, es), 1n))
  sp.if(List<&2, Lz>, sp.head.is(a, "fun"), _ => sp.lz.fun(sp.fa.unself(sp.at(a, 1n)), a, Nil{}, acc), _ => sp.if(List<&2, Lz>, Bool.and(sp.head.is(a, "abs"), Bool.and(mono, one)), _ => sp.lz.fun(sp.at(sp.first(es), 1n), sp.first(fs), evs, acc), _ => acc))

def sp.lz.of(x: X.Sx, +acc: List<&2, Lz>) -> List<&2, Lz>:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +acc2 = sp.if(List<&2, Lz>, sp.is(X.tsx.atom.of(h), "nonrec"), _ => sp.lz.grp(sp.at(n, 1n), acc), _ => acc)
      sp.lz.of(t, sp.lz.of(h, acc2))
    case _:
      acc

# a use of v outside every lambda and local function
def sp.lz.out(x: X.Sx, +v: X.Sx) -> Bool:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      +n = {X.SxCons{X.SxAtom{a}, t} : X.Sx}
      +self = sp.at(n, 1n)
      +fn = Bool.and(sp.is(a, "fun"), Bool.and(sp.head.is(sp.fa.unself(self), "l"), Bool.or(sp.eq(sp.fa.unself(self), v), Nat.is_gt(X.tsx.len(sp.at(sp.at(n, 4n), 1n)), 0n))))
      +skip = Bool.or(sp.is(a, "lam"), Bool.or(fn, Bool.or(sp.is(a, "export"), sp.is(a, "self"))))
      sp.if(Bool, sp.eq(n, v), _ => True{}, _ => sp.if(Bool, skip, _ => False{}, _ => sp.lz.out(t, v)))
    case X.SxCons{h, t}:
      Bool.or(sp.lz.out(h, v), sp.lz.out(t, v))
    case y:
      False{}

def sp.lz.first(ls: List<&2, Lz>, +x: X.Sx) -> Maybe<&2, Lz>:
  match ls:
    case Nil{}:
      None{}
    case Lz{+v, e} <> t:
      sp.if(Maybe<&2, Lz>, sp.lz.out(x, v), _ => sp.lz.first(t, x), _ => Some{Lz{v, e}})

def sp.lz.one(m: Maybe<&2, Lz>, +x: X.Sx, k: X.Sx -> X.Sx) -> X.Sx:
  match m:
    case Some{Lz{+v, e}}:
      k(sp.beta.sub(sp.lh.drop(x, v), v, e))
    case None{}:
      x

# one at a time (another's value may use it; fuel)
def sp.lz.go(n: Nat, +x: X.Sx) -> X.Sx:
  match n:
    case 0n:
      x
    case 1n+p:
      sp.lz.one(sp.lz.first(sp.lz.of(x, Nil{}), x), x, y => sp.lz.go(p, y))

def sp.lz(+x: X.Sx) -> X.Sx:
  sp.lz.go(8n, x)

# show at a known showsPrec, applied (the prelude's showVia sp v): sp 0 v "",
# and showList (showListVia sp vs): the model's showListWith sp 0 vs.  The
# showsPrec is then called, not a template of the prelude's: a type that
# holds itself through another's Show (ShowCof) is a group of calls.
def sp.sv.zero() -> X.Sx:
  sp.l([sp.a("olit"), sp.l([sp.a("int"), sp.a("0")]), sp.l([sp.a("tc"), X.SxStr{S.b("HsPrelude")}, X.SxStr{S.b("HsInt")}]), sp.l([sp.a("int"), sp.a("0")])])

def sp.sv.at(+f: X.Sx, +v: X.Sx, +hb: Bool) -> X.Sx:
  +sf = sp.pc.strip(f)
  +h = sp.at(sf, 1n)
  +k = sp.gkey(sp.vhead(h))
  +s = sp.at(sf, 2n)
  +app = sp.head.is(sf, "app")
  +d = sp.l([sp.a("app"), sp.l([sp.a("app"), s, sp.sv.zero()]), v])
  +lw = sp.l([sp.a("tyapp"), sp.g(S.b("Cata.Base"), S.b("showListWith"), "var"), sp.at(h, 2n)])
  sp.if(X.Sx, Bool.and(app, sp.is(k, "HsPrelude.Z.showVia")), _ => sp.l([sp.a("app"), d, sp.l([sp.a("string"), X.SxStr{Nil{}}])]), _ => sp.if(X.Sx, Bool.and(Bool.and(app, hb), Bool.and(sp.is(k, "HsPrelude.Z.showListVia"), sp.head.is(h, "tyapp"))), _ => sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), lw, s]), sp.sv.zero()]), v]), _ => sp.l([sp.a("app"), f, v])))

# bottom up
def sp.sv(x: X.Sx, +hb: Bool) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +f2 = sp.sv(f, hb)
      +e2 = sp.sv(e, hb)
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.sv.at(f2, e2, hb), _ => X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}})
    case X.SxCons{h, t}:
      X.SxCons{sp.sv(h, hb), sp.sv(t, hb)}
    case y:
      y

def sp.rw.sv(r: Rw, +hb: Bool) -> Rw:
  match r:
    case Rw{x, q}:
      Rw{sp.sv(x, hb), q}

def sp.passes0(+x: X.Sx, +cur: List<&2, U32>, +ix: Ix, +rl0: List<&2, X.Sx>, +ol0: List<&2, Og>, +kn: List<&2, Rq>, +rg: List<&2, X.Sx>) -> Rw:
  +xr = sp.lr(sp.lh(sp.lz(sp.lec(x))), cur)
  +xl = sp.lc(xr, sp.fa.binds(xr, Nil{}), sp.ix.cts(ix))
  +xm = sp.if(X.Sx, sp.ix.hasgen(ix), _ => sp.hm(xl, sp.hf.env(xl, sp.ix.sys(ix)), sp.ix.sys(ix)), _ => xl)
  +xq = sp.pl(sp.pc(xm, sp.ix.hasbase(ix), ix), sp.pl.toptvs(x), ix)
  +xp = sp.ifl(sp.beta(sp.hf(xq, sp.hf.env(xq, sp.ix.sys(ix)), sp.ix.sys(ix), sp.hf.tab()), sp.ix.sys(ix)))
  +x0 = sp.lg(sp.p0(xp, sp.isfun(xp)))
  +y = sp.p1(64n, x0, sp.p1k(x0, ix), ix)
  sp.rw.p10(sp.rw.p9(sp.rw.p7(sp.rw.sv(sp.p4(sp.p8(sp.p3(y, sp.ispv(y), ix), False{}), True{}, cur, ix), sp.ix.hasbase2(ix)), ix)), cur, ix, rl0, ol0, kn, rg)

# Local copies ----------------------------------------------------------------
# A copy whose known argument names a recursive local (sp.fa.sl: a where's
# or a let's group member) is a member of that group, (l NAME 0): the
# copy's own recursion through the argument is then the group's (EAL's
# selfReferential: classIfaces hands tau to firstJustM), which the fold
# writes with fuel, not a closure over a recursive def (rec-value before).
# The copy is the def at its types (sp.fa.copy.of) through the passes, its
# var then the local; its own asks go on (a copy at another group's member
# waits for the top that has the group).
def sp.fl.isfl(r: Rq) -> Bool:
  match r:
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys}:
      True{}
    case Rq{n, LoFlm{nm, m, j, mtys, fas, fvt, gv, rg}, tys}:
      True{}
    case _:
      False{}

def sp.fl.gv(r: Rq) -> X.Sx:
  match r:
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys}:
      gv
    case Rq{n, LoFlm{nm, m, j, mtys, fas, fvt, gv, rg}, tys}:
      gv
    case _:
      X.SxNil{}

def sp.rq.rg(r: Rq) -> List<&2, X.Sx>:
  match r:
    case Rq{n, LoF{k, fas, fvt, rg}, tys}:
      rg
    case Rq{n, LoFl{k, fas, fvt, gv, rg}, tys}:
      rg
    case Rq{n, LoFm{nm, m, j, mtys, fas, fvt, rg}, tys}:
      rg
    case Rq{n, LoFlm{nm, m, j, mtys, fas, fvt, gv, rg}, tys}:
      rg
    case _:
      Nil{}

def sp.fl.x(r: Rw) -> X.Sx:
  match r:
    case Rw{x, q}:
      x

def sp.fl.q(r: Rw) -> List<&2, Rq>:
  match r:
    case Rw{x, q}:
      q

# whether x binds the local v: an (export v ..), or a (fun (self v) ..)
def sp.fl.has(x: X.Sx, +v: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +a = X.tsx.atom.of(h)
      +ex = Bool.and(sp.is(a, "export"), sp.eq(sp.at(n, 1n), v))
      +fu = Bool.and(sp.is(a, "fun"), sp.eq(sp.var.of(sp.at(n, 1n)), v))
      +sub = Bool.or(sp.fl.has(h, v), sp.fl.has(t, v))
      Bool.or(Bool.or(ex, fu), sub)
    case _:
      False{}

# the first local copy q asks for that x has the group of and not the copy
def sp.fl.want(+r: Rq, +x: X.Sx, +done: List<&2, List<&2, U32>>) -> Bool:
  +n = sp.rq.n(r)
  Bool.and(sp.fl.isfl(r), Bool.and(Bool.not(S.mem(n, done)), Bool.and(sp.fl.has(x, sp.fl.gv(r)), Bool.not(sp.fl.has(x, sp.fl.var(n))))))

def sp.fl.next(q: List<&2, Rq>, +x: X.Sx, +done: List<&2, List<&2, U32>>) -> Maybe<&2, Rq>:
  match q:
    case Nil{}:
      None{}
    case +r <> t:
      +rest = sp.fl.next(t, x, done)
      Bool.pick(Maybe<&2, Rq>, sp.fl.want(r, x, done), Some{r}, rest)

# A local copy's parameters are fvHASH_i (HASH its name's), not fv_i: the
# copy is in the scope of what encloses it, which may be a copy with its own
# fv_0, and the fold hands every member of the group the locals the others
# use, by name (traverseScoped's goPattern uses the outer fv_0, the copy of
# listTraverse at goAlternative has one of its own).
def sp.fl.hash(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case +c <> t:
      sp.fl.hash(t, Bool.pick(List<&2, U32>, U32.is_eq(c, 102), Nil{}, c <> acc))

def sp.fl.fvs(ts: List<&2, X.Sx>, +i: Nat, +p: List<&2, U32>) -> List<&2, Asb>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Asb{sp.fa.fv(i), sp.l([sp.a("l"), X.SxStr{sp.cat(p, S.b(Nat.show(i)))}, sp.a("0")])} <> sp.fl.fvs(r, 1n+i, p)

def sp.fl.own(+n: List<&2, U32>, fvt: List<&2, X.Sx>, m: Maybe<&2, X.Sx>) -> Maybe<&2, X.Sx>:
  match m:
    case Some{+c}:
      Some{sp.as.sub(c, None{}, sp.fl.fvs(fvt, 0n, sp.cat(S.b("fv"), sp.cat(sp.fl.hash(n, Nil{}), S.b("_")))))}
    case None{}:
      None{}

# the copy of a local copy's def at its types and argument, as a top
def sp.fl.copy(+r: Rq, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, X.Sx>:
  match r ix:
    case Rq{+n, LoFl{k, fas, +fvt, gv, rg}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, +fns, cts}:
      sp.fl.own(n, fvt, sp.fa.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.df.find(fns, k), t => sp.fun.of(t)), n, fas, fvt, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns, cts}))
    case Rq{+n, LoFlm{nm, m, j, mtys, fas, +fvt, gv, rg}, tys} +i:
      sp.fl.own(n, fvt, sp.fa.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.copy(Rq{nm, LoL{m, j}, mtys}, cur, i), t => sp.fun.of(t)), n, fas, fvt, Nil{}, cur, i))
    case _ _:
      None{}

# A local copy's variables that are named as one of its group's scope (the
# model's kleisliR has an f, and so has transformNoDeferM around it: both
# are then parameters of the group's members, by name): NAME_lc.
def sp.fl.names(vs: List<&2, Asb>) -> List<&2, List<&2, U32>>:
  match vs:
    case Nil{}:
      Nil{}
    case Asb{+v, e} <> t:
      sp.sat(v, 1n) <> sp.fl.names(t)

def sp.fl.apart.s(bs: List<&2, Asb>, +ns: List<&2, List<&2, U32>>) -> List<&2, Asb>:
  match bs:
    case Nil{}:
      Nil{}
    case Asb{+v, e} <> t:
      +rest = sp.fl.apart.s(t, ns)
      +w = sp.l([sp.a("l"), X.SxStr{sp.cat(sp.sat(v, 1n), S.b("_lc"))}, sp.at(v, 2n)])
      Bool.pick(List<&2, Asb>, Bool.and(sp.head.is(v, "l"), S.mem(sp.sat(v, 1n), ns)), Asb{v, w} <> rest, rest)

# the variables of the copy's clauses' patterns
def sp.fl.apart.ps(ms: List<&2, X.Sx>) -> List<&2, Asb>:
  match ms:
    case Nil{}:
      Nil{}
    case m <> t:
      List.append(&2, Asb, sp.fa.binds(sp.at(m, 1n), Nil{}), sp.fl.apart.ps(t))

def sp.fl.apart.fun(f: Maybe<&2, X.Sx>) -> List<&2, Asb>:
  match f:
    case Some{x}:
      sp.fl.apart.ps(sp.els(sp.at(sp.at(x, 4n), 4n)))
    case None{}:
      Nil{}

def sp.fl.apart(+c: X.Sx, +sc: List<&2, Asb>) -> X.Sx:
  +s = sp.fl.apart.s(sp.fl.apart.fun(sp.fun.of(c)), sp.fl.names(sc))
  sp.if(X.Sx, List.is_empty(&2, Asb, s), _ => c, _ => sp.as.sub(c, None{}, s))

# the copy's top through the passes, its var (g CUR N var) the local
def sp.fl.run(m: Maybe<&2, X.Sx>, +n: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +rl: List<&2, X.Sx>, +ol: List<&2, Og>, +kn: List<&2, Rq>, +rg: List<&2, X.Sx>) -> Rw:
  match m:
    case Some{+c}:
      +r = sp.passes0(sp.fl.apart(c, sp.og.base(ol)), cur, ix, rl, ol, kn, rg)
      +s = {[Asb{sp.g(cur, n, "var"), sp.fl.var(n)}] : List<&2, Asb>}
      +y = sp.fl.x(r)
      Rw{sp.as.sub(y, sp.as.look(y, s), s), sp.fl.q(r)}
    case None{}:
      Rw{X.SxNil{}, Nil{}}

def sp.fl.snoc(+xs: X.Sx, +y: X.Sx) -> X.Sx:
  sp.l(List.append(&2, X.Sx, sp.els(xs), [y]))

# (abs TVS EVS EXPORTS EVBINDS BINDS ..) with the copy's export and bind
def sp.fl.ins.abs(+n: X.Sx, +e: X.Sx, +b: X.Sx) -> X.Sx:
  match n:
    case X.SxCons{a, X.SxCons{tv, X.SxCons{ev, X.SxCons{es, X.SxCons{eb, X.SxCons{bs, rest}}}}}}:
      X.SxCons{a, X.SxCons{tv, X.SxCons{ev, X.SxCons{sp.fl.snoc(es, e), X.SxCons{eb, X.SxCons{sp.fl.snoc(bs, b), rest}}}}}}
    case y:
      y

def sp.fl.exp.has(es: List<&2, X.Sx>, +v: X.Sx) -> Bool:
  match es:
    case Nil{}:
      False{}
    case +e <> t:
      Bool.or(Bool.and(sp.head.is(e, "export"), sp.eq(sp.at(e, 1n), v)), sp.fl.exp.has(t, v))

def sp.fl.fun.has(bs: List<&2, X.Sx>, +v: X.Sx) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +b <> t:
      Bool.or(Bool.and(sp.head.is(b, "fun"), sp.eq(sp.var.of(sp.at(b, 1n)), v)), sp.fl.fun.has(t, v))

# x with the copy (its export e and bind b) in the group of v: the abs that
# exports v, or the (rec ..) that binds v by a bare fun
def sp.fl.ins(x: X.Sx, +v: X.Sx, +e: X.Sx, +b: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      +n = {X.SxCons{h, t} : X.Sx}
      +a = X.tsx.atom.of(h)
      +isabs = Bool.and(sp.is(a, "abs"), sp.fl.exp.has(sp.els(sp.at(n, 3n)), v))
      +isrec = Bool.and(sp.is(a, "rec"), sp.fl.fun.has(sp.els(t), v))
      +down = {X.SxCons{sp.fl.ins(h, v, e, b), sp.fl.ins(t, v, e, b)} : X.Sx}
      Bool.pick(X.Sx, isabs, sp.fl.ins.abs(n, e, b), Bool.pick(X.Sx, isrec, sp.fl.snoc(n, b), down))
    case y:
      y

# x with the copy c's top's export and bind in v's group (none: x)
def sp.fl.put(+x: X.Sx, +v: X.Sx, c: X.Sx) -> X.Sx:
  match c:
    case X.SxNil{}:
      x
    case +c1:
      +ab = sp.at(c1, 1n)
      sp.fl.ins(x, v, sp.or(sp.nth(sp.els(sp.at(ab, 3n)), 0n), X.SxNil{}), sp.or(sp.nth(sp.els(sp.at(ab, 5n)), 0n), X.SxNil{}))

# each local copy x asks for into its group, at most fuel, each once
def sp.fl.fix(fuel: Nat, m: Maybe<&2, Rq>, +x: X.Sx, +q: List<&2, Rq>, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +ix: Ix, +kn: List<&2, Rq>) -> Rw:
  match fuel m:
    case 1n+p Some{+r}:
      +c = sp.fl.run(sp.fl.copy(r, cur, ix), sp.rq.n(r), cur, ix, sp.fl.recs(x, Nil{}), sp.og.at(sp.og.of(x, Nil{}, Nil{}, False{}), sp.fl.gv(r)), List.append(&2, Rq, q, kn), sp.rq.rg(r))
      +x2 = sp.fl.put(x, sp.fl.gv(r), sp.fl.x(c))
      +q2 = sp.rw.cat(q, sp.fl.q(c))
      +d2 = {sp.rq.n(r) <> done : List<&2, List<&2, U32>>}
      sp.fl.fix(p, sp.fl.next(q2, x2, d2), x2, q2, d2, cur, ix, kn)
    case _ _:
      Rw{x, q}

def sp.fl.start(r: Rw, +cur: List<&2, U32>, +ix: Ix, +kn: List<&2, Rq>) -> Rw:
  match r:
    case Rw{+x, +q}:
      sp.fl.fix(64n, sp.fl.next(q, x, Nil{}), x, q, Nil{}, cur, ix, kn)

def sp.passes(+x: X.Sx, +cur: List<&2, U32>, +ix: Ix, +kn: List<&2, Rq>, +rg: List<&2, X.Sx>) -> Rw:
  sp.fl.start(sp.passes0(x, cur, ix, Nil{}, Nil{}, kn, rg), cur, ix, kn)

def sp.rq.name(rq: Rq) -> List<&2, U32>:
  match rq:
    case Rq{n, lo, tys}:
      n

def sp.work.at(m: Maybe<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix, +kn: List<&2, Rq>, +rg: List<&2, X.Sx>) -> Rw:
  match m:
    case Some{top}:
      sp.passes(top, cur, ix, kn, rg)
    case None{}:
      Rw{X.SxNil{}, Nil{}}

def sp.work.put(r: Rw, acc: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match r:
    case Rw{X.SxNil{}, q}:
      acc
    case Rw{x, q}:
      x <> acc

def sp.work.rq(r: Rw) -> List<&2, Rq>:
  match r:
    case Rw{x, q}:
      q

# the copies asked for, and those their copies ask for, each once, at most n
def sp.names.cons(n: List<&2, U32>, ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  n <> ns

def sp.work.seen(todo: List<&2, Rq>, +done: List<&2, List<&2, U32>>) -> Bool:
  match todo:
    case Nil{}:
      False{}
    case rq <> t:
      S.mem(sp.rq.name(rq), done)

def sp.work(n: Nat, todo: List<&2, Rq>, seen: Bool, +done: List<&2, List<&2, U32>>, acc: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> List<&2, X.Sx>:
  match n todo seen:
    case Succ{k} rq <> +rest True{}:
      sp.work(k, rest, sp.work.seen(rest, done), done, acc, cur, ix)
    case Succ{k} +rq <> rest False{}:
      +nm = sp.rq.name(rq)
      +r = sp.work.at(sp.copy.any(rq, cur, ix), cur, ix, Nil{}, Nil{})
      +todo2 = List.append(&2, Rq, rest, sp.work.rq(r))
      +done2 = sp.names.cons(nm, done)
      sp.work(k, todo2, sp.work.seen(todo2, done2), done2, sp.work.put(r, acc), cur, ix)
    case _ _ _:
      List.reverse(&2, X.Sx, acc)

# A module: each top's passes, then the copies they ask for
def sp.items.one(top: Bool, +x: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match top:
    case True{}:
      sp.passes(x, cur, ix, Nil{}, Nil{})
    case False{}:
      Rw{x, Nil{}}

def sp.items(xs: List<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match xs:
    case Nil{}:
      Rw{X.SxNil{}, Nil{}}
    case +x <> t:
      sp.rw.cons(sp.items.one(sp.head.is(x, "top"), x, cur, ix), sp.items(t, cur, ix))

def sp.rw.x(r: Rw) -> X.Sx:
  match r:
    case Rw{x, q}:
      x

# Copies once per package (the user, 11-23: "merge the duplicate
# copies"). A copy of a global def at its types (LoG: a def or an
# instance's method, NAME__TYPES) is one program wherever it is asked
# for, so a module that imports a module of the package that wrote it
# names that one, (g THAT NAME var), and writes no copy of its own (nor
# the copies only it would ask for). Copies at a known function argument
# (LoF, LoFl) and of a module's locals (LoL) are still made in each
# module: their names do not say the caller's function or local.

# a copy a module wrote: its def's key (LoG's), its name, the module
type Wc is Data:
  Wc{k: List<&2, U32>, n: List<&2, U32>, m: List<&2, U32>}

# a copy the module names in another module
type Rd is Data:
  Rd{n: List<&2, U32>, m: List<&2, U32>}

# a module's copies, the ones it names elsewhere, the ones it wrote
type Wk is Data:
  Wk{tops: List<&2, X.Sx>, rd: List<&2, Rd>, wc: List<&2, Wc>}

# a module's output and the package's copies after it
type Md is Data:
  Md{xs: List<&2, X.Sx>, wc: List<&2, Wc>}

# a request's global key (LoG), else empty
def sp.rq.lok(rq: Rq) -> List<&2, U32>:
  match rq:
    case Rq{n, LoG{k}, tys}:
      k
    case _:
      Nil{}

# the module among ims that wrote the copy n of k
def sp.wc.at(ws: List<&2, Wc>, +k: List<&2, U32>, +n: List<&2, U32>, +ims: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ws:
    case Nil{}:
      None{}
    case Wc{k2, n2, +m2} <> t:
      sp.if(Maybe<&2, List<&2, U32>>, Bool.and(Bool.and(S.eq(n, n2), S.eq(k, k2)), S.mem(m2, ims)), _ => Some{m2}, _ => sp.wc.at(t, k, n, ims))

# the modules a module imports, from its (module NAME ((import M ..)..))
def sp.ims.of(its: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match its:
    case Nil{}:
      Nil{}
    case +i <> t:
      sp.sat(i, 1n) <> sp.ims.of(t)

def sp.imports(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      sp.if(List<&2, List<&2, U32>>, sp.head.is(x, "module"), _ => sp.ims.of(sp.els(sp.at(x, 2n))), _ => sp.imports(t))

def sp.wc.add(+lk: List<&2, U32>, +nm: List<&2, U32>, +cur: List<&2, U32>, +wc: List<&2, Wc>) -> List<&2, Wc>:
  Bool.pick(List<&2, Wc>, List.is_empty(&2, U32, lk), wc, Wc{lk, nm, cur} <> wc)

# the module (of ims) that wrote todo's first copy, if any
def sp.work.got(todo: List<&2, Rq>, +ws: List<&2, Wc>, +ims: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match todo:
    case Nil{}:
      None{}
    case +rq <> t:
      sp.wc.at(ws, sp.rq.lok(rq), sp.rq.name(rq), ims)

# the dictionary copies asked for so far (kn: the module's, for the copies'
# own passes: an argument's call was p4's in the def that has it)
def sp.kn.add(rs: List<&2, Rq>, +kn: List<&2, Rq>) -> List<&2, Rq>:
  match rs:
    case Nil{}:
      kn
    case +r <> t:
      +d = Bool.or(sp.rq.isg(r), sp.rq.isl(r))
      sp.kn.add(t, Bool.pick(List<&2, Rq>, d, r <> kn, kn))

# sp.work, a copy another module wrote (got: todo's first's) named there
# (rd) and not made
def sp.work2(n: Nat, +todo: List<&2, Rq>, +kn: List<&2, Rq>, seen: Bool, got: Maybe<&2, List<&2, U32>>, +done: List<&2, List<&2, U32>>, acc: List<&2, X.Sx>, rd: List<&2, Rd>, wc: List<&2, Wc>, +ws: List<&2, Wc>, +ims: List<&2, List<&2, U32>>, +cur: List<&2, U32>, +ix: Ix) -> Wk:
  match n todo seen got:
    case Succ{k} rq <> +rest True{} _:
      sp.work2(k, rest, kn, sp.work.seen(rest, done), sp.work.got(rest, ws, ims), done, acc, rd, wc, ws, ims, cur, ix)
    case Succ{k} +rq <> +rest False{} Some{m}:
      +done2 = sp.names.cons(sp.rq.name(rq), done)
      sp.work2(k, rest, kn, sp.work.seen(rest, done2), sp.work.got(rest, ws, ims), done2, acc, Rd{sp.rq.name(rq), m} <> rd, wc, ws, ims, cur, ix)
    case Succ{k} +rq <> +rest False{} None{}:
      +nm = sp.rq.name(rq)
      +r = sp.work.at(sp.copy.any(rq, cur, ix), cur, ix, kn, sp.rq.rg(rq))
      +todo2 = List.append(&2, Rq, rest, sp.work.rq(r))
      +done2 = sp.names.cons(nm, done)
      sp.work2(k, todo2, sp.kn.add(sp.work.rq(r), kn), sp.work.seen(todo2, done2), sp.work.got(todo2, ws, ims), done2, sp.work.put(r, acc), rd, sp.wc.add(sp.rq.lok(rq), nm, cur, wc), ws, ims, cur, ix)
    case _ _ _ _:
      Wk{List.reverse(&2, X.Sx, acc), rd, wc}

def sp.rd.find(rd: List<&2, Rd>, +n: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match rd:
    case Nil{}:
      None{}
    case Rd{n2, +m} <> t:
      sp.if(Maybe<&2, List<&2, U32>>, S.eq(n, n2), _ => Some{m}, _ => sp.rd.find(t, n))

def sp.redir.g(m: Maybe<&2, List<&2, U32>>, +y: X.Sx) -> X.Sx:
  match m:
    case Some{a}:
      sp.l([sp.a("g"), X.SxStr{a}, sp.at(y, 2n), sp.at(y, 3n)])
    case None{}:
      y

# x with each (g CUR NAME ..) of a copy named elsewhere as (g THAT NAME ..)
def sp.redir(x: X.Sx, +cur: List<&2, U32>, +rd: List<&2, Rd>) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      +y = {X.SxCons{sp.redir(h, cur, rd), sp.redir(t, cur, rd)} : X.Sx}
      sp.if(X.Sx, Bool.and(sp.head.is(y, "g"), S.eq(sp.sat(y, 1n), cur)), _ => sp.redir.g(sp.rd.find(rd, sp.sat(y, 2n)), y), _ => y)
    case z:
      z

def sp.redirs(xs: List<&2, X.Sx>, +cur: List<&2, U32>, +rd: List<&2, Rd>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.redir(x, cur, rd) <> sp.redirs(t, cur, rd)

def sp.wk.tops(w: Wk) -> List<&2, X.Sx>:
  match w:
    case Wk{t, r, c}:
      t

def sp.wk.rd(w: Wk) -> List<&2, Rd>:
  match w:
    case Wk{t, r, c}:
      r

def sp.wk.wc(w: Wk) -> List<&2, Wc>:
  match w:
    case Wk{t, r, c}:
      c

def sp.md.xs(m: Md) -> List<&2, X.Sx>:
  match m:
    case Md{x, w}:
      x

def sp.md.wc(m: Md) -> List<&2, Wc>:
  match m:
    case Md{x, w}:
      w

# the module's items and copies, the copies named elsewhere redirected
def sp.module.at(+xs: List<&2, X.Sx>, +cur: List<&2, U32>, +rd: List<&2, Rd>) -> List<&2, X.Sx>:
  sp.if(List<&2, X.Sx>, List.is_empty(&2, Rd, rd), _ => xs, _ => sp.redirs(xs, cur, rd))

def sp.module(+xs: List<&2, X.Sx>, +ix: Ix, +ws: List<&2, Wc>) -> Md:
  +cur = sp.modname(xs)
  +r = sp.items(xs, cur, ix)
  +ims = sp.imports(xs)
  +todo = sp.work.rq(r)
  +w = sp.work2(4000n, todo, sp.kn.add(todo, Nil{}), False{}, sp.work.got(todo, ws, ims), Nil{}, Nil{}, Nil{}, Nil{}, ws, ims, cur, ix)
  Md{sp.module.at(List.append(&2, X.Sx, sp.els(sp.rw.x(r)), sp.wk.tops(w)), cur, sp.wk.rd(w)), List.append(&2, Wc, sp.wk.wc(w), ws)}

# crypton's Digest SHA256 as HsPrelude's HsDigest (SHA256 itself, the
# algorithm's tag, as ()) and a ByteString (strict or lazy) as a list of
# Word8;
# Int and Integer as HsPrelude's HsInt (an integer: telomare's function
# indices are negative), IntMap v as Map HsInt v and IntSet as Set HsInt,
# their functions Data.Map's and Data.Set's at key HsInt (the key the
# first type argument, or the last where Data.Map's own order has it so:
# map, filter, foldr, Set's unions)
def sp.hsint() -> X.Sx:
  sp.tc(S.b("HsPrelude"), S.b("HsInt"), Nil{})

# containers' Data.Graph and Data.Tree as cata's model's (prelude/Cata/Graph.hs):
# a Vertex is an Int, a Graph (an Array Vertex [Vertex] from 0) the model's
# IntMap Int [Int] (here Map HsInt [HsInt]), Tree and SCC the model's types
def sp.p5.graph(+k: List<&2, U32>, +args: List<&2, X.Sx>) -> X.Sx:
  Bool.pick(X.Sx, sp.is(k, "Data.Graph.Vertex"), sp.hsint(), Bool.pick(X.Sx, sp.is(k, "Data.Graph.Graph"), sp.tc(S.b("Data.Map.Internal"), S.b("Map"), [sp.hsint(), sp.tc(S.b("GHC.Types"), S.b("List"), [sp.hsint()])]), Bool.pick(X.Sx, sp.is(k, "Data.Tree.Tree"), sp.tc(S.b("Cata.Graph"), S.b("Tree"), args), sp.tc(S.b("Cata.Graph"), S.b("SCC"), args))))

# binary's Get and Put, utf8-string's toString, ByteString's length and
# filepath's takeExtension as cata's model's (prelude/Cata/Binary.hs): Get a
# is the model's ExceptT String (State ([Word8], HsInt)) a, PutM a its
# Writer [Word8] a and Put its Writer [Word8] () (a partial application
# keeps its arguments: Monad Get's Get alone); a global of theirs is the
# model's def (sp.bin.tab; utf8-string's fromString is utf8-string's
# encode); fail at the model's Get (no other monad is that ExceptT: State
# has no MonadFail) is its failGet
def sp.bin.w8s() -> X.Sx:
  sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Internal.Word"), S.b("Word8"), Nil{})])

def sp.bin.st() -> X.Sx:
  sp.tc(S.b("Control.Monad.Trans.State.Lazy"), S.b("State"), [sp.tc(S.b("GHC.Tuple"), S.b("Tuple2"), [sp.bin.w8s(), sp.hsint()])])

def sp.bin.tc(+k: List<&2, U32>, +x: X.Sx) -> X.Sx:
  +args = sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))
  +get = sp.is(k, "Data.Binary.Get.Internal.Get")
  +putm = sp.is(k, "Data.Binary.Put.PutM")
  +put = sp.is(k, "Data.Binary.Put.Put")
  +wr = {"Control.Monad.Trans.Writer.Strict" : String}
  +idn = sp.tc(S.b("GHC.Internal.Data.Functor.Identity"), S.b("Identity"), Nil{})
  Bool.pick(X.Sx, get, sp.tc(S.b("Control.Monad.Trans.Except"), S.b("ExceptT"), sp.tc(S.b("GHC.Internal.Base"), S.b("String"), Nil{}) <> sp.bin.st() <> args), Bool.pick(X.Sx, putm, sp.tc(S.b(wr), S.b("WriterT"), sp.bin.w8s() <> idn <> args), Bool.pick(X.Sx, put, sp.tc(S.b(wr), S.b("WriterT"), [sp.bin.w8s(), idn, sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{})]), x)))

def sp.bin.tab() -> List<&2, Pcr>:
  +g = {"Data.Binary.Get." : String}
  +p = {"Data.Binary.Put." : String}
  [Pcr{S.b(g ++ "getWord8"), S.b("getWord8"), 0n}, Pcr{S.b(g ++ "getInt64le"), S.b("getInt64le"), 0n}, Pcr{S.b(g ++ "getLazyByteString"), S.b("getLazyByteString"), 0n}, Pcr{S.b(g ++ "runGetOrFail"), S.b("runGetOrFail"), 0n}, Pcr{S.b(p ++ "putWord8"), S.b("putWord8"), 0n}, Pcr{S.b(p ++ "putInt64le"), S.b("putInt64le"), 0n}, Pcr{S.b(p ++ "putLazyByteString"), S.b("putLazyByteString"), 0n}, Pcr{S.b(p ++ "runPut"), S.b("runPut"), 0n}, Pcr{S.b("Data.ByteString.UTF8.toString"), S.b("utf8Decode"), 0n}, Pcr{S.b("Data.ByteString.Lazy.length"), S.b("byteLength"), 0n}, Pcr{S.b("System.FilePath.Posix.takeExtension"), S.b("takeExtension"), 0n}]

# (tyapp (evapp (tyapp (g fail) T) DICT) A), T the model's Get: failGet at A
def sp.bin.fail(+y: X.Sx) -> X.Sx:
  +e = sp.at(y, 1n)
  +t = sp.at(e, 1n)
  +ty = sp.at(t, 2n)
  +isf = Bool.and(Bool.and(sp.head.is(y, "tyapp"), sp.head.is(e, "evapp")), Bool.and(sp.head.is(t, "tyapp"), sp.is(sp.gkey(sp.at(t, 1n)), "GHC.Internal.Control.Monad.Fail.fail")))
  +get = Bool.and(sp.is(sp.tckey(ty), "Control.Monad.Trans.Except.ExceptT"), sp.is(sp.tckey(sp.at(ty, 4n)), "Control.Monad.Trans.State.Lazy.State"))
  Bool.pick(X.Sx, Bool.and(isf, get), sp.l([sp.a("tyapp"), sp.g(S.b("Cata.Binary"), S.b("failGet"), "var"), sp.at(y, 2n)]), y)

def sp.bin.model(m: Maybe<&2, Pcr>, +y: X.Sx) -> X.Sx:
  match m:
    case Some{Pcr{k, n, d}}:
      sp.g(S.b("Cata.Binary"), n, "var")
    case None{}:
      sp.bin.fail(y)

def sp.bin.g(+y: X.Sx) -> X.Sx:
  +k = sp.gkey(y)
  +g = sp.head.is(y, "g")
  +fs = Bool.and(g, sp.is(k, "Data.ByteString.UTF8.fromString"))
  Bool.pick(X.Sx, fs, sp.g(S.b("Codec.Binary.UTF8.String"), S.b("encode"), "var"), sp.bin.model(Bool.pick(Maybe<&2, Pcr>, g, sp.pc.find(sp.bin.tab(), k), None{}), y))

# IO as the model's State World (Cata.Base): its type, and base's console
# and file actions
type Iok is Data:
  Iok{k: String, n: String}

def sp.io.tab() -> List<&2, Iok>:
  +io = {"GHC.Internal.System.IO." : String}
  +bl = {"Data.ByteString.Lazy." : String}
  [Iok{io ++ "putStr", "ioPutStr"}, Iok{io ++ "putStrLn", "ioPutStrLn"}, Iok{io ++ "putChar", "ioPutChar"}, Iok{io ++ "print", "ioPrint"}, Iok{io ++ "getLine", "ioGetLine"}, Iok{io ++ "getChar", "ioGetChar"}, Iok{io ++ "getContents", "ioGetContents"}, Iok{io ++ "interact", "ioInteract"}, Iok{io ++ "readFile", "ioReadFile"}, Iok{io ++ "writeFile", "ioWriteFile"}, Iok{io ++ "appendFile", "ioAppendFile"}, Iok{bl ++ "readFile", "ioReadBytes"}, Iok{bl ++ "writeFile", "ioWriteBytes"}, Iok{"GHC.Internal.IO.Handle.isEOF", "ioIsEOF"}, Iok{"GHC.Internal.IO.Handle.hFlush", "ioFlush"}, Iok{"GHC.Internal.IO.StdHandles.stdout", "ioStdout"}]

def sp.io.find(ts: List<&2, Iok>, +k: List<&2, U32>) -> Maybe<&2, String>:
  match ts:
    case Nil{}:
      None{}
    case Iok{+q, n} <> t:
      Bool.pick(Maybe<&2, String>, sp.is(k, q), Some{n}, sp.io.find(t, k))

def sp.io.put(m: Maybe<&2, String>, y: X.Sx) -> X.Sx:
  match m:
    case Some{n}:
      sp.g(S.b("Cata.Base"), S.b(n), "var")
    case None{}:
      y

def sp.io.mod(+m: List<&2, U32>) -> Bool:
  Bool.or(sp.is(m, "GHC.Internal.System.IO"), Bool.or(sp.is(m, "Data.ByteString.Lazy"), S.prefix(m, S.b("GHC.Internal.IO."))))

def sp.io.g(+y: X.Sx) -> X.Sx:
  sp.if(X.Sx, Bool.and(sp.head.is(y, "g"), sp.io.mod(sp.sat(y, 1n))), _ => sp.io.put(sp.io.find(sp.io.tab(), sp.gkey(y)), y), _ => y)

# base's Down as the model's
def sp.io.down(+y: X.Sx) -> X.Sx:
  +n = sp.sat(y, 2n)
  +d = Bool.or(Bool.or(sp.is(n, "Down"), sp.is(n, "getDown")), Bool.or(sp.is(n, "$fOrdDown"), sp.is(n, "$fEqDown")))
  sp.if(X.Sx, Bool.and(d, Bool.and(sp.head.is(y, "g"), sp.is(sp.sat(y, 1n), "GHC.Internal.Data.Ord"))), _ => sp.l([sp.a("g"), X.SxStr{S.b("Cata.Base")}, sp.at(y, 2n), sp.at(y, 3n)]), _ => y)

def sp.io.tc(+k: List<&2, U32>, +x: X.Sx, +y: X.Sx) -> X.Sx:
  sp.if(X.Sx, sp.is(k, "GHC.Types.IO"), _ => sp.tc(S.b("Control.Monad.Trans.State.Lazy"), S.b("StateT"), sp.tc(S.b("Cata.Base"), S.b("World"), Nil{}) <> sp.tc(S.b("GHC.Internal.Data.Functor.Identity"), S.b("Identity"), Nil{}) <> sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))), _ => sp.if(X.Sx, sp.is(k, "GHC.Internal.IO.Handle.Types.Handle"), _ => sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{}), _ => sp.if(X.Sx, sp.is(k, "GHC.Internal.Data.Ord.Down"), _ => sp.tc(S.b("Cata.Base"), S.b("Down"), sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))), _ => y)))

def sp.p5.tc(+k: List<&2, U32>, +x: X.Sx) -> X.Sx:
  +integer = sp.is(k, "GHC.Num.Integer.Integer")
  +int = Bool.or(sp.is(k, "GHC.Types.Int"), Bool.or(Bool.or(sp.is(k, "GHC.Internal.Int.Int64"), sp.is(k, "Data.Binary.Get.ByteOffset")), Bool.or(sp.is(k, "Data.IntSet.Internal.Key"), sp.is(k, "Data.IntMap.Internal.Key"))))
  +im = sp.is(k, "Data.IntMap.Internal.IntMap")
  +iset = sp.is(k, "Data.IntSet.Internal.IntSet")
  +dig = sp.is(k, "Crypto.Hash.Types.Digest")
  +sha = Bool.or(sp.is(k, "Crypto.Hash.SHA256.SHA256"), sp.is(k, "Crypto.Hash.Algorithms.SHA256"))
  +bs = Bool.or(Bool.or(sp.is(k, "Data.ByteString.Internal.Type.ByteString"), sp.is(k, "Data.ByteString.Internal.Type.StrictByteString")), Bool.or(sp.is(k, "Data.ByteString.Lazy.Internal.ByteString"), sp.is(k, "Data.ByteString.Lazy.Internal.LazyByteString")))
  +rat = Bool.or(sp.is(k, "GHC.Internal.Real.Rational"), sp.is(k, "GHC.Internal.Real.Ratio"))
  +gr = Bool.or(Bool.or(sp.is(k, "Data.Graph.Vertex"), sp.is(k, "Data.Graph.Graph")), Bool.or(sp.is(k, "Data.Tree.Tree"), sp.is(k, "Data.Graph.SCC")))
  Bool.pick(X.Sx, gr, sp.p5.graph(k, sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))), Bool.pick(X.Sx, rat, sp.tc(S.b("HsPrelude"), S.b("HsRational"), Nil{}), Bool.pick(X.Sx, dig, sp.tc(S.b("HsPrelude"), S.b("HsDigest"), Nil{}), Bool.pick(X.Sx, sha, sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{}), Bool.pick(X.Sx, bs, sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Internal.Word"), S.b("Word8"), Nil{})]), Bool.pick(X.Sx, int, sp.hsint(), Bool.pick(X.Sx, integer, sp.tc(S.b("HsPrelude"), S.b("HsInteger"), Nil{}), Bool.pick(X.Sx, im, sp.tc(S.b("Data.Map.Internal"), S.b("Map"), sp.hsint() <> sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))), Bool.pick(X.Sx, iset, sp.tc(S.b("Data.Set.Internal"), S.b("Set"), [sp.hsint()]), sp.bin.tc(k, x))))))))))

# a global of Data.Graph or Data.Tree (stronglyConnComp, graphFromEdges,
# components, flatten, Node, AcyclicSCC) is the model's of its name, and the
# pattern synonym CyclicSCC vs (containers 0.7's, NECyclicSCC's list) the
# model's constructor CyclicSCC
def sp.p5.gr(+y: X.Sx) -> X.Sx:
  +m = sp.sat(y, 1n)
  +g = Bool.and(sp.head.is(y, "g"), Bool.or(sp.is(m, "Data.Graph"), sp.is(m, "Data.Tree")))
  +ps = Bool.and(sp.head.is(y, "unsupported"), Bool.and(sp.is(m, "PatSynCon"), sp.is(sp.sat(y, 2n), "CyclicSCC")))
  Bool.pick(X.Sx, g, sp.l([sp.a("g"), X.SxStr{S.b("Cata.Graph")}, sp.at(y, 2n), sp.at(y, 3n)]), Bool.pick(X.Sx, ps, sp.g(S.b("Cata.Graph"), S.b("CyclicSCC"), "con"), sp.bin.g(sp.io.down(sp.io.g(y)))))

# an IntMap or IntSet function's Map or Set name, and where its key goes
def sp.p5.mod(+m: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, sp.is(m, "Data.IntMap.Internal"), S.b("Data.Map.Internal"), Bool.pick(List<&2, U32>, sp.is(m, "Data.IntMap.Strict.Internal"), S.b("Data.Map.Strict.Internal"), Bool.pick(List<&2, U32>, sp.is(m, "Data.IntSet.Internal"), S.b("Data.Set.Internal"), Nil{})))

def sp.p5.last(+m: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  Bool.or(Bool.and(Bool.not(sp.is(m, "Data.IntSet.Internal")), Bool.or(sp.is(n, "map"), Bool.or(sp.is(n, "filter"), Bool.or(sp.is(n, "foldr"), Bool.or(sp.is(n, "partition"), sp.is(n, "mapMaybe")))))), Bool.and(sp.is(m, "Data.IntSet.Internal"), sp.is(n, "unions")))

# IntMap's unionsWith: Data.Map's has the key second (Foldable f, then
# Ord k)
def sp.p5.second(+m: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  Bool.and(Bool.or(sp.is(m, "Data.IntMap.Internal"), sp.is(m, "Data.IntMap.Strict.Internal")), Bool.or(sp.is(n, "unionsWith"), sp.is(n, "unions")))

def sp.mkspine(ts: List<&2, X.Sx>, h: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      h
    case t <> r:
      sp.mkspine(r, sp.l([sp.a("tyapp"), h, t]))

# a spine (or a bare name) whose head is an IntMap or IntSet function (IntMap's
# ! is the model's intMapAt, whose error text is IntMap's own)
def sp.p5.call(+x: X.Sx) -> Maybe<&2, X.Sx>:
  +h = sp.vhead(x)
  +m = sp.sat(h, 1n)
  +n = sp.sat(h, 2n)
  +nm = sp.p5.mod(m)
  +tys = sp.spine.tys(x, Nil{})
  +ks = Bool.pick(List<&2, X.Sx>, sp.p5.second(m, n), sp.first(tys) <> sp.hsint() <> sp.pc.drop(1n, tys), Bool.pick(List<&2, X.Sx>, sp.p5.last(m, n), List.append(&2, X.Sx, tys, [sp.hsint()]), sp.hsint() <> tys))
  +at = Bool.and(sp.is(n, "!"), Bool.or(sp.is(m, "Data.IntMap.Internal"), sp.is(m, "Data.IntMap.Strict.Internal")))
  Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(h, "g"), at), Some{sp.mkspine(tys, sp.g(S.b("Cata.Base"), S.b("intMapAt"), "var"))}, Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(h, "g"), Bool.not(S.eq(nm, Nil{}))), Some{sp.mkspine(ks, sp.g(nm, n, "var"))}, None{}))

def sp.p5.isg(+x: X.Sx) -> Bool:
  Bool.or(sp.isty(x), sp.head.is(x, "g"))

# Identity's constructor and runIdentity are id (the fold erases the
# newtype), a pattern Identity p is p; base's functions whose Int is HsInt
# here (length, take, drop, replicate, ord, chr, !!) are HsPrelude.Z's
def sp.p5.ident(+y: X.Sx) -> X.Sx:
  +k = sp.gkey(y)
  +idc = Bool.or(sp.is(k, "GHC.Internal.Data.Functor.Identity.Identity"), sp.is(k, "GHC.Internal.Data.Functor.Identity.runIdentity"))
  +pid = Bool.and(sp.head.is(y, "pcon"), sp.is(sp.gkey(sp.at(y, 1n)), "GHC.Internal.Data.Functor.Identity.Identity"))
  +z = Bool.or(Bool.or(Bool.or(sp.is(k, "GHC.Internal.Data.Foldable.length"), sp.is(k, "GHC.Internal.List.take")), Bool.or(Bool.or(sp.is(k, "GHC.Internal.List.drop"), sp.is(k, "GHC.Internal.List.replicate")), Bool.or(sp.is(k, "GHC.Internal.Base.ord"), sp.is(k, "GHC.Internal.Char.chr")))), sp.is(k, "GHC.Internal.List.!!"))
  Bool.pick(X.Sx, idc, sp.g(S.b("GHC.Internal.Base"), S.b("id"), "var"), Bool.pick(X.Sx, pid, sp.at(sp.at(y, 3n), 1n), Bool.pick(X.Sx, z, sp.l([sp.a("g"), X.SxStr{S.b("HsPrelude.Z")}, sp.at(y, 2n), sp.at(y, 3n)]), sp.p5.gr(y))))

# zip [n ..] xs, zip xs [n ..], zipWith f [n ..] xs and zipWith f xs [n ..]
# (Haskell's endless list from n, which the zip ends): HsPrelude.Z's zipFrom,
# zipR, zipWithFrom and zipWithR given n
def sp.zf.from(+x: X.Sx) -> Bool:
  Bool.and(sp.head.is(x, "arith"), sp.head.is(sp.at(x, 2n), "from"))

# the name of the global under a function's type arguments
def sp.zf.key(f: X.Sx) -> List<&2, U32>:
  match f:
    case X.SxCons{+h, X.SxCons{+g, +r}}:
      Bool.pick(List<&2, U32>, sp.is(X.tsx.atom.of(h), "tyapp"), sp.zf.key(g), sp.gkey(X.SxCons{h, X.SxCons{g, r}}))
    case y:
      sp.gkey(y)

# the global under a function's type arguments renamed HsPrelude.Z's n
def sp.zf.ren(f: X.Sx, +n: List<&2, U32>) -> X.Sx:
  match f:
    case X.SxCons{+h, X.SxCons{+g, +r}}:
      Bool.pick(X.Sx, sp.is(X.tsx.atom.of(h), "tyapp"), X.SxCons{h, X.SxCons{sp.zf.ren(g, n), r}}, sp.g(S.b("HsPrelude.Z"), n, "var"))
    case y:
      y

def sp.zf.ap(f: X.Sx, x: X.Sx) -> X.Sx:
  sp.l([sp.a("app"), f, x])

def sp.zf.n(+x: X.Sx) -> X.Sx:
  sp.at(sp.at(x, 2n), 1n)

# a bare literal (int N) as an argument (GHC's derived code writes them so,
# at Int): an olit at HsInt
def sp.int.arg(+y: X.Sx) -> X.Sx:
  +x = sp.at(y, 2n)
  Bool.pick(X.Sx, sp.head.is(x, "int"), sp.zf.ap(sp.at(y, 1n), sp.l([sp.a("olit"), x, sp.tc(S.b("HsPrelude"), S.b("HsInt"), Nil{}), x])), y)

def sp.zf.go(r1: Bool, r2: Bool, r3: Bool, r4: Bool, +f: X.Sx, +x: X.Sx, +y: X.Sx) -> X.Sx:
  match r1 r2 r3 r4:
    case True{} _ _ _:
      sp.zf.ap(sp.zf.ren(f, S.b("zipFrom")), sp.zf.n(x))
    case False{} True{} _ _:
      sp.zf.ap(sp.zf.ap(sp.zf.ren(sp.at(f, 1n), S.b("zipR")), sp.at(f, 2n)), sp.zf.n(x))
    case False{} False{} True{} _:
      sp.zf.ap(sp.zf.ap(sp.zf.ren(sp.at(f, 1n), S.b("zipWithFrom")), sp.at(f, 2n)), sp.zf.n(x))
    case False{} False{} False{} True{}:
      sp.zf.ap(sp.zf.ap(sp.zf.ap(sp.zf.ren(sp.at(sp.at(f, 1n), 1n), S.b("zipWithR")), sp.at(sp.at(f, 1n), 2n)), sp.at(f, 2n)), sp.zf.n(x))
    case False{} False{} False{} False{}:
      sp.int.arg(y)

def sp.zf.app(+f: X.Sx, +x: X.Sx, +y: X.Sx) -> X.Sx:
  +fr = sp.zf.from(x)
  +f1 = sp.at(f, 1n)
  +fa = Bool.and(fr, sp.head.is(f, "app"))
  +k1 = sp.zf.key(f1)
  sp.zf.go(Bool.and(fr, sp.is(sp.zf.key(f), "GHC.Internal.List.zip")), Bool.and(fa, sp.is(k1, "GHC.Internal.List.zip")), Bool.and(fa, sp.is(k1, "GHC.Internal.List.zipWith")), Bool.and(Bool.and(fa, sp.head.is(f1, "app")), sp.is(sp.zf.key(sp.at(f1, 1n)), "GHC.Internal.List.zipWith")), f, x, y)

def sp.zf.if(app: Bool, +y: X.Sx) -> X.Sx:
  match app:
    case True{}:
      sp.zf.app(sp.at(y, 1n), sp.at(y, 2n), y)
    case False{}:
      y

def sp.zf(y: X.Sx) -> X.Sx:
  match y:
    case X.SxCons{+h, t}:
      sp.zf.if(sp.is(X.tsx.atom.of(h), "app"), X.SxCons{h, t})
    case z:
      z

# f $ x as f x, and (f . g) x as f (g x): one call, as the survey and the
# fold read calls (f passed to $ or . was a use of f as a value: a
# recursive f was out, rec-value). The parts may be under (expanded ..)
# wrappers (an operator's application); (f . g) x's g x is read again, so a
# chain f . g . h $ x is f (g (h x)) (8 deep at most)
def sp.dl.dot(n: Nat, +y: X.Sx) -> X.Sx:
  match n:
    case 0n:
      y
    case 1n+k:
      +f1 = sp.pc.strip(sp.at(y, 1n))
      +f2 = sp.pc.strip(sp.at(f1, 1n))
      +c = Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(f1, "app")), Bool.and(sp.head.is(f2, "app"), sp.is(sp.zf.key(sp.at(f2, 1n)), "GHC.Internal.Base..")))
      sp.if(X.Sx, c, _ => sp.zf.ap(sp.at(f2, 2n), sp.dl.dot(k, sp.zf.ap(sp.at(f1, 2n), sp.at(y, 2n)))), _ => y)

def sp.dl(+y: X.Sx) -> X.Sx:
  +f1 = sp.pc.strip(sp.at(y, 1n))
  +d = Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(f1, "app")), sp.is(sp.zf.key(sp.at(f1, 1n)), "GHC.Internal.Base.$"))
  sp.if(X.Sx, d, _ => sp.dl.dot(8n, sp.zf.ap(sp.pc.strip(sp.at(f1, 2n)), sp.at(y, 2n))), _ => sp.dl.dot(8n, y))

def sp.p6(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      sp.dl(X.SxCons{sp.p6(h), sp.p6(t)})
    case y:
      y

# foldr (.) id (intersperse s (fmap f xs)), a list of shows: the model's
# composeSep s f xs; sequence [a, b, ..], a list of actions written out: the
# model's sequenceN a b .. (Bend's lists hold no functions a def may take)
def sp.cs.h(+x: X.Sx, +k: String) -> Bool:
  sp.is(sp.gkey(sp.vhead(sp.pc.strip(x))), k)

def sp.cs.put(+e: X.Sx, +y: X.Sx) -> X.Sx:
  +e1 = sp.pc.strip(sp.at(e, 1n))
  +m = sp.pc.strip(sp.at(e, 2n))
  +m1 = sp.pc.strip(sp.at(m, 1n))
  +g = sp.at(m1, 1n)
  +tys = sp.spine.tys(sp.pc.strip(g), Nil{})
  +fm = sp.cs.h(g, "GHC.Internal.Base.fmap")
  +ok = Bool.and(Bool.and(sp.head.is(e, "app"), sp.head.is(e1, "app")), Bool.and(Bool.and(sp.head.is(m, "app"), sp.head.is(m1, "app")), Bool.and(sp.cs.h(sp.at(e1, 1n), "GHC.Internal.Data.OldList.intersperse"), Bool.or(fm, sp.cs.h(g, "GHC.Internal.Base.map")))))
  +a = Maybe.default(&2, X.Sx, sp.nth(tys, Bool.pick(Nat, fm, 1n, 0n)), X.SxNil{})
  Bool.pick(X.Sx, ok, sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("app"), sp.l([sp.a("tyapp"), sp.g(S.b("Cata.Base"), S.b("composeSep"), "var"), a]), sp.at(e1, 2n)]), sp.at(m1, 2n)]), sp.at(m, 2n)]), y)

def sp.cs(+y: X.Sx) -> X.Sx:
  +f = sp.pc.strip(sp.at(y, 1n))
  +g = sp.pc.strip(sp.at(f, 1n))
  +ok = Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(f, "app")), sp.head.is(g, "app"))
  sp.if(X.Sx, ok, _ => sp.if(X.Sx, Bool.and(sp.cs.h(sp.at(g, 1n), "GHC.Internal.Data.Foldable.foldr"), Bool.and(sp.cs.h(sp.at(g, 2n), "GHC.Internal.Base.."), sp.cs.h(sp.at(f, 2n), "GHC.Internal.Base.id"))), _ => sp.cs.put(sp.pc.strip(sp.at(y, 2n)), y), _ => y), _ => y)

def sp.sq.apps(es: List<&2, X.Sx>, h: X.Sx) -> X.Sx:
  match es:
    case Nil{}:
      h
    case e <> t:
      sp.sq.apps(t, sp.l([sp.a("app"), h, e]))

def sp.sq.name(n: Nat) -> String:
  match n:
    case 1n:
      "sequence1"
    case 2n:
      "sequence2"
    case 3n:
      "sequence3"
    case 4n:
      "sequence4"
    case 5n:
      "sequence5"
    case _:
      ""

def sp.sq.put(+f: X.Sx, +es: List<&2, X.Sx>, +y: X.Sx) -> X.Sx:
  +tys = sp.spine.tys(f, Nil{})
  +m = Maybe.default(&2, X.Sx, sp.nth(tys, 1n), X.SxNil{})
  +a = Maybe.default(&2, X.Sx, sp.nth(tys, 2n), X.SxNil{})
  +n = List.length(&2, X.Sx, es)
  +ok = Bool.and(Bool.and(Nat.is_eq(List.length(&2, X.Sx, tys), 3n), sp.head.is(f, "evapp")), Bool.and(Nat.is_gt(n, 0n), Nat.is_lt(n, 6n)))
  sp.if(X.Sx, ok, _ => sp.sq.apps(es, sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), sp.g(S.b("Cata.Base"), S.b(sp.sq.name(n)), "var"), m]), a]), sp.at(f, 2n)])), _ => y)

def sp.sq(+y: X.Sx) -> X.Sx:
  +f = sp.pc.strip(sp.at(y, 1n))
  +e = sp.pc.strip(sp.at(y, 2n))
  sp.if(X.Sx, Bool.and(sp.head.is(y, "app"), sp.head.is(e, "list")), _ => sp.if(X.Sx, sp.cs.h(f, "GHC.Internal.Data.Traversable.sequence"), _ => sp.sq.put(f, sp.els(sp.at(e, 2n)), y), _ => y), _ => y)

# minimumBy, maximumBy, sortBy, sortOn, groupBy and nubBy at a function that
# names a local (EAL's minimumBy (comparing (tbBasis tab IntMap.!))): the
# model's, which the specialiser copies at it (the prelude's are templates)
def sp.cl.tab() -> List<&2, Iok>:
  [Iok{"GHC.Internal.Data.Foldable.minimumBy", "minimumByOp"}, Iok{"GHC.Internal.Data.Foldable.maximumBy", "maximumByOp"}, Iok{"GHC.Internal.Data.OldList.sortBy", "sortByOp"}, Iok{"GHC.Internal.Data.OldList.sortOn", "sortOnOp"}, Iok{"GHC.Internal.Data.OldList.groupBy", "groupByOp"}, Iok{"GHC.Internal.Data.OldList.nubBy", "nubByOp"}, Iok{"Data.Set.Internal.filter", "setFilterOp"}, Iok{"Data.Set.Internal.map", "setMapOp"}]

def sp.cl.tys(ts: List<&2, X.Sx>, h: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      h
    case t <> r:
      sp.cl.tys(r, sp.l([sp.a("tyapp"), h, t]))

# (a Foldable's is at lists: its type and dictionary go; sortOn keeps its Ord)
def sp.cl.put(m: Maybe<&2, String>, +f: X.Sx, +y: X.Sx) -> X.Sx:
  match m:
    case Some{+n}:
      +tys = sp.spine.tys(f, Nil{})
      +fo = Bool.or(sp.is(S.b(n), "minimumByOp"), sp.is(S.b(n), "maximumByOp"))
      +so = Bool.or(sp.is(S.b(n), "sortOnOp"), sp.is(S.b(n), "setMapOp"))
      +ts = Bool.pick(List<&2, X.Sx>, fo, sp.pc.drop(1n, tys), tys)
      +ok = Bool.and(Nat.is_eq(List.length(&2, X.Sx, ts), Bool.pick(Nat, so, 2n, 1n)), Bool.and(Bool.or(Bool.not(fo), sp.is(sp.tckey(sp.first(tys)), "GHC.Types.List")), Bool.or(Bool.not(so), sp.head.is(f, "evapp"))))
      +h = sp.cl.tys(ts, sp.g(S.b("Cata.Base"), S.b(n), "var"))
      Bool.pick(X.Sx, ok, sp.l([sp.a("app"), Bool.pick(X.Sx, so, sp.l([sp.a("evapp"), h, sp.at(f, 2n)]), h), sp.at(y, 2n)]), y)
    case None{}:
      y

# .. at comparing f: the model's at the key f (minimumOnOp, sortOnOp)
def sp.cl.on(+n: String) -> String:
  Bool.pick(String, sp.is(S.b(n), "minimumByOp"), "minimumOnOp", Bool.pick(String, sp.is(S.b(n), "maximumByOp"), "maximumOnOp", Bool.pick(String, sp.is(S.b(n), "sortByOp"), "sortOnOp", "")))

def sp.cl.key(m: Maybe<&2, String>, +f: X.Sx, +c: X.Sx, +y: X.Sx) -> X.Sx:
  match m:
    case Some{+n}:
      +g = sp.pc.strip(sp.at(c, 1n))
      +tys = sp.spine.tys(g, Nil{})
      +l = Bool.or(sp.is(S.b(n), "sortByOp"), sp.is(sp.tckey(sp.first(sp.spine.tys(f, Nil{}))), "GHC.Types.List"))
      +ok = Bool.and(Bool.and(Bool.not(sp.is(S.b(sp.cl.on(n)), "")), l), Bool.and(Nat.is_eq(List.length(&2, X.Sx, tys), 2n), sp.head.is(g, "evapp")))
      Bool.pick(X.Sx, ok, sp.l([sp.a("app"), sp.l([sp.a("evapp"), sp.cl.tys(tys, sp.g(S.b("Cata.Base"), S.b(sp.cl.on(n)), "var")), sp.at(g, 2n)]), sp.at(c, 2n)]), y)
    case None{}:
      y

def sp.cl.iscmp(+c: X.Sx) -> Bool:
  Bool.and(sp.head.is(c, "app"), sp.cs.h(sp.at(c, 1n), "GHC.Internal.Data.Ord.comparing"))

def sp.cl.mod(+m: List<&2, U32>) -> Bool:
  Bool.or(sp.is(m, "GHC.Internal.Data.Foldable"), Bool.or(sp.is(m, "GHC.Internal.Data.OldList"), sp.is(m, "Data.Set.Internal")))

def sp.cl(+y: X.Sx) -> X.Sx:
  +f = sp.pc.strip(sp.at(y, 1n))
  +g = sp.vhead(f)
  +m = sp.if(Maybe<&2, String>, Bool.and(Bool.and(sp.head.is(y, "app"), sp.head.is(g, "g")), sp.cl.mod(sp.sat(g, 1n))), _ => sp.io.find(sp.cl.tab(), sp.gkey(g)), _ => None{})
  sp.if(X.Sx, Maybe.is_some(&2, String, m), _ => sp.if(X.Sx, List.is_empty(&2, X.Sx, sp.fa.frees(sp.at(y, 2n), sp.fa.binds(sp.at(y, 2n), Nil{}), Nil{})), _ => y, _ => sp.if(X.Sx, sp.cl.iscmp(sp.pc.strip(sp.at(y, 2n))), _ => sp.cl.key(m, f, sp.pc.strip(sp.at(y, 2n)), y), _ => sp.cl.put(m, f, y))), _ => y)

# top: x is no spine's function (so a spine is judged whole)
def sp.p5(x: X.Sx, top: Bool) -> X.Sx:
  match x:
    case X.SxCons{+h, X.SxCons{+e, +r}}:
      +a = X.tsx.atom.of(h)
      +inner = sp.isty(X.SxCons{h, X.SxCons{e, r}})
      +y = sp.cons(sp.p5(h, True{}), sp.cons(sp.p5(e, Bool.not(inner)), sp.p5(r, True{})))
      +c = Bool.pick(Maybe<&2, X.Sx>, Bool.and(top, sp.p5.isg(X.SxCons{h, X.SxCons{e, r}})), sp.p5.call(y), None{})
      Bool.pick(X.Sx, Maybe.is_some(&2, X.Sx, c), sp.or(c, X.SxNil{}), Bool.pick(X.Sx, sp.is(a, "tc"), sp.io.tc(sp.key(sp.sat(y, 1n), sp.sat(y, 2n)), y, sp.p5.tc(sp.key(sp.sat(y, 1n), sp.sat(y, 2n)), y)), sp.cl(sp.sq(sp.cs(sp.zf(sp.p5.ident(y)))))))
    case X.SxCons{+h, X.SxNil{}}:
      X.SxCons{sp.p5(h, True{}), X.SxNil{}}
    case y:
      y

# a local pattern binding's binders as plain locals: in its pattern (bv
# (self V) T) is (bv V T), the local the let's body names; and the
# pattern's type after it, (patbind PAT SPAN GRHSS TYPE) (the fold folds
# the binding as a case on its right-hand side, Fold.bend's RPb)
def sp.pb.unself(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      +y = {X.SxCons{sp.pb.unself(h), sp.pb.unself(t)} : X.Sx}
      Bool.pick(X.Sx, sp.head.is(y, "self"), sp.at(y, 1n), y)
    case z:
      z

# (a pattern's type written already stays: spec's, from the package's
# constructors, when survey, fold and law read its output again)
def sp.pb.ty(+old: X.Sx, +p: X.Sx, +cts: List<&2, Ct>) -> X.Sx:
  sp.if(X.Sx, Nat.is_gt(X.tsx.len(old), 0n), _ => old, _ => sp.first(sp.lc.ty(p, False{}, cts)))

def sp.pb.at(+y: X.Sx, +cts: List<&2, Ct>) -> X.Sx:
  +p = sp.pb.unself(sp.at(y, 1n))
  sp.l([sp.a("patbind"), p, sp.at(y, 2n), sp.at(y, 3n), sp.pb.ty(sp.at(y, 4n), p, cts)])

# a module's own constructors, as sp.ix.ct.add reads them
def sp.cts.own(xs: List<&2, X.Sx>, +m: List<&2, U32>) -> List<&2, Ct>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      +d = Bool.or(sp.head.is(x, "data"), sp.head.is(x, "newtype"))
      List.append(&2, Ct, sp.if(List<&2, Ct>, d, _ => sp.ct.of(m, sp.sat(x, 1n), sp.els(sp.at(x, 3n))), _ => Nil{}), sp.cts.own(t, m))

# A clause whose guards can all fail, (match (PAT..) (grhss (GRHS..) BINDS))
# with a last GRHS that is guarded (and not by otherwise): Haskell goes on
# to the next clause there, which the fold writes as a def of the clause's
# variables (Fold.bend's fd.ft), so its wildcards are variables with their
# types: (pwild T) is (pvar (bv (l "ft_wN" N) T)).

# every guard is otherwise or True
def sp.ftw.sure(gs: List<&2, X.Sx>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case +h <> t:
      +k = sp.gkey(sp.pc.strip(sp.at(h, 1n)))
      Bool.and(Bool.and(sp.head.is(h, "body"), Bool.or(sp.is(k, "GHC.Internal.Base.otherwise"), sp.is(k, "GHC.Types.True"))), sp.ftw.sure(t))

def sp.ftw.last(xs: List<&2, X.Sx>, z: X.Sx) -> X.Sx:
  match xs:
    case Nil{}:
      z
    case h <> t:
      sp.ftw.last(t, h)

# whether the clauses g can fall through
def sp.ftw.falls(+g: X.Sx) -> Bool:
  Bool.and(sp.head.is(g, "grhss"), Bool.not(sp.ftw.sure(sp.els(sp.at(sp.ftw.last(sp.els(sp.at(g, 1n)), X.SxNil{}), 1n)))))

# a tree with its wildcards named, and the next one's number
type Wn is Data:
  Wn{x: X.Sx, n: Nat}

def sp.ftw.mk(+ty: X.Sx, +n: Nat) -> X.Sx:
  +k = S.b(Nat.show(n))
  sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("ft_w"), k)}, X.SxAtom{k}]), ty])])

def sp.ftw.put(x: X.Sx, r: Wn) -> Wn:
  match r:
    case Wn{y, m}:
      Wn{X.SxCons{x, y}, m}

def sp.ftw.cons(h: Wn, rest: Nat -> Wn) -> Wn:
  match h:
    case Wn{x, n}:
      sp.ftw.put(x, rest(n))

def sp.ftw.name(x: X.Sx, +n: Nat) -> Wn:
  match x:
    case X.SxCons{+h, +t}:
      sp.if(Wn, sp.is(X.tsx.atom.of(h), "pwild"), _ => Wn{sp.ftw.mk(sp.at(t, 0n), n), 1n+n}, _ => sp.ftw.cons(sp.ftw.name(h, n), m => sp.ftw.name(t, m)))
    case z:
      Wn{z, n}

def sp.ftw.x(w: Wn) -> X.Sx:
  match w:
    case Wn{x, n}:
      x

def sp.ftw.at(+y: X.Sx) -> X.Sx:
  sp.if(X.Sx, Bool.and(Nat.is_eq(X.tsx.len(y), 3n), sp.ftw.falls(sp.at(y, 2n))), _ => sp.l([sp.a("match"), sp.ftw.x(sp.ftw.name(sp.at(y, 1n), 0n)), sp.at(y, 2n)]), _ => y)

# a pattern guard, (bind PAT E), with its pattern's type after it (the fold
# folds it as a case on E, Fold.bend's fd.pg)
def sp.ftw.bind(+g: X.Sx, +cts: List<&2, Ct>) -> X.Sx:
  sp.if(X.Sx, Bool.and(sp.head.is(g, "bind"), Nat.is_eq(X.tsx.len(g), 3n)), _ => sp.l([sp.a("bind"), sp.at(g, 1n), sp.at(g, 2n), sp.first(sp.lc.ty(sp.at(g, 1n), False{}, cts))]), _ => g)

def sp.ftw.binds(gs: List<&2, X.Sx>, +cts: List<&2, Ct>) -> List<&2, X.Sx>:
  match gs:
    case Nil{}:
      Nil{}
    case h <> t:
      sp.ftw.bind(h, cts) <> sp.ftw.binds(t, cts)

def sp.ftw.anybind(gs: List<&2, X.Sx>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case +h <> t:
      Bool.or(sp.head.is(h, "bind"), sp.ftw.anybind(t))

# (grhs (GUARD..) E)
def sp.ftw.grhs(+y: X.Sx, +cts: List<&2, Ct>) -> X.Sx:
  +gs = sp.els(sp.at(y, 1n))
  sp.if(X.Sx, sp.ftw.anybind(gs), _ => sp.l([sp.a("grhs"), sp.l(sp.ftw.binds(gs, cts)), sp.at(y, 2n)]), _ => y)

# Natural's (-), an error below 0: HsPrelude.N's natSub (the fold's
# HsNum.sub, a failure value there; Int's and Integer's is another)
def sp.natsub(+y: X.Sx) -> X.Sx:
  +f = sp.at(y, 1n)
  +g = sp.at(f, 1n)
  +ok = Bool.and(Bool.and(sp.head.is(f, "tyapp"), sp.head.is(g, "g")), Bool.and(sp.is(sp.sat(g, 2n), "-"), Bool.and(sp.is(sp.sat(g, 1n), "GHC.Internal.Num"), sp.is(sp.tckey(sp.at(f, 2n)), "GHC.Num.Natural.Natural"))))
  sp.if(X.Sx, ok, _ => sp.g(S.b("HsPrelude.N"), S.b("natSub"), "var"), _ => y)

# Local polymorphism -----------------------------------------------------------
#
# A local function that GHC generalised (or whose signature is polymorphic)
# has type variables of its own, and perhaps dictionaries: (abs TVS DICTS
# ((export (l N I) TYPE)) EVBINDS BINDS), each use of it (evapp (tyapp (l N
# I) T) D). When every use outside it is at the same types, and those are in
# scope at it, it is read as the function at those types: its variables
# replaced by them, its dictionaries by the first use's, no foralls, no
# constraints, and its uses plain. (The same types' dictionaries are the
# same: a class has one instance at a type.) A local function at two types
# stays as it was.

# a local (l N I), its type's variables, and how many dictionaries it takes
type Lm is Data:
  Lm{id: X.Sx, vs: List<&2, List<&2, U32>>, k: Nat}

# a use's types and dictionaries (ok: whether it takes them all)
type Lu is Data:
  Lu{ts: List<&2, X.Sx>, ds: List<&2, X.Sx>, ok: Bool}

# a type's first foralls' variables
def sp.lm.vs(t: X.Sx) -> List<&2, List<&2, U32>>:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+v}, X.SxCons{+r, X.SxNil{}}}}:
      sp.if(List<&2, List<&2, U32>>, sp.is(a, "tforall"), _ => v <> sp.lm.vs(r), _ => Nil{})
    case _:
      Nil{}

# a type without its first foralls
def sp.lm.body(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+v, X.SxCons{+r, X.SxNil{}}}}:
      sp.if(X.Sx, sp.is(a, "tforall"), _ => sp.lm.body(r), _ => X.SxCons{X.SxAtom{a}, X.SxCons{v, X.SxCons{r, X.SxNil{}}}})
    case z:
      z

# how many constraints a type takes first, and it without them
def sp.lm.ctx(t: X.Sx) -> Nat:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{c, X.SxCons{+r, X.SxNil{}}}}:
      sp.if(Nat, sp.is(a, "tctx"), _ => 1n+sp.lm.ctx(r), _ => 0n)
    case _:
      0n

def sp.lm.unctx(t: X.Sx) -> X.Sx:
  match t:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+c, X.SxCons{+r, X.SxNil{}}}}:
      sp.if(X.Sx, sp.is(a, "tctx"), _ => sp.lm.unctx(r), _ => X.SxCons{X.SxAtom{a}, X.SxCons{c, X.SxCons{r, X.SxNil{}}}})
    case z:
      z

def sp.lm.id(m: Lm) -> X.Sx:
  match m:
    case Lm{i, vs, k}:
      i

def sp.lm.mvs(m: Lm) -> List<&2, List<&2, U32>>:
  match m:
    case Lm{i, vs, k}:
      vs

def sp.lm.mk(m: Lm) -> Nat:
  match m:
    case Lm{i, vs, k}:
      k

# a local abs's local, when it is polymorphic (and of rank 1)
def sp.lm.of(+y: X.Sx) -> List<&2, Lm>:
  +es = sp.at(y, 3n)
  +e = sp.at(es, 0n)
  +t = sp.at(e, 2n)
  +vs = sp.lm.vs(t)
  +b = sp.lm.body(t)
  +r1 = Bool.not(sp.head.is(sp.lm.unctx(b), "tforall"))
  +one = Bool.and(Nat.is_eq(X.tsx.len(es), 1n), sp.head.is(sp.at(e, 1n), "l"))
  sp.if(List<&2, Lm>, Bool.and(Bool.and(one, r1), Bool.not(List.is_empty(&2, List<&2, U32>, vs))), _ => [Lm{sp.at(e, 1n), vs, sp.lm.ctx(b)}], _ => Nil{})

# the polymorphic locals of x
def sp.lm.all(x: X.Sx) -> List<&2, Lm>:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +a = Bool.and(sp.head.is(y, "abs"), Nat.is_gt(X.tsx.len(y), 5n))
      List.append(&2, Lm, sp.if(List<&2, Lm>, a, _ => sp.lm.of(y), _ => Nil{}), List.append(&2, Lm, sp.lm.all(h), sp.lm.all(t)))
    case _:
      Nil{}

def sp.lm.is(+y: X.Sx, +i: X.Sx) -> Bool:
  sp.if(Bool, sp.head.is(y, "l"), _ => sp.eq(y, i), _ => False{})

# the types, then the dictionaries, i is applied to in y
def sp.lm.peelt(n: Nat, +y: X.Sx, +i: X.Sx, +ts: List<&2, X.Sx>, +ds: List<&2, X.Sx>) -> Maybe<&2, Lu>:
  match n:
    case 0n:
      sp.if(Maybe<&2, Lu>, sp.lm.is(y, i), _ => Some{Lu{ts, ds, True{}}}, _ => None{})
    case 1n+p:
      sp.if(Maybe<&2, Lu>, sp.head.is(y, "tyapp"), _ => sp.lm.peelt(p, sp.at(y, 1n), i, sp.at(y, 2n) <> ts, ds), _ => None{})

def sp.lm.peeld(k: Nat, +n: Nat, +y: X.Sx, +i: X.Sx, +ds: List<&2, X.Sx>) -> Maybe<&2, Lu>:
  match k:
    case 0n:
      sp.lm.peelt(n, y, i, Nil{}, ds)
    case 1n+p:
      sp.if(Maybe<&2, Lu>, sp.head.is(y, "evapp"), _ => sp.lm.peeld(p, n, sp.at(y, 1n), i, sp.at(y, 2n) <> ds), _ => None{})

def sp.lm.peel(+y: X.Sx, +m: Lm) -> Maybe<&2, Lu>:
  +app = Bool.or(sp.head.is(y, "tyapp"), sp.head.is(y, "evapp"))
  sp.if(Maybe<&2, Lu>, app, _ => sp.lm.peeld(sp.lm.mk(m), List.length(&2, List<&2, U32>, sp.lm.mvs(m)), y, sp.lm.id(m), Nil{}), _ => None{})

# its uses (not its binding's own names, nor (self ..), it at its own types)
def sp.lm.uses(x: X.Sx, +m: Lm) -> List<&2, Lu>:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +u = sp.lm.peel(y, m)
      +own = Bool.or(sp.head.is(y, "self"), Bool.and(sp.head.is(y, "export"), sp.lm.is(sp.at(y, 1n), sp.lm.id(m))))
      sp.if(List<&2, Lu>, Maybe.is_some(&2, Lu, u), _ => [Maybe.default(&2, Lu, u, Lu{Nil{}, Nil{}, False{}})], _ => sp.if(List<&2, Lu>, own, _ => Nil{}, _ => sp.if(List<&2, Lu>, sp.lm.is(y, sp.lm.id(m)), _ => [Lu{Nil{}, Nil{}, False{}}], _ => List.append(&2, Lu, sp.lm.uses(h, m), sp.lm.uses(t, m)))))
    case _:
      Nil{}

def sp.lm.eqs(a: List<&2, X.Sx>, b: List<&2, X.Sx>) -> Bool:
  match a b:
    case +x <> t +y <> u:
      Bool.and(sp.eq(x, y), sp.lm.eqs(t, u))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

# whether the types are the variables themselves (a use in its own binding)
def sp.lm.own(ts: List<&2, X.Sx>, vs: List<&2, List<&2, U32>>) -> Bool:
  match ts vs:
    case +t <> r +v <> u:
      Bool.and(Bool.and(sp.head.is(t, "tv"), S.eq(sp.sat(t, 1n), v)), sp.lm.own(r, u))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

# the uses that are not its own, and the one they all are
def sp.lm.ext(us: List<&2, Lu>, +vs: List<&2, List<&2, U32>>) -> List<&2, Lu>:
  match us:
    case Lu{+ts, +ds, +ok} <> +r:
      sp.if(List<&2, Lu>, Bool.and(ok, sp.lm.own(ts, vs)), _ => sp.lm.ext(r, vs), _ => Lu{ts, ds, ok} <> sp.lm.ext(r, vs))
    case Nil{}:
      Nil{}

def sp.lm.same(us: List<&2, Lu>, +ts: List<&2, X.Sx>) -> Bool:
  match us:
    case Lu{+ts1, ds, +ok} <> r:
      Bool.and(Bool.and(ok, sp.lm.eqs(ts1, ts)), sp.lm.same(r, ts))
    case Nil{}:
      True{}

def sp.lm.one(us: List<&2, Lu>) -> Maybe<&2, Lu>:
  match us:
    case Lu{+ts, +ds, +ok} <> +r:
      sp.if(Maybe<&2, Lu>, Bool.and(ok, sp.lm.same(r, ts)), _ => Some{Lu{ts, ds, ok}}, _ => None{})
    case Nil{}:
      None{}

# What is in scope at any local of a top (abs TVS DICTS EXPORTS EVBINDS
# BINDS): its type variables and dictionaries, and its binding's wrapper's,
# which are outside its clauses (matches); not a clause's own.
def sp.lm.sc.tvs(x: X.Sx) -> List<&2, List<&2, U32>>:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +v = sp.if(List<&2, List<&2, U32>>, sp.head.is(y, "tylam"), _ => [sp.sat(y, 1n)], _ => Nil{})
      sp.if(List<&2, List<&2, U32>>, sp.head.is(y, "matches"), _ => Nil{}, _ => List.append(&2, List<&2, U32>, v, List.append(&2, List<&2, U32>, sp.lm.sc.tvs(h), sp.lm.sc.tvs(t))))
    case _:
      Nil{}

def sp.lm.strs(xs: List<&2, X.Sx>) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxStr{+s} <> t:
      s <> sp.lm.strs(t)
    case _ <> t:
      sp.lm.strs(t)
    case Nil{}:
      Nil{}

# the (l N I) that x binds, (bv (l N I) T); with top, not a clause's
def sp.lm.bvs(x: X.Sx, +top: Bool) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +v = sp.if(List<&2, X.Sx>, sp.head.is(y, "bv"), _ => [sp.at(y, 1n)], _ => Nil{})
      sp.if(List<&2, X.Sx>, Bool.and(top, sp.head.is(y, "matches")), _ => Nil{}, _ => List.append(&2, X.Sx, v, List.append(&2, X.Sx, sp.lm.bvs(h, top), sp.lm.bvs(t, top))))
    case _:
      Nil{}

def sp.lm.mem(xs: List<&2, X.Sx>, +y: X.Sx) -> Bool:
  match xs:
    case +x <> t:
      Bool.or(sp.eq(x, y), sp.lm.mem(t, y))
    case Nil{}:
      False{}

# whether every type variable of x is one of vs
def sp.lm.tvsin(x: X.Sx, +vs: List<&2, List<&2, U32>>) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      sp.if(Bool, sp.istv(h, t), _ => S.mem(X.tsx.str.of(sp.at(t, 0n)), vs), _ => Bool.and(sp.lm.tvsin(h, vs), sp.lm.tvsin(t, vs)))
    case _:
      True{}

# whether every local of x is in scope (one of sc, or bound nowhere in the top)
def sp.lm.locsin(x: X.Sx, +sc: List<&2, X.Sx>, +al: List<&2, X.Sx>) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      sp.if(Bool, sp.head.is(y, "l"), _ => Bool.or(sp.lm.mem(sc, y), Bool.not(sp.lm.mem(al, y))), _ => Bool.and(sp.lm.locsin(h, sc, al), sp.lm.locsin(t, sc, al)))
    case _:
      True{}

def sp.lm.allin(xs: List<&2, X.Sx>, +vs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case +x <> t:
      Bool.and(sp.lm.tvsin(x, vs), sp.lm.allin(t, vs))
    case Nil{}:
      True{}

def sp.lm.alllocs(xs: List<&2, X.Sx>, +sc: List<&2, X.Sx>, +al: List<&2, X.Sx>) -> Bool:
  match xs:
    case +x <> t:
      Bool.and(sp.lm.locsin(x, sc, al), sp.lm.alllocs(t, sc, al))
    case Nil{}:
      True{}

# (top ABS): in scope there. A top varbind's clauses are in its expression,
# so a top that is one has only its abs's.
def sp.lm.scope.ok(+x: X.Sx, +u: Lu) -> Bool:
  match u:
    case Lu{+ts, +ds, ok}:
      +ab = sp.at(x, 1n)
      +vb = sp.head.is(sp.at(sp.at(ab, 5n), 0n), "varbind")
      +head = sp.l([sp.at(ab, 2n), sp.at(ab, 4n)])
      +body = Bool.pick(X.Sx, vb, X.SxNil{}, sp.at(ab, 5n))
      +vs = List.append(&2, List<&2, U32>, sp.lm.strs(sp.els(sp.at(ab, 1n))), sp.lm.sc.tvs(body))
      sp.if(Bool, sp.lm.allin(ts, vs), _ => sp.if(Bool, List.is_empty(&2, X.Sx, ds), _ => True{}, _ => sp.lm.alllocs(ds, List.append(&2, X.Sx, sp.lm.bvs(head, True{}), sp.lm.bvs(body, True{})), sp.lm.bvs(x, False{}))), _ => False{})

# The reading ------------------------------------------------------------------

type Lb is Data:
  Lb{d: X.Sx, by: X.Sx}

def sp.lm.sbs(vs: List<&2, List<&2, U32>>, ts: List<&2, X.Sx>) -> List<&2, Sb>:
  match vs ts:
    case v <> r t <> u:
      Sb{v, t} <> sp.lm.sbs(r, u)
    case _ _:
      Nil{}

def sp.lm.lbs(bs: List<&2, X.Sx>, ds: List<&2, X.Sx>) -> List<&2, Lb>:
  match bs ds:
    case b <> r d <> u:
      Lb{b, d} <> sp.lm.lbs(r, u)
    case _ _:
      Nil{}

def sp.lm.lb(ls: List<&2, Lb>, +y: X.Sx) -> Maybe<&2, X.Sx>:
  match ls:
    case Lb{+d, by} <> t:
      sp.if(Maybe<&2, X.Sx>, sp.eq(d, y), _ => Some{by}, _ => sp.lm.lb(t, y))
    case Nil{}:
      None{}

# a type variable's application at a type, (tapp (tc M N A..) T), as the
# type (tc M N A.. T)
def sp.lm.tapp(+z: X.Sx) -> X.Sx:
  +f = sp.at(z, 1n)
  sp.if(X.Sx, sp.head.is(f, "tc"), _ => sp.l(List.append(&2, X.Sx, sp.els(f), [sp.at(z, 2n)])), _ => z)

# the abs's part x at the types and dictionaries: (tv V) and (l D J)
# replaced, the variables' foralls (and the constraints after) and type
# lambdas gone, and the dictionaries' lambdas
def sp.lm.at(x: X.Sx, +sbs: List<&2, Sb>, +ls: List<&2, Lb>) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +a = sp.hd(y)
      +z = sp.if(X.Sx, sp.istv(h, t), _ => sp.sb.get(sbs, X.tsx.str.of(sp.at(t, 0n)), y), _ => X.SxCons{sp.lm.at(h, sbs, ls), sp.lm.at(t, sbs, ls)})
      +fa = Bool.and(sp.is(a, "tforall"), sp.sb.has(sbs, sp.sat(y, 1n)))
      +tl = Bool.and(sp.is(a, "tylam"), sp.sb.has(sbs, sp.sat(y, 1n)))
      +el = Bool.and(sp.is(a, "evlam"), Maybe.is_some(&2, X.Sx, sp.lm.lb(ls, sp.at(sp.at(y, 1n), 1n))))
      +d = sp.if(Maybe<&2, X.Sx>, sp.is(a, "l"), _ => sp.lm.lb(ls, y), _ => None{})
      sp.if(X.Sx, fa, _ => sp.lm.unctx(sp.at(z, 2n)), _ => sp.if(X.Sx, Bool.or(tl, el), _ => sp.at(z, 2n), _ => sp.if(X.Sx, sp.is(a, "tapp"), _ => sp.lm.tapp(z), _ => Maybe.default(&2, X.Sx, d, z))))
    case w:
      w

# the dictionaries a local's binding takes: its abs's, or its wrapper's
# (a binding with a signature: (tylam V (evlam (bv (l D J) T) ..)))
def sp.lm.bvids(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case +x <> t:
      sp.at(x, 1n) <> sp.lm.bvids(t)
    case Nil{}:
      Nil{}

def sp.lm.evs(w: X.Sx) -> List<&2, X.Sx>:
  match w:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+b, X.SxCons{+r, X.SxNil{}}}}:
      sp.if(List<&2, X.Sx>, sp.is(a, "tylam"), _ => sp.lm.evs(r), _ => sp.if(List<&2, X.Sx>, sp.is(a, "evlam"), _ => sp.at(b, 1n) <> sp.lm.evs(r), _ => Nil{}))
    case _:
      Nil{}

def sp.lm.dicts(+y: X.Sx) -> List<&2, X.Sx>:
  +ds = sp.els(sp.at(y, 2n))
  +b = sp.at(sp.at(y, 5n), 0n)
  +w = sp.if(X.Sx, sp.head.is(b, "fun"), _ => sp.at(b, 5n), _ => sp.at(b, 3n))
  sp.if(List<&2, X.Sx>, List.is_empty(&2, X.Sx, ds), _ => sp.lm.evs(w), _ => sp.lm.bvids(ds))

def sp.lm.abs(+y: X.Sx, +m: Lm, u: Lu) -> X.Sx:
  match u:
    case Lu{ts, ds, ok}:
      +z = sp.lm.at(y, sp.lm.sbs(sp.lm.mvs(m), ts), sp.lm.lbs(sp.lm.dicts(y), ds))
      sp.l(List.append(&2, X.Sx, [sp.a("abs"), X.SxNil{}, X.SxNil{}, sp.at(z, 3n), sp.at(z, 4n), sp.at(z, 5n)], sp.pc.drop(6n, sp.els(z))))

# x with m's binding read at u and its uses plain
def sp.lm.put(x: X.Sx, +m: Lm, +u: Lu) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +z = {X.SxCons{sp.lm.put(h, m, u), sp.lm.put(t, m, u)} : X.Sx}
      +ab = Bool.and(Bool.and(sp.head.is(y, "abs"), Nat.is_gt(X.tsx.len(y), 5n)), sp.lm.is(sp.at(sp.at(sp.at(y, 3n), 0n), 1n), sp.lm.id(m)))
      sp.if(X.Sx, Maybe.is_some(&2, Lu, sp.lm.peel(y, m)), _ => sp.lm.id(m), _ => sp.if(X.Sx, ab, _ => sp.lm.abs(z, m, u), _ => z))
    case w:
      w

# a use's dictionary bound where its local is not in scope (the evbinds of a
# binding beside it: GHC gives each binding its own) is what it is bound to,
# when that is ($fOrdInt, or in terms of what is in scope)
def sp.lm.evbs(x: X.Sx) -> List<&2, Lb>:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +r = List.append(&2, Lb, sp.lm.evbs(h), sp.lm.evbs(t))
      sp.if(List<&2, Lb>, sp.head.is(y, "evbind"), _ => Lb{sp.at(sp.at(y, 1n), 1n), sp.at(y, 2n)} <> r, _ => r)
    case _:
      Nil{}

def sp.lm.putev(x: X.Sx, +evs: List<&2, Lb>) -> X.Sx:
  match x:
    case X.SxCons{+h, +t}:
      +y = {X.SxCons{h, t} : X.Sx}
      +d = sp.if(Maybe<&2, X.Sx>, sp.head.is(y, "l"), _ => sp.lm.lb(evs, y), _ => None{})
      sp.if(X.Sx, Maybe.is_some(&2, X.Sx, d), _ => Maybe.default(&2, X.Sx, d, y), _ => X.SxCons{sp.lm.putev(h, evs), sp.lm.putev(t, evs)})
    case w:
      w

def sp.lm.resolve(fuel: Nat, d: X.Sx, +evs: List<&2, Lb>) -> X.Sx:
  match fuel:
    case 0n:
      d
    case 1n+p:
      sp.lm.resolve(p, sp.lm.putev(d, evs), evs)

def sp.lm.resolves(ds: List<&2, X.Sx>, +evs: List<&2, Lb>) -> List<&2, X.Sx>:
  match ds:
    case d <> t:
      sp.lm.resolve(6n, d, evs) <> sp.lm.resolves(t, evs)
    case Nil{}:
      Nil{}

def sp.lm.resolved(u: Lu, +x: X.Sx) -> Lu:
  match u:
    case Lu{ts, ds, ok}:
      Lu{ts, sp.lm.resolves(ds, sp.lm.evbs(x)), ok}

# the first of ms that can be read so, done (None: none can)
def sp.lm.try(+x: X.Sx, ms: List<&2, Lm>) -> Maybe<&2, X.Sx>:
  match ms:
    case +m <> t:
      +u = sp.lm.one(sp.lm.ext(sp.lm.uses(x, m), sp.lm.mvs(m)))
      +v = Maybe.default(&2, Lu, u, Lu{Nil{}, Nil{}, False{}})
      +some = Maybe.is_some(&2, Lu, u)
      +ok0 = sp.if(Bool, some, _ => sp.lm.scope.ok(x, v), _ => False{})
      +w = sp.if(Lu, Bool.and(some, Bool.not(ok0)), _ => sp.lm.resolved(v, x), _ => v)
      +ok = sp.if(Bool, Bool.or(ok0, Bool.not(some)), _ => ok0, _ => sp.lm.scope.ok(x, w))
      sp.if(Maybe<&2, X.Sx>, ok, _ => Some{sp.lm.put(x, m, w)}, _ => sp.lm.try(x, t))
    case Nil{}:
      None{}

def sp.lm.go(fuel: Nat, +x: X.Sx) -> X.Sx:
  match fuel:
    case 0n:
      x
    case 1n+p:
      +ms = sp.lm.all(x)
      +r = sp.if(Maybe<&2, X.Sx>, List.is_empty(&2, Lm, ms), _ => None{}, _ => sp.lm.try(x, ms))
      sp.if(X.Sx, Maybe.is_some(&2, X.Sx, r), _ => sp.lm.go(p, Maybe.default(&2, X.Sx, r, x)), _ => x)

# a top's local functions read at their one type
def sp.lm(+x: X.Sx) -> X.Sx:
  sp.if(X.Sx, sp.head.is(x, "top"), _ => sp.lm.go(64n, x), _ => x)

# an arithmetic sequence (arith ENUM (fromto A B)) as ENUM's call, enumFromTo
# A B, and (fromthento A B C), A and B two different literals, as
# enumFromThenTo A B C (two equal ones are an endless list, or none)
def sp.arith.lit(+x: X.Sx) -> Bool:
  Bool.and(sp.head.is(x, "olit"), sp.head.is(sp.at(x, 1n), "int"))

def sp.arith(+y: X.Sx) -> X.Sx:
  +w = sp.at(y, 1n)
  +k = sp.at(y, 2n)
  +a = sp.at(k, 1n)
  +b = sp.at(k, 2n)
  +ft = sp.head.is(k, "fromto")
  +fs = Bool.and(sp.head.is(k, "fromthento"), Bool.and(Bool.and(sp.arith.lit(a), sp.arith.lit(b)), Bool.not(sp.eq(sp.at(a, 1n), sp.at(b, 1n)))))
  +c2 = sp.l([sp.a("app"), sp.l([sp.a("app"), w, a]), b])
  sp.if(X.Sx, ft, _ => c2, _ => sp.if(X.Sx, fs, _ => sp.l([sp.a("app"), c2, sp.at(k, 3n)]), _ => y))

# divMod a b as (div a b, mod a b), quotRem a b as (quot a b, rem a b), where
# a and b bind nothing (each is written twice; GHC's own error at b 0 is
# div's)
def sp.divmod.put(x: X.Sx, +n: String) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+t, X.SxNil{}}}}:
      sp.if(X.Sx, Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp")), _ => sp.l([X.SxAtom{a}, sp.divmod.put(f, n), t]), _ => sp.l([X.SxAtom{a}, f, t]))
    case X.SxCons{X.SxAtom{+a}, X.SxCons{X.SxStr{+m}, X.SxCons{X.SxStr{o}, X.SxCons{+k, X.SxNil{}}}}}:
      sp.l([X.SxAtom{a}, X.SxStr{m}, X.SxStr{S.b(n)}, k])
    case z:
      z

def sp.divmod.two(+h: X.Sx, +a: X.Sx, +b: X.Sx, +p: String, +q: String) -> X.Sx:
  +one = sp.l([sp.a("app"), sp.l([sp.a("app"), sp.divmod.put(h, p), a]), b])
  +two = sp.l([sp.a("app"), sp.l([sp.a("app"), sp.divmod.put(h, q), a]), b])
  sp.l([sp.a("tuple"), one, two])

def sp.divmod(+y: X.Sx) -> X.Sx:
  +f = sp.at(y, 1n)
  +h = sp.at(f, 1n)
  +a = sp.at(f, 2n)
  +b = sp.at(y, 2n)
  +ap = Bool.and(sp.head.is(f, "app"), sp.head.is(h, "evapp"))
  +k = sp.if(List<&2, U32>, ap, _ => sp.pc.key(sp.pc.peel(h, Nil{}, Nil{})), _ => Nil{})
  +dm = sp.is(k, "GHC.Internal.Real.divMod")
  +qr = sp.is(k, "GHC.Internal.Real.quotRem")
  +ok = sp.if(Bool, Bool.or(dm, qr), _ => Bool.not(Bool.or(sp.has(a, S.b("bv")), sp.has(b, S.b("bv")))), _ => False{})
  sp.if(X.Sx, ok, _ => Bool.pick(X.Sx, dm, sp.divmod.two(h, a, b, "div", "mod"), sp.divmod.two(h, a, b, "quot", "rem")), _ => y)

# a type variable GHC found no type for (ZonkAny n): nothing looks at a
# value of it, so any type is it, and here it is ()
def sp.zonk.at(+y: X.Sx) -> X.Sx:
  sp.if(X.Sx, Bool.and(S.eq(X.tsx.str.of(sp.at(y, 1n)), S.b("GHC.Types")), S.eq(X.tsx.str.of(sp.at(y, 2n)), S.b("ZonkAny"))), _ => sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{}), _ => y)

# the export's clauses and local pattern bindings as the fold reads them
# (cts: the package's constructors, for a pattern's type)
def sp.pb.tl(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      t
    case z:
      z

# A pattern binding of an as pattern, `let v@p = e`, is two: v = e, and then
# p = v (the fold's patbind takes a constructor's pattern).
def sp.pb.isas.at(+abs: X.Sx) -> Bool:
  +bs = sp.at(abs, 5n)
  +b = sp.at(bs, 0n)
  Bool.and(Bool.and(sp.head.is(abs, "abs"), Nat.is_eq(X.tsx.len(bs), 1n)), Bool.and(sp.head.is(b, "patbind"), sp.head.is(sp.at(b, 1n), "pas")))

def sp.pb.isas(+n: X.Sx) -> Bool:
  sp.if(Bool, sp.head.is(n, "nonrec"), _ => sp.pb.isas.at(sp.at(n, 1n)), _ => False{})

def sp.pb.exp(es: List<&2, X.Sx>, +v: X.Sx) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      +rest = sp.pb.exp(t, v)
      sp.if(List<&2, X.Sx>, sp.eq(sp.at(e, 1n), v), _ => rest, _ => e <> rest)

def sp.pb.abs(+old: X.Sx, es: X.Sx, ev: X.Sx, b: X.Sx, +q: List<&2, X.Sx>) -> X.Sx:
  sp.l(sp.a("nonrec") <> sp.l([sp.a("abs"), sp.at(old, 1n), sp.at(old, 2n), es, ev, sp.l([b])]) <> q)

def sp.pb.as(+n: X.Sx, rest: X.Sx) -> X.Sx:
  +abs = sp.at(n, 1n)
  +q = List.drop(&2, X.Sx, sp.els(n), 2n)
  +b = sp.at(sp.at(abs, 5n), 0n)
  +bv = sp.at(sp.at(b, 1n), 1n)
  +v = sp.at(bv, 1n)
  +ty = sp.at(bv, 2n)
  +fun = sp.l([sp.a("fun"), sp.l([sp.a("self"), v]), ty, sp.at(b, 2n), sp.l([sp.a("matches"), X.SxNil{}, ty, sp.a("source"), sp.l([sp.l([sp.a("match"), X.SxNil{}, sp.at(b, 3n)])])]), sp.a("hole")])
  +pat = sp.l(sp.a("patbind") <> sp.at(sp.at(b, 1n), 2n) <> sp.at(b, 2n) <> sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, v])]), sp.l([sp.a("binds")])]) <> List.drop(&2, X.Sx, sp.els(b), 4n))
  X.SxCons{sp.pb.abs(abs, sp.l([sp.l([sp.a("export"), v, ty])]), sp.at(abs, 4n), fun, q), X.SxCons{sp.pb.abs(abs, sp.l(sp.pb.exp(sp.els(sp.at(abs, 3n)), v)), sp.l([sp.l([sp.a("evbinds")])]), pat, q), rest}}

def sp.pb(x: X.Sx, +cts: List<&2, Ct>) -> X.Sx:
  match x:
    case X.SxCons{h, t}:
      +y = {X.SxCons{sp.pb(h, cts), sp.pb(t, cts)} : X.Sx}
      +a = sp.hd(y)
      sp.if(X.Sx, sp.pb.isas(sp.at(y, 0n)), _ => sp.pb.as(sp.at(y, 0n), sp.pb.tl(y)), _ => sp.if(X.Sx, sp.is(a, "patbind"), _ => sp.pb.at(y, cts), _ => sp.if(X.Sx, sp.is(a, "match"), _ => sp.ftw.at(y), _ => sp.if(X.Sx, sp.is(a, "grhs"), _ => sp.ftw.grhs(y, cts), _ => sp.if(X.Sx, sp.is(a, "evapp"), _ => sp.natsub(y), _ => sp.if(X.Sx, sp.is(a, "arith"), _ => sp.arith(y), _ => sp.if(X.Sx, sp.is(a, "app"), _ => sp.divmod(y), _ => sp.if(X.Sx, sp.is(a, "tc"), _ => sp.zonk.at(y), _ => y))))))))
    case z:
      z

# Safe subtraction -------------------------------------------------------------------
#
# x - y at Int and Integer is out of a module alone (int-sub: F reads them as
# Nat), and at Natural it is an error below 0. But where what is around it
# says x >= y it is Nat's subtraction: n - 1 in the else of n <= 0, a - b in
# the else of a < b, n - 2 in f n after f 0 and f 1. sp.ssb walks a tree with
# the facts its tests give (an if's, a guard's and the ones before it, the
# literals a clause before this one took) and writes such a subtraction as
# HsPrelude.N's subSafe at the same type, which the survey takes and the fold
# reads as -. A fact is about an expression as it stands (locals are
# numbered, so a name hides nothing, and an expression has one value), and
# holds in the branch its test chose. Every Int is 0 or more here, as F
# reads it; `max k (a - b)` at Int is max k of Nat's subtraction at any a
# and b, and abs (a - b), a and b locals, (a - b) + (b - a), each Nat's.

# an expression is at least k; is not k; is at least another, is greater; a
# subtraction at a type variable may be read as Integer's
type Mf is Data:
  MfLo{v: X.Sx, k: Nat}
  MfNe{v: X.Sx, k: Nat}
  MfGe{a: X.Sx, b: X.Sx}
  MfGt{a: X.Sx, b: X.Sx}
  MfTv{}

# digits, at most 6, as a number
def sp.ssb.digits(xs: List<&2, U32>, +acc: Nat, lim: Nat) -> Maybe<&2, Nat>:
  match xs lim:
    case Nil{} 1n+l:
      Some{acc}
    case Con{+c, t} 1n+l:
      Bool.pick(Maybe<&2, Nat>, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), sp.ssb.digits(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))), l), None{})
    case _ 0n:
      None{}

# GHC's expansion of an operator application, opened
def sp.ssb.open(n: Nat, +x: X.Sx) -> X.Sx:
  match n:
    case 0n:
      x
    case 1n+p:
      sp.if(X.Sx, sp.head.is(x, "expanded"), _ => sp.ssb.open(p, sp.at(x, 2n)), _ => x)

# a function without its type and evidence arguments
def sp.ssb.peel(n: Nat, +x: X.Sx) -> X.Sx:
  match n:
    case 0n:
      x
    case 1n+p:
      sp.if(X.Sx, Bool.or(sp.head.is(x, "evapp"), sp.head.is(x, "tyapp")), _ => sp.ssb.peel(p, sp.at(x, 1n)), _ => x)

# a global function's name, M.N
def sp.ssb.key(+f: X.Sx) -> List<&2, U32>:
  +g = sp.ssb.peel(4n, f)
  sp.if(List<&2, U32>, sp.head.is(g, "g"), _ => sp.key(sp.sat(g, 1n), sp.sat(g, 2n)), _ => Nil{})

# a number as it stands: an overloaded literal (olit (int N) TYPE WITNESS), a
# character (its code), ord or fromEnum of one
def sp.ssb.num(olit: Bool, char: Bool, +x: X.Sx) -> Maybe<&2, Nat>:
  match olit char:
    case True{} _:
      sp.ssb.digits(X.tsx.atom.of(sp.at(sp.at(x, 1n), 1n)), 0n, 7n)
    case False{} True{}:
      sp.ssb.digits(X.tsx.atom.of(sp.at(x, 1n)), 0n, 7n)
    case False{} False{}:
      None{}

def sp.ssb.isord(+k: List<&2, U32>) -> Bool:
  Bool.or(sp.is(k, "GHC.Internal.Base.ord"), Bool.or(sp.is(k, "HsPrelude.Z.ord"), sp.is(k, "GHC.Internal.Enum.fromEnum")))

def sp.ssb.ord(+x: X.Sx) -> Bool:
  sp.if(Bool, sp.head.is(x, "app"), _ => sp.ssb.isord(sp.ssb.key(sp.at(x, 1n))), _ => False{})

def sp.ssb.lit(+x: X.Sx) -> Maybe<&2, Nat>:
  +y = sp.if(X.Sx, Bool.and(sp.head.is(sp.at(x, 2n), "char"), sp.ssb.ord(x)), _ => sp.at(x, 2n), _ => x)
  sp.ssb.num(Bool.and(sp.head.is(y, "olit"), sp.head.is(sp.at(y, 1n), "int")), sp.head.is(y, "char"), y)

# the type a function is applied at: (evapp (tyapp F T) D), (tyapp F T)
def sp.ssb.ty(+f: X.Sx) -> X.Sx:
  +t = sp.if(X.Sx, sp.head.is(f, "evapp"), _ => sp.at(f, 1n), _ => f)
  sp.if(X.Sx, sp.head.is(t, "tyapp"), _ => sp.at(t, 2n), _ => X.SxNil{})

# F, A and B of (app (app F A) B), and F and A of (app F A)
def sp.ssb.two(+x: X.Sx) -> Bool:
  Bool.and(sp.head.is(x, "app"), sp.head.is(sp.at(x, 1n), "app"))

def sp.ssb.f2(+x: X.Sx) -> X.Sx:
  sp.at(sp.at(x, 1n), 1n)

def sp.ssb.a2(+x: X.Sx) -> X.Sx:
  sp.at(sp.at(x, 1n), 2n)

def sp.ssb.b2(+x: X.Sx) -> X.Sx:
  sp.at(x, 2n)

# a number as it stands, or an atom of its digits
def sp.ssb.norm.at(m: Maybe<&2, Nat>, x: X.Sx) -> X.Sx:
  match m:
    case Some{k}:
      X.SxAtom{S.b(Nat.show(k))}
    case None{}:
      x

def sp.ssb.norm(+x: X.Sx) -> X.Sx:
  +y = sp.ssb.open(4n, x)
  sp.ssb.norm.at(sp.ssb.lit(y), y)

# a number's type that Nat is, or a type variable (read at Integer, or out)
def sp.ssb.nat(+t: X.Sx) -> Bool:
  sp.is(sp.tckey(t), "GHC.Num.Natural.Natural")

def sp.ssb.int0(+t: X.Sx) -> Bool:
  +k = sp.tckey(t)
  Bool.or(sp.is(k, "GHC.Types.Int"), sp.is(k, "GHC.Num.Integer.Integer"))

def sp.ssb.int(+t: X.Sx) -> Bool:
  Bool.or(sp.head.is(t, "tv"), sp.ssb.int0(t))

# whether x is X - Y, at a type of those; and the type
def sp.ssb.issub2(+x: X.Sx) -> Bool:
  +f = sp.ssb.f2(x)
  +k = sp.ssb.key(f)
  +t = sp.ssb.ty(f)
  Bool.or(sp.is(k, "HsPrelude.N.natSub"), Bool.and(sp.is(k, "GHC.Internal.Num.-"), Bool.or(sp.ssb.nat(t), sp.ssb.int(t))))

def sp.ssb.issub(+x: X.Sx) -> Bool:
  sp.if(Bool, sp.ssb.two(x), _ => sp.ssb.issub2(x), _ => False{})

def sp.ssb.subty(+x: X.Sx) -> X.Sx:
  +f = sp.ssb.f2(x)
  sp.if(X.Sx, sp.is(sp.ssb.key(f), "HsPrelude.N.natSub"), _ => sp.tc(S.b("GHC.Num.Natural"), S.b("Natural"), Nil{}), _ => sp.ssb.ty(f))

def sp.ssb.safe.op(t: X.Sx) -> X.Sx:
  sp.l([sp.a("tyapp"), sp.g(S.b("HsPrelude.N"), S.b("subSafe"), "var"), t])

# Facts

def sp.ssb.max(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), b, a)

# the greatest bound the facts give an expression
def sp.ssb.los(fs: List<&2, Mf>, +v: X.Sx, +acc: Nat) -> Nat:
  match fs:
    case Nil{}:
      acc
    case MfLo{w, +k} <> t:
      sp.ssb.los(t, v, Bool.pick(Nat, sp.eq(w, v), sp.ssb.max(k, acc), acc))
    case _ <> t:
      sp.ssb.los(t, v, acc)

def sp.ssb.isne(fs: List<&2, Mf>, +v: X.Sx, +k: Nat) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case MfNe{w, j} <> t:
      Bool.or(Bool.and(Nat.is_eq(j, k), sp.eq(w, v)), sp.ssb.isne(t, v, k))
    case _ <> t:
      sp.ssb.isne(t, v, k)

# at least k and not k: at least k + 1
def sp.ssb.bump(n: Nat, +fs: List<&2, Mf>, +v: X.Sx, +k: Nat) -> Nat:
  match n:
    case 0n:
      k
    case 1n+p:
      sp.if(Nat, sp.ssb.isne(fs, v, k), _ => sp.ssb.bump(p, fs, v, 1n+k), _ => k)

def sp.ssb.mget(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case Some{k}:
      k
    case None{}:
      d

def sp.ssb.isgt(fs: List<&2, Mf>, +a: X.Sx, +b: X.Sx) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case MfGt{c, d} <> t:
      Bool.or(Bool.and(sp.eq(c, a), sp.eq(d, b)), sp.ssb.isgt(t, a, b))
    case _ <> t:
      sp.ssb.isgt(t, a, b)

# what an expression is at least: a literal, a sum, a difference by a
# literal, and what the facts say
def sp.ssb.lo(n: Nat, +x: X.Sx, +fs: List<&2, Mf>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n++p:
      +y = sp.ssb.open(4n, x)
      +b = sp.ssb.bump(12n, fs, y, sp.ssb.los(fs, y, 0n))
      +two = sp.ssb.two(y)
      +k = sp.if(List<&2, U32>, two, _ => sp.ssb.key(sp.ssb.f2(y)), _ => Nil{})
      +plus = sp.if(Nat, sp.is(k, "GHC.Internal.Num.+"), _ => Nat.add(sp.ssb.lo(p, sp.ssb.a2(y), fs), sp.ssb.lo(p, sp.ssb.b2(y), fs)), _ => 0n)
      +less = sp.if(Nat, sp.ssb.issub(y), _ => sp.ssb.max(Bool.pick(Nat, sp.ssb.isgt(fs, sp.ssb.norm(sp.ssb.a2(y)), sp.ssb.norm(sp.ssb.b2(y))), 1n, 0n), Nat.sub(sp.ssb.lo(p, sp.ssb.a2(y), fs), sp.ssb.mget(sp.ssb.lit(sp.ssb.open(4n, sp.ssb.b2(y))), 4000000000n))), _ => 0n)
      +ord = sp.if(Nat, sp.ssb.ord(y), _ => sp.ssb.lo(p, sp.at(y, 2n), fs), _ => 0n)
      sp.ssb.mget(sp.ssb.lit(y), sp.ssb.max(b, sp.ssb.max(ord, sp.ssb.max(plus, less))))

def sp.ssb.isge(fs: List<&2, Mf>, +a: X.Sx, +b: X.Sx) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case MfGe{c, d} <> t:
      Bool.or(Bool.and(sp.eq(c, a), sp.eq(d, b)), sp.ssb.isge(t, a, b))
    case _ <> t:
      sp.ssb.isge(t, a, b)

def sp.ssb.atleast(m: Maybe<&2, Nat>, +x: X.Sx, +fs: List<&2, Mf>) -> Bool:
  match m:
    case Some{k}:
      Nat.is_ge(sp.ssb.lo(4n, x, fs), k)
    case None{}:
      False{}

# whether x >= y
def sp.ssb.ge(+x: X.Sx, +y: X.Sx, +fs: List<&2, Mf>) -> Bool:
  +a = sp.ssb.norm(x)
  +b = sp.ssb.norm(y)
  sp.if(Bool, Bool.or(sp.eq(a, b), sp.ssb.isge(fs, a, b)), _ => True{}, _ => sp.ssb.atleast(sp.ssb.lit(sp.ssb.open(4n, y)), x, fs))

# the fact a >= b (strict: a > b)
def sp.ssb.add.lit(m: Maybe<&2, Nat>, strict: Bool, +a: X.Sx, fs: List<&2, Mf>) -> List<&2, Mf>:
  match m strict:
    case Some{k} True{}:
      MfLo{sp.ssb.open(4n, a), 1n+k} <> fs
    case Some{k} False{}:
      MfLo{sp.ssb.open(4n, a), k} <> fs
    case None{} True{}:
      MfLo{sp.ssb.open(4n, a), 1n} <> fs
    case None{} False{}:
      fs

def sp.ssb.add.gt(strict: Bool, a: X.Sx, b: X.Sx, fs: List<&2, Mf>) -> List<&2, Mf>:
  match strict:
    case True{}:
      MfGt{a, b} <> fs
    case False{}:
      fs

def sp.ssb.add.ge(+a: X.Sx, +b: X.Sx, +strict: Bool, fs: List<&2, Mf>) -> List<&2, Mf>:
  +na = sp.ssb.norm(a)
  +nb = sp.ssb.norm(b)
  MfGe{na, nb} <> sp.ssb.add.gt(strict, na, nb, sp.ssb.add.lit(sp.ssb.lit(sp.ssb.open(4n, b)), strict, a, fs))

def sp.ssb.add.ne(m: Maybe<&2, Nat>, +a: X.Sx, fs: List<&2, Mf>) -> List<&2, Mf>:
  match m:
    case Some{k}:
      MfNe{sp.ssb.open(4n, a), k} <> fs
    case None{}:
      fs

# a comparison's facts, where it holds (pos) or does not
def sp.ssb.rel.t(+k: List<&2, U32>, +a: X.Sx, +b: X.Sx, +fs: List<&2, Mf>) -> List<&2, Mf>:
  +lt = sp.is(k, "GHC.Classes.<")
  +gt = sp.is(k, "GHC.Classes.>")
  sp.if(List<&2, Mf>, Bool.or(lt, sp.is(k, "GHC.Classes.<=")), _ => sp.ssb.add.ge(b, a, lt, fs), _ =>
    sp.if(List<&2, Mf>, Bool.or(gt, sp.is(k, "GHC.Classes.>=")), _ => sp.ssb.add.ge(a, b, gt, fs), _ =>
      sp.if(List<&2, Mf>, sp.is(k, "GHC.Classes.=="), _ => sp.ssb.add.ge(a, b, False{}, sp.ssb.add.ge(b, a, False{}, fs)), _ =>
        sp.if(List<&2, Mf>, sp.is(k, "GHC.Classes./="), _ => sp.ssb.add.ne(sp.ssb.lit(sp.ssb.open(4n, b)), a, sp.ssb.add.ne(sp.ssb.lit(sp.ssb.open(4n, a)), b, fs)), _ => fs))))

def sp.ssb.rel.f(+k: List<&2, U32>, +a: X.Sx, +b: X.Sx, +fs: List<&2, Mf>) -> List<&2, Mf>:
  +le = sp.is(k, "GHC.Classes.<=")
  +ge = sp.is(k, "GHC.Classes.>=")
  sp.if(List<&2, Mf>, Bool.or(le, sp.is(k, "GHC.Classes.<")), _ => sp.ssb.add.ge(a, b, le, fs), _ =>
    sp.if(List<&2, Mf>, Bool.or(ge, sp.is(k, "GHC.Classes.>")), _ => sp.ssb.add.ge(b, a, ge, fs), _ =>
      sp.if(List<&2, Mf>, sp.is(k, "GHC.Classes./="), _ => sp.ssb.add.ge(a, b, False{}, sp.ssb.add.ge(b, a, False{}, fs)), _ =>
        sp.if(List<&2, Mf>, sp.is(k, "GHC.Classes.=="), _ => sp.ssb.add.ne(sp.ssb.lit(sp.ssb.open(4n, b)), a, sp.ssb.add.ne(sp.ssb.lit(sp.ssb.open(4n, a)), b, fs)), _ => fs))))

def sp.ssb.rel(+k: List<&2, U32>, pos: Bool, +a: X.Sx, +b: X.Sx, +fs: List<&2, Mf>) -> List<&2, Mf>:
  match pos:
    case True{}:
      sp.ssb.rel.t(k, a, b, fs)
    case False{}:
      sp.ssb.rel.f(k, a, b, fs)

# the least code of the characters a test takes
def sp.ssb.least(+k: List<&2, U32>) -> Nat:
  +digit = Bool.or(sp.is(k, "GHC.Internal.Unicode.isDigit"), Bool.or(sp.is(k, "GHC.Internal.Unicode.isOctDigit"), Bool.or(sp.is(k, "GHC.Internal.Unicode.isHexDigit"), sp.is(k, "GHC.Internal.Unicode.isAlphaNum"))))
  +upper = Bool.or(sp.is(k, "GHC.Internal.Unicode.isUpper"), Bool.or(sp.is(k, "GHC.Internal.Unicode.isAsciiUpper"), Bool.or(sp.is(k, "GHC.Internal.Unicode.isAlpha"), sp.is(k, "GHC.Internal.Data.Char.isLetter"))))
  +lower = Bool.or(sp.is(k, "GHC.Internal.Unicode.isLower"), sp.is(k, "GHC.Internal.Unicode.isAsciiLower"))
  Bool.pick(Nat, digit, 48n, Bool.pick(Nat, upper, 65n, Bool.pick(Nat, lower, 97n, 0n)))

def sp.ssb.char(pos: Bool, +k: List<&2, U32>, +a: X.Sx, fs: List<&2, Mf>) -> List<&2, Mf>:
  match pos:
    case True{}:
      MfLo{sp.ssb.open(4n, a), sp.ssb.least(k)} <> fs
    case False{}:
      fs

# a test's facts: both of a && b where it holds, both of a || b where it
# does not, not's the other way
def sp.ssb.test(n: Nat, +c: X.Sx, +pos: Bool, +fs: List<&2, Mf>) -> List<&2, Mf>:
  match n:
    case 0n:
      fs
    case 1n++p:
      +x = sp.ssb.open(4n, c)
      +two = sp.ssb.two(x)
      +k = sp.if(List<&2, U32>, two, _ => sp.ssb.key(sp.ssb.f2(x)), _ => sp.if(List<&2, U32>, sp.head.is(x, "app"), _ => sp.ssb.key(sp.at(x, 1n)), _ => Nil{}))
      +both = Bool.and(two, Bool.or(Bool.and(pos, sp.is(k, "GHC.Classes.&&")), Bool.and(Bool.not(pos), sp.is(k, "GHC.Classes.||"))))
      sp.if(List<&2, Mf>, both, _ => sp.ssb.test(p, sp.ssb.a2(x), pos, sp.ssb.test(p, sp.ssb.b2(x), pos, fs)), _ =>
        sp.if(List<&2, Mf>, Bool.and(Bool.not(two), sp.is(k, "GHC.Classes.not")), _ => sp.ssb.test(p, sp.at(x, 2n), Bool.not(pos), fs), _ =>
          sp.if(List<&2, Mf>, two, _ => sp.ssb.rel(k, pos, sp.ssb.a2(x), sp.ssb.b2(x), fs), _ => sp.if(List<&2, Mf>, sp.head.is(x, "app"), _ => sp.ssb.char(pos, k, sp.at(x, 2n), fs), _ => fs))))

# the facts of a guarded branch's guards, (body C) each
def sp.ssb.guards(gs: List<&2, X.Sx>, +fs: List<&2, Mf>) -> List<&2, Mf>:
  match gs:
    case Nil{}:
      fs
    case +g <> t:
      sp.ssb.guards(t, sp.if(List<&2, Mf>, sp.head.is(g, "body"), _ => sp.ssb.test(6n, sp.at(g, 1n), True{}, fs), _ => fs))

# and of the branches after it: its one guard does not hold
def sp.ssb.after(+g: X.Sx, +fs: List<&2, Mf>) -> List<&2, Mf>:
  +gs = sp.at(g, 1n)
  +c = sp.at(gs, 0n)
  sp.if(List<&2, Mf>, Bool.and(Nat.is_eq(X.tsx.len(gs), 1n), sp.head.is(c, "body")), _ => sp.ssb.test(6n, sp.at(c, 1n), False{}, fs), _ => fs)

# Clauses: the literals that an earlier clause took at an argument

type Ml is Data:
  Ml{i: Nat, k: Nat}
  MlLo{i: Nat, k: Nat}

# a pattern that takes everything, and the variable it binds
def sp.ssb.pany(n: Nat, +p: X.Sx) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+q:
      sp.if(Bool, Bool.or(sp.head.is(p, "pbang"), sp.head.is(p, "plazy")), _ => sp.ssb.pany(q, sp.at(p, 1n)), _ => Bool.or(sp.head.is(p, "pvar"), sp.head.is(p, "pwild")))

def sp.ssb.pvar(n: Nat, +p: X.Sx) -> X.Sx:
  match n:
    case 0n:
      X.SxNil{}
    case 1n+q:
      sp.if(X.Sx, sp.head.is(p, "pbang"), _ => sp.ssb.pvar(q, sp.at(p, 1n)), _ => sp.if(X.Sx, Bool.or(sp.head.is(p, "pvar"), sp.head.is(p, "pas")), _ => sp.at(sp.at(p, 1n), 1n), _ => X.SxNil{}))

# a literal pattern's number, (pnlit OLIT pos TYPE)
def sp.ssb.plit(+p: X.Sx) -> Maybe<&2, Nat>:
  sp.if(Maybe<&2, Nat>, Bool.and(sp.head.is(p, "pnlit"), sp.is(X.tsx.atom.of(sp.at(p, 2n)), "pos")), _ => sp.ssb.lit(sp.at(p, 1n)), _ => None{})

# whether a clause that its patterns took answers (a branch with no guard, or
# otherwise)
def sp.ssb.total(gs: List<&2, X.Sx>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case +g <> t:
      +q = sp.at(g, 1n)
      +o = sp.ssb.key(sp.at(sp.at(q, 0n), 1n))
      Bool.or(Bool.or(Nat.is_eq(X.tsx.len(q), 0n), Bool.and(Nat.is_eq(X.tsx.len(q), 1n), sp.is(o, "GHC.Internal.Base.otherwise"))), sp.ssb.total(t))

# all the patterns but the one at i take everything
def sp.ssb.rest.all(ps: List<&2, X.Sx>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(sp.ssb.pany(3n, p), sp.ssb.rest.all(t))

def sp.ssb.rest(ps: List<&2, X.Sx>, i: Nat) -> Bool:
  match ps i:
    case Nil{} _:
      True{}
    case p <> t 0n:
      sp.ssb.rest.all(t)
    case p <> t 1n+j:
      Bool.and(sp.ssb.pany(3n, p), sp.ssb.rest(t, j))

def sp.ssb.lit.add(m: Maybe<&2, Nat>, ok: Bool, i: Nat, st: List<&2, Ml>) -> List<&2, Ml>:
  match m ok:
    case Some{k} True{}:
      Ml{i, k} <> st
    case _ _:
      st

# the literals clause m takes: the one literal at i, the rest everything
def sp.ssb.lits(ps: List<&2, X.Sx>, +i: Nat, +all: List<&2, X.Sx>, +tot: Bool, st: List<&2, Ml>) -> List<&2, Ml>:
  match ps:
    case Nil{}:
      st
    case p <> t:
      sp.ssb.lit.add(sp.ssb.plit(p), Bool.and(tot, sp.ssb.rest(all, i)), i, sp.ssb.lits(t, 1n+i, all, tot, st))

# a clause whose patterns take everything but whose guards may all fail: what
# their failing says of the variable at i
def sp.ssb.afters(gs: List<&2, X.Sx>, +fs: List<&2, Mf>) -> List<&2, Mf>:
  match gs:
    case Nil{}:
      fs
    case +g <> t:
      sp.ssb.afters(t, sp.ssb.after(g, fs))

def sp.ssb.low(+i: Nat, +k: Nat, st: List<&2, Ml>) -> List<&2, Ml>:
  match k:
    case 0n:
      st
    case +j:
      MlLo{i, j} <> st

def sp.ssb.lows(ps: List<&2, X.Sx>, +i: Nat, +fs: List<&2, Mf>, st: List<&2, Ml>) -> List<&2, Ml>:
  match ps:
    case Nil{}:
      st
    case +p <> t:
      +v = sp.ssb.pvar(3n, p)
      sp.ssb.low(i, sp.ssb.bump(12n, fs, v, sp.ssb.los(fs, v, 0n)), sp.ssb.lows(t, 1n+i, fs, st))

def sp.ssb.clause(+m: X.Sx, st: List<&2, Ml>) -> List<&2, Ml>:
  +ps = sp.els(sp.at(m, 1n))
  +gs = sp.els(sp.at(sp.at(m, 2n), 1n))
  +st1 = {sp.ssb.lits(ps, 0n, ps, sp.ssb.total(gs), st) : List<&2, Ml>}
  sp.if(List<&2, Ml>, sp.ssb.rest.all(ps), _ => sp.ssb.lows(ps, 0n, sp.ssb.afters(gs, Nil{}), st1), _ => st1)

def sp.ssb.nth(xs: List<&2, X.Sx>, i: Nat) -> X.Sx:
  match xs i:
    case Nil{} _:
      X.SxNil{}
    case x <> t 0n:
      x
    case x <> t 1n+j:
      sp.ssb.nth(t, j)

# the facts of a clause: its variable at i is none of the literals taken at i
# before, nor is the case's scrutinee (scr)
def sp.ssb.not(+v: X.Sx, +k: Nat, +fs: List<&2, Mf>) -> List<&2, Mf>:
  sp.if(List<&2, Mf>, Bool.or(sp.head.is(v, "l"), sp.head.is(v, "app")), _ => MfNe{v, k} <> fs, _ => fs)

def sp.ssb.low.in(+v: X.Sx, +k: Nat, +fs: List<&2, Mf>) -> List<&2, Mf>:
  sp.if(List<&2, Mf>, Bool.or(sp.head.is(v, "l"), sp.head.is(v, "app")), _ => MfLo{v, k} <> fs, _ => fs)

def sp.ssb.enter(st: List<&2, Ml>, +ps: List<&2, X.Sx>, +scr: X.Sx, fs: List<&2, Mf>) -> List<&2, Mf>:
  match st:
    case Nil{}:
      fs
    case Ml{+i, +k} <> t:
      sp.ssb.not(scr, k, sp.ssb.not(sp.ssb.pvar(3n, sp.ssb.nth(ps, i)), k, sp.ssb.enter(t, ps, scr, fs)))
    case MlLo{+i, +k} <> t:
      sp.ssb.low.in(scr, k, sp.ssb.low.in(sp.ssb.pvar(3n, sp.ssb.nth(ps, i)), k, sp.ssb.enter(t, ps, scr, fs)))

# The walk

# what a tree about to be walked is (Mk): an if, guarded branches (a list),
# one, a clause's right side, a multi-way if, a case, clauses (scr: the
# case's scrutinee), a list of them after the literals st, a subtraction to
# write with op, max at a subtraction, abs at one, anything
type Mk is Data:
  MkE{}
  MkIf{}
  MkGs{}
  MkG{}
  MkGrhss{}
  MkMulti{}
  MkCase{}
  MkMs{scr: X.Sx}
  MkMl{st: List<&2, Ml>, scr: X.Sx}
  MkSub{op: X.Sx}
  MkMax{}
  MkAbs{}

def sp.ssb.hastv(fs: List<&2, Mf>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case MfTv{} <> t:
      True{}
    case _ <> t:
      sp.ssb.hastv(t)

# a subtraction at Int; at a type variable only where no copy of it is made
# after (MfTv: the survey's reading, where the default rule has it Integer): a
# copy may be at HsInt, where (a - b) + (b - a) is 0, or at Natural, where
# max 0 (a - b) is an error
def sp.ssb.sub1(+x: X.Sx, +fs: List<&2, Mf>) -> Bool:
  +y = sp.ssb.open(4n, x)
  +t = sp.ssb.subty(y)
  Bool.and(sp.ssb.issub(y), Bool.or(sp.ssb.int0(t), Bool.and(sp.ssb.int(t), sp.ssb.hastv(fs))))

# whether x is max's call with one
def sp.ssb.ismax(+x: X.Sx, +fs: List<&2, Mf>) -> Bool:
  Bool.and(sp.ssb.two(x), Bool.and(sp.is(sp.ssb.key(sp.ssb.f2(x)), "GHC.Classes.max"), Bool.or(sp.ssb.sub1(sp.ssb.a2(x), fs), sp.ssb.sub1(sp.ssb.b2(x), fs))))

def sp.ssb.loc(+x: X.Sx) -> Bool:
  +y = sp.ssb.open(4n, x)
  Bool.or(sp.head.is(y, "l"), sp.head.is(y, "olit"))

# abs (a - b), a and b locals or literals
def sp.ssb.isabs(+x: X.Sx, +fs: List<&2, Mf>) -> Bool:
  +y = sp.ssb.open(4n, sp.at(x, 2n))
  Bool.and(Bool.and(sp.head.is(x, "app"), sp.is(sp.ssb.key(sp.at(x, 1n)), "GHC.Internal.Num.abs")), Bool.and(sp.ssb.sub1(sp.at(x, 2n), fs), Bool.and(sp.ssb.loc(sp.ssb.a2(y)), sp.ssb.loc(sp.ssb.b2(y)))))

# the name of the function an application of one or two arguments calls
def sp.ssb.name(+x: X.Sx) -> List<&2, U32>:
  +f = sp.if(X.Sx, sp.ssb.two(x), _ => sp.ssb.f2(x), _ => sp.at(x, 1n))
  +g = sp.ssb.peel(4n, f)
  sp.if(List<&2, U32>, sp.head.is(g, "g"), _ => sp.sat(g, 2n), _ => Nil{})

def sp.ssb.kd.app(+x: X.Sx, +fs: List<&2, Mf>) -> Mk:
  +n = sp.ssb.name(x)
  sp.if(Mk, Bool.or(sp.is(n, "-"), sp.is(n, "natSub")), _ => sp.if(Mk, sp.if(Bool, sp.ssb.issub(x), _ => sp.ssb.ge(sp.ssb.a2(x), sp.ssb.b2(x), fs), _ => False{}), _ => MkSub{sp.ssb.safe.op(sp.ssb.subty(x))}, _ => MkE{}), _ =>
    sp.if(Mk, sp.is(n, "max"), _ => sp.if(Mk, sp.ssb.ismax(x, fs), _ => MkMax{}, _ => MkE{}), _ => sp.if(Mk, sp.is(n, "abs"), _ => sp.if(Mk, sp.ssb.isabs(x, fs), _ => MkAbs{}, _ => MkE{}), _ => MkE{})))

def sp.ssb.kd(+x: X.Sx, +fs: List<&2, Mf>) -> Mk:
  +a = sp.hd(x)
  sp.if(Mk, sp.is(a, "app"), _ => sp.ssb.kd.app(x, fs), _ =>
    sp.if(Mk, sp.is(a, "if"), _ => MkIf{}, _ =>
      sp.if(Mk, sp.is(a, "grhss"), _ => MkGrhss{}, _ =>
        sp.if(Mk, sp.is(a, "case"), _ => MkCase{}, _ =>
          sp.if(Mk, sp.is(a, "matches"), _ => MkMs{X.SxNil{}}, _ => sp.if(Mk, sp.is(a, "multiif"), _ => MkMulti{}, _ => MkE{}))))))

# with the fact a >= b of a subtraction a - b (max's argument)
def sp.ssb.asif(+x: X.Sx, +fs: List<&2, Mf>) -> List<&2, Mf>:
  +y = sp.ssb.open(4n, x)
  sp.if(List<&2, Mf>, sp.ssb.sub1(x, fs), _ => MfGe{sp.ssb.norm(sp.ssb.a2(y)), sp.ssb.norm(sp.ssb.b2(y))} <> fs, _ => fs)

# (app ABS (a - b)) as (a - b) + (b - a), each Nat's
def sp.ssb.rename(x: X.Sx, +a: List<&2, U32>, +b: List<&2, U32>) -> X.Sx:
  match x:
    case X.SxStr{+s}:
      Bool.pick(X.Sx, S.eq(s, a), X.SxStr{b}, X.SxStr{s})
    case X.SxCons{h, t}:
      X.SxCons{sp.ssb.rename(h, a, b), sp.ssb.rename(t, a, b)}
    case z:
      z

def sp.ssb.abs(+f: X.Sx, +x: X.Sx) -> X.Sx:
  +y = sp.ssb.open(4n, x)
  +op = sp.ssb.safe.op(sp.ssb.subty(y))
  +a = sp.ssb.a2(y)
  +b = sp.ssb.b2(y)
  +ab = sp.l([sp.a("app"), sp.l([sp.a("app"), op, a]), b])
  +ba = sp.l([sp.a("app"), sp.l([sp.a("app"), op, b]), a])
  sp.l([sp.a("app"), sp.l([sp.a("app"), sp.ssb.rename(f, S.b("abs"), S.b("+")), ab]), ba])

def sp.ssb(x: X.Sx, k: Mk, +fs: List<&2, Mf>) -> X.Sx:
  match x k:
    case X.SxCons{h, X.SxCons{+c, X.SxCons{+t, X.SxCons{+e, r}}}} MkIf{}:
      +f1 = sp.ssb.test(6n, c, True{}, fs)
      +f2 = sp.ssb.test(6n, c, False{}, fs)
      X.SxCons{h, X.SxCons{sp.ssb(c, sp.ssb.kd(c, fs), fs), X.SxCons{sp.ssb(t, sp.ssb.kd(t, f1), f1), X.SxCons{sp.ssb(e, sp.ssb.kd(e, f2), f2), r}}}}
    case X.SxCons{+g, rest} MkGs{}:
      X.SxCons{sp.ssb(g, MkG{}, fs), sp.ssb(rest, MkGs{}, sp.ssb.after(g, fs))}
    case X.SxCons{h, X.SxCons{+gs, X.SxCons{+e, r}}} MkG{}:
      +f1 = sp.ssb.guards(sp.els(gs), fs)
      X.SxCons{h, X.SxCons{sp.ssb(gs, MkE{}, fs), X.SxCons{sp.ssb(e, sp.ssb.kd(e, f1), f1), r}}}
    case X.SxCons{h, X.SxCons{gs, X.SxCons{lb, r}}} MkGrhss{}:
      X.SxCons{h, X.SxCons{sp.ssb(gs, MkGs{}, fs), X.SxCons{sp.ssb(lb, MkE{}, fs), r}}}
    case X.SxCons{h, X.SxCons{ty, X.SxCons{gs, r}}} MkMulti{}:
      X.SxCons{h, X.SxCons{ty, X.SxCons{sp.ssb(gs, MkGs{}, fs), r}}}
    case X.SxCons{h, X.SxCons{+e, X.SxCons{m, r}}} MkCase{}:
      X.SxCons{h, X.SxCons{sp.ssb(e, sp.ssb.kd(e, fs), fs), X.SxCons{sp.ssb(m, MkMs{sp.ssb.open(4n, e)}, fs), r}}}
    case X.SxCons{h, X.SxCons{as, X.SxCons{rt, X.SxCons{s, X.SxCons{ms, r}}}}} MkMs{scr}:
      X.SxCons{h, X.SxCons{as, X.SxCons{rt, X.SxCons{s, X.SxCons{sp.ssb(ms, MkMl{Nil{}, scr}, fs), r}}}}}
    case X.SxCons{+m, rest} MkMl{+st, +scr}:
      X.SxCons{sp.ssb(m, MkE{}, sp.ssb.enter(st, sp.els(sp.at(m, 1n)), scr, fs)), sp.ssb(rest, MkMl{sp.ssb.clause(m, st), scr}, fs)}
    case X.SxCons{h, X.SxCons{X.SxCons{h2, X.SxCons{f, X.SxCons{+a, r1}}}, X.SxCons{+b, r2}}} MkSub{op}:
      X.SxCons{h, X.SxCons{X.SxCons{h2, X.SxCons{op, X.SxCons{sp.ssb(a, sp.ssb.kd(a, fs), fs), r1}}}, X.SxCons{sp.ssb(b, sp.ssb.kd(b, fs), fs), r2}}}
    case X.SxCons{h, X.SxCons{X.SxCons{h2, X.SxCons{f, X.SxCons{+a, r1}}}, X.SxCons{+b, r2}}} MkMax{}:
      +fa = sp.ssb.asif(a, fs)
      +fb = sp.ssb.asif(b, fs)
      X.SxCons{h, X.SxCons{X.SxCons{h2, X.SxCons{f, X.SxCons{sp.ssb(a, sp.ssb.kd(a, fa), fa), r1}}}, X.SxCons{sp.ssb(b, sp.ssb.kd(b, fb), fb), r2}}}
    case X.SxCons{h, X.SxCons{+f, X.SxCons{+y, r}}} MkAbs{}:
      sp.ssb.abs(f, y)
    case X.SxCons{+h, t} MkE{}:
      X.SxCons{sp.ssb(h, sp.ssb.kd(h, fs), fs), sp.ssb(t, MkE{}, fs)}
    case z _:
      z

# A tuple section, (tuple (missing T) e), is the lambda over what is missing,
# \ts_0 -> (ts_0, e). Its answer's type is the parts': a local's, what is
# missing's, a nullary constructor's; a part of no known type has a type
# variable (a lambda's answer's type is asked for where it is lifted).
def sp.ts.ty(+e: X.Sx, +env: List<&2, Asb>) -> X.Sx:
  +y = sp.pc.strip(e)
  +h = sp.vhead(y)
  +m = sp.as.look(y, env)
  +un = Bool.and(sp.head.is(y, "g"), sp.is(sp.gkey(y), "GHC.Tuple.()"))
  +nl = Bool.and(sp.head.is(y, "tyapp"), sp.is(sp.gkey(h), "GHC.Types.[]"))
  +no = Bool.and(sp.head.is(y, "tyapp"), sp.is(sp.gkey(h), "GHC.Internal.Maybe.Nothing"))
  sp.if(X.Sx, sp.head.is(y, "missing"), _ => sp.at(y, 1n), _ => sp.if(X.Sx, Maybe.is_some(&2, X.Sx, m), _ => sp.or(m, y), _ => sp.if(X.Sx, un, _ => sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{}), _ => sp.if(X.Sx, nl, _ => sp.hf.list(sp.at(y, 2n)), _ => sp.if(X.Sx, no, _ => sp.tc(S.b("GHC.Internal.Maybe"), S.b("Maybe"), [sp.at(y, 2n)]), _ => sp.l([sp.a("tv"), X.SxStr{S.b("%ts")}]))))))

def sp.ts.tys(es: List<&2, X.Sx>, +env: List<&2, Asb>) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      sp.ts.ty(e, env) <> sp.ts.tys(t, env)

def sp.ts.v(+i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b("ts_"), S.b(Nat.show(i)))}, sp.a("0")])

def sp.ts.has(es: List<&2, X.Sx>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(sp.head.is(e, "missing"), sp.ts.has(t))

def sp.ts.pats(es: List<&2, X.Sx>, +i: Nat) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      +rest = sp.ts.pats(t, 1n+i)
      Bool.pick(List<&2, X.Sx>, sp.head.is(e, "missing"), sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.ts.v(i), sp.at(e, 1n)])]) <> rest, rest)

def sp.ts.els(es: List<&2, X.Sx>, +i: Nat) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Bool.pick(X.Sx, sp.head.is(e, "missing"), sp.ts.v(i), e) <> sp.ts.els(t, 1n+i)

def sp.ts.mis(es: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      +rest = sp.ts.mis(t)
      Bool.pick(List<&2, X.Sx>, sp.head.is(e, "missing"), sp.at(e, 1n) <> rest, rest)

# (tuple E..) with a (missing T)
def sp.ts.lam(+es: List<&2, X.Sx>, +env: List<&2, Asb>) -> X.Sx:
  +n = List.length(&2, X.Sx, es)
  +res = sp.tc(S.b("GHC.Tuple"), sp.cat(S.b("Tuple"), S.b(Nat.show(n))), sp.ts.tys(es, env))
  +m = sp.l([sp.a("match"), sp.l(sp.ts.pats(es, 0n)), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, X.SxCons{sp.a("tuple"), sp.l(sp.ts.els(es, 0n))}])]), sp.l([sp.a("binds")])])])
  sp.l([sp.a("lam"), sp.a("single"), sp.l([sp.a("matches"), sp.l(sp.ts.mis(es)), res, sp.a("source"), sp.l([m])])])

def sp.ts.go(x: X.Sx, +env: List<&2, Asb>) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, t}:
      +t2 = sp.ts.go(t, env)
      sp.if(X.Sx, sp.is(a, "tuple"), _ => sp.if(X.Sx, sp.ts.has(sp.els(t2)), _ => sp.ts.lam(sp.els(t2), env), _ => X.SxCons{X.SxAtom{a}, t2}), _ => X.SxCons{X.SxAtom{a}, t2})
    case X.SxCons{h, t}:
      X.SxCons{sp.ts.go(h, env), sp.ts.go(t, env)}
    case y:
      y

def sp.ts.any(x: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, t}:
      Bool.or(sp.is(X.tsx.atom.of(h), "missing"), Bool.or(sp.ts.any(h), sp.ts.any(t)))
    case y:
      False{}

def sp.ts(+x: X.Sx) -> X.Sx:
  sp.if(X.Sx, sp.ts.any(x), _ => sp.ts.go(x, sp.fa.binds(x, Nil{})), _ => x)

# an item, read where no copy of it is made after (alone), or before the copies
def sp.ssb.start(alone: Bool) -> List<&2, Mf>:
  match alone:
    case True{}:
      [MfTv{}]
    case False{}:
      Nil{}

def sp.ssb.item(alone: Bool, x: X.Sx) -> X.Sx:
  sp.ssb(x, MkE{}, sp.ssb.start(alone))

def sp.p5s.go(xs: List<&2, X.Sx>, +cts: List<&2, Ct>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.ssb.item(False{}, sp.pb(sp.p5(sp.p6(sp.lm(sp.ts(x))), True{}), cts)) <> sp.p5s.go(t, cts)

# (cts: the constructors of the package's modules before it)
def sp.p5s(+xs: List<&2, X.Sx>, +cts: List<&2, Ct>) -> List<&2, X.Sx>:
  sp.p5s.go(xs, List.append(&2, Ct, sp.cts.own(xs, sp.modname(xs)), cts))

# Eq1 derived via Generically1 (`deriving Eq1 via (Generically1 T)`): GHC
# writes liftEq as a coercion of the generic one, which is the equality of
# T's structure: t at a field of T's last type variable, liftEq at a field
# of a functor at it, == at any other. Written so, from T's declaration.
def sp.g1.has(x: X.Sx, +v: X.Sx) -> Bool:
  match x:
    case X.SxCons{+h, +t}:
      Bool.or(sp.eq(X.SxCons{h, t}, v), Bool.or(sp.g1.has(h, v), sp.g1.has(t, v)))
    case y:
      False{}

def sp.g1.atom(x: X.Sx, +s: List<&2, U32>) -> Bool:
  match x:
    case X.SxCons{h, t}:
      Bool.or(sp.g1.atom(h, s), sp.g1.atom(t, s))
    case X.SxStr{+a}:
      S.eq(a, s)
    case _:
      False{}

def sp.g1.v(+s: String, +i: Nat) -> X.Sx:
  sp.l([sp.a("l"), X.SxStr{sp.cat(S.b(s), S.b(Nat.show(i)))}, sp.a("0")])

def sp.g1.app(+f: X.Sx, +x: X.Sx) -> X.Sx:
  sp.l([sp.a("app"), f, x])

def sp.g1.init(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> Nil{}:
      Nil{}
    case x <> t:
      x <> sp.g1.init(t)

def sp.g1.last(xs: List<&2, X.Sx>) -> X.Sx:
  match xs:
    case Nil{}:
      X.SxNil{}
    case x <> Nil{}:
      x
    case x <> t:
      sp.g1.last(t)

# a field's comparison (ty: its type in the declaration, f: the last type
# variable, sa: the variables' types, ta and tb the two element types)
def sp.g1.field(+ty: X.Sx, +f: X.Sx, +sa: List<&2, Sb>, +ta: X.Sx, +tb: X.Sx, +x: X.Sx, +y: X.Sx) -> X.Sx:
  +t = sp.g1.v("g1t", 0n)
  +as = sp.els(ty)
  +fun = Bool.and(sp.head.is(ty, "tc"), Bool.and(sp.eq(sp.g1.last(as), f), Bool.not(sp.g1.has(sp.l(sp.g1.init(as)), f))))
  +le = sp.l([sp.a("tyapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("g"), X.SxStr{S.b("Data.Functor.Classes")}, X.SxStr{S.b("liftEq")}, sp.l([sp.a("method"), X.SxStr{S.b("Data.Functor.Classes")}, X.SxStr{S.b("Eq1")}])]), sp.subst(sp.l(sp.g1.init(as)), sa)]), sp.l([sp.a("l"), X.SxStr{S.b("$dEq1")}, sp.a("0")])]), ta]), tb])
  +eq = sp.l([sp.a("evapp"), sp.l([sp.a("tyapp"), sp.l([sp.a("g"), X.SxStr{S.b("GHC.Classes")}, X.SxStr{S.b("==")}, sp.l([sp.a("method"), X.SxStr{S.b("GHC.Classes")}, X.SxStr{S.b("Eq")}])]), sp.subst(ty, sa)]), sp.l([sp.a("l"), X.SxStr{S.b("$dEq")}, sp.a("0")])])
  +h = sp.if(X.Sx, sp.eq(ty, f), _ => t, _ => sp.if(X.Sx, Bool.not(sp.g1.has(ty, f)), _ => eq, _ => sp.if(X.Sx, fun, _ => sp.g1.app(le, t), _ => sp.g(S.b("HsPrelude.Z"), S.b("g1out"), "var"))))
  sp.g1.app(sp.g1.app(h, x), y)

def sp.g1.and(+a: X.Sx, b: Maybe<&2, X.Sx>) -> X.Sx:
  match b:
    case Some{y}:
      sp.g1.app(sp.g1.app(sp.g(S.b("GHC.Classes"), S.b("&&"), "var"), a), y)
    case None{}:
      a

def sp.g1.fields(tys: List<&2, X.Sx>, +i: Nat, +f: X.Sx, +sa: List<&2, Sb>, +ta: X.Sx, +tb: X.Sx) -> Maybe<&2, X.Sx>:
  match tys:
    case Nil{}:
      None{}
    case ty <> t:
      Some{sp.g1.and(sp.g1.field(ty, f, sa, ta, tb, sp.g1.v("g1x", i), sp.g1.v("g1y", i)), sp.g1.fields(t, 1n+i, f, sa, ta, tb))}

def sp.g1.vars(tys: List<&2, X.Sx>, +s: String, +i: Nat, +sb: List<&2, Sb>) -> List<&2, X.Sx>:
  match tys:
    case Nil{}:
      Nil{}
    case ty <> t:
      sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.g1.v(s, i), sp.subst(ty, sb)])]) <> sp.g1.vars(t, s, 1n+i, sb)

def sp.g1.match(+ps: List<&2, X.Sx>, +b: X.Sx) -> X.Sx:
  sp.l([sp.a("match"), sp.l(ps), sp.l([sp.a("grhss"), sp.l([sp.l([sp.a("grhs"), X.SxNil{}, b])]), sp.l([sp.a("binds")])])])

# a constructor's clause
def sp.g1.clauses(cs: List<&2, X.Sx>, +m: List<&2, U32>, +ft: X.Sx, +tya: X.Sx, +tyb: X.Sx, +f: X.Sx, +sa: List<&2, Sb>, +sb: List<&2, Sb>) -> List<&2, X.Sx>:
  match cs:
    case Nil{}:
      [sp.g1.match([sp.l([sp.a("pwild"), ft]), sp.l([sp.a("pwild"), tya]), sp.l([sp.a("pwild"), tyb])], sp.hf.bool("False"))]
    case +c <> t:
      +k = sp.g(m, sp.sat(c, 1n), "con")
      +tys = sp.els(sp.at(c, 3n))
      +pa = {sp.l([sp.a("pcon"), k, sp.l(sp.dropn(sp.els(tya), 3n)), X.SxCons{sp.a("args"), sp.l(sp.g1.vars(tys, "g1x", 0n, sa))}]) : X.Sx}
      +pb = {sp.l([sp.a("pcon"), k, sp.l(sp.dropn(sp.els(tyb), 3n)), X.SxCons{sp.a("args"), sp.l(sp.g1.vars(tys, "g1y", 0n, sb))}]) : X.Sx}
      +b = {sp.or(sp.g1.fields(tys, 0n, f, sa, sp.g1.last(sp.els(tya)), sp.g1.last(sp.els(tyb))), sp.hf.bool("True")) : X.Sx}
      sp.g1.match([sp.l([sp.a("pvar"), sp.l([sp.a("bv"), sp.g1.v("g1t", 0n), ft])]), pa, pb], b) <> sp.g1.clauses(t, m, ft, tya, tyb, f, sa, sb)

# the declaration of the type named n among the items
def sp.g1.data(xs: List<&2, X.Sx>, +n: List<&2, U32>) -> X.Sx:
  match xs:
    case Nil{}:
      X.SxNil{}
    case +x <> t:
      Bool.pick(X.Sx, Bool.and(Bool.or(sp.head.is(x, "data"), sp.head.is(x, "newtype")), S.eq(sp.sat(x, 1n), n)), x, sp.g1.data(t, n))

# the matches of the fun in x as ms
def sp.g1.put(x: X.Sx, +ms: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      +isf = sp.is(a, "fun")
      sp.if(X.Sx, isf, _ => X.SxCons{X.SxAtom{a}, X.SxCons{sp.at(t, 0n), X.SxCons{sp.at(t, 1n), X.SxCons{sp.at(t, 2n), X.SxCons{ms, X.SxCons{sp.a("hole"), X.SxNil{}}}}}}}, _ => X.SxCons{X.SxAtom{a}, sp.g1.put(t, ms)})
    case X.SxCons{h, t}:
      X.SxCons{sp.g1.put(h, ms), sp.g1.put(t, ms)}
    case y:
      y

def sp.g1.top(+x: X.Sx, +xs: List<&2, X.Sx>, +m: List<&2, U32>) -> X.Sx:
  +ty = sp.strip(sp.at(sp.or(sp.nth(sp.exports(x), 0n), X.SxNil{}), 2n))
  +ft = sp.at(ty, 1n)
  +r1 = sp.at(ty, 2n)
  +tya = sp.at(r1, 1n)
  +tyb = sp.at(sp.at(r1, 2n), 1n)
  +d = sp.g1.data(xs, sp.sat(tya, 2n))
  +tvs = sp.strs(sp.at(d, 2n))
  +f = sp.l([sp.a("tv"), X.SxStr{Maybe.default(&2, List<&2, U32>, List.last(&2, List<&2, U32>, tvs), Nil{})}])
  +sa = sp.zip(tvs, sp.dropn(sp.els(tya), 3n))
  +sb = sp.zip(tvs, sp.dropn(sp.els(tyb), 3n))
  +cls = sp.g1.clauses(sp.els(sp.at(d, 3n)), m, ft, tya, tyb, f, sa, sb)
  +ms = {sp.l([sp.a("matches"), sp.l([ft, tya, tyb]), sp.tc(S.b("GHC.Types"), S.b("Bool"), Nil{}), sp.a("source"), sp.l(cls)]) : X.Sx}
  sp.if(X.Sx, sp.eq(d, X.SxNil{}), _ => x, _ => sp.g1.put(x, ms))

def sp.g1.is(+x: X.Sx) -> Bool:
  +v = sp.at(sp.or(sp.nth(sp.exports(x), 0n), X.SxNil{}), 1n)
  sp.if(Bool, Bool.and(sp.head.is(x, "top"), Bool.and(sp.head.is(v, "l"), sp.is(sp.sat(v, 1n), "$cliftEq"))), _ => sp.g1.atom(x, S.b("Generically1")), _ => False{})

def sp.g1.go(ys: List<&2, X.Sx>, +xs: List<&2, X.Sx>, +m: List<&2, U32>) -> List<&2, X.Sx>:
  match ys:
    case Nil{}:
      Nil{}
    case +x <> t:
      sp.if(X.Sx, sp.g1.is(x), _ => sp.g1.top(x, xs, m), _ => x) <> sp.g1.go(t, xs, m)

def sp.g1(+xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  sp.g1.go(xs, xs, sp.modname(xs))

# The program ------------------------------------------------------------------------

def sp.text(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.cat(X.tsx.show(x), 10 <> sp.text(t))

def sp.run(fs: List<String>, +out: String, +ix: Ix, list: List<&2, U32>, ws: List<&2, Wc>) -> IO(Unit):
  match fs:
    case Nil{}:
      S.write(out ++ "/modules.txt", list)
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +xs : List<&2, X.Sx> <- IO.pure(List<&2, X.Sx>, sp.p5s(sp.g1(X.tsx.read(bytes)), sp.ix.cts(ix)))
        +ix2 : Ix <- IO.pure(Ix, sp.ix.module(xs, ix))
        +p : String <- IO.pure(String, out ++ "/" ++ S.base(f))
        +md : Md <- IO.pure(Md, sp.module(xs, ix2, ws))
        S.write(p, sp.text(sp.md.xs(md)))
        sp.run(t, out, ix2, sp.cat(list, sp.cat(S.b(p), [10])), sp.md.wc(md))

def sp.main(args: List<String>) -> IO(Unit):
  match args:
    case out <> files:
      sp.run(files, out, sp.ix0(), Nil{}, Nil{})
    case Nil{}:
      IO.print("usage: spec OUTDIR FILE.sexp...")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    sp.main(List.tail(&1, String, argv))

