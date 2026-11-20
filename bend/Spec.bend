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
#     at those types (NAME__TYPES), written into the module that calls it;
#     a method of a class at such types, whose instance the package wrote
#     by hand, by a copy of that instance's method.
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

def sp.is(+x: List<&2, U32>, s: String) -> Bool:
  S.eq(x, S.b(s))

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

def sp.match(p: X.Sx, +t: X.Sx, +acc: Maybe<&2, List<&2, Sb>>) -> Maybe<&2, List<&2, Sb>>:
  match p:
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

type Ix is Data:
  Ix{dfs: List<&2, Df>, lcs: List<&2, Lc>, pss: List<&2, Ps>, ins: List<&2, In>, cls: List<&2, Cl>, sys: List<&2, Sy>, fms: List<&2, Fm>, fns: List<&2, Df>}

def sp.ix.sys(ix: Ix) -> List<&2, Sy>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      sys

def sp.ix0() -> Ix:
  Ix{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}

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

def sp.ix.df.add(+e: X.Sx, +top: X.Sx, +ds: List<&2, Df>) -> List<&2, Df>:
  Bool.pick(List<&2, Df>, Bool.and(sp.head.is(sp.at(e, 1n), "g"), sp.has(sp.at(e, 2n), S.b("tctx"))), Df{sp.key(sp.sat(sp.at(e, 1n), 1n), sp.sat(sp.at(e, 1n), 2n)), top} <> ds, ds)

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
      Bool.pick(Bool, strip, sp.fnp.has(r, sys), Bool.and(fun, Bool.or(sp.fnp.isfn(p, sys), sp.fnp.has(r, sys))))
    case _:
      False{}

# a global def that takes a function: its key and its top (known function
# arguments)
def sp.ix.fn.add(+e: X.Sx, +top: X.Sx, +fs: List<&2, Df>, +sys: List<&2, Sy>) -> List<&2, Df>:
  Bool.pick(List<&2, Df>, Bool.and(sp.head.is(sp.at(e, 1n), "g"), sp.fnp.has(sp.at(e, 2n), sys)), Df{sp.key(sp.sat(sp.at(e, 1n), 1n), sp.sat(sp.at(e, 1n), 2n)), top} <> fs, fs)

def sp.ix.exps(+m: List<&2, U32>, es: List<&2, X.Sx>, +top: X.Sx, ix: Ix) -> Ix:
  match es ix:
    case Nil{} i:
      i
    case +e <> r Ix{dfs, lcs, pss, ins, cls, +sys, fms, fns}:
      sp.ix.exps(m, r, top, Ix{sp.ix.df.add(e, top, dfs), sp.ix.lc.add(m, e, top, lcs), pss, ins, cls, sys, fms, sp.ix.fn.add(e, top, fns, sys)})

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
    case False{} True{} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      Ix{dfs, lcs, List.append(&2, Ps, sp.ps.of(b), pss), ins, cls, sys, fms, fns}
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

# recursion-schemes' Base at Fix and Cofree, base's String
def sp.builtin(+m: List<&2, U32>, +n: List<&2, U32>, +args: List<&2, X.Sx>, d: X.Sx) -> X.Sx:
  +k = sp.key(m, n)
  +a0 = Maybe.default(&2, X.Sx, List.head(&2, X.Sx, args), X.SxNil{})
  +fixf = Bool.and(sp.head.is(a0, "tc"), sp.is(sp.key(sp.sat(a0, 1n), sp.sat(a0, 2n)), "Data.Fix.Fix"))
  +cof = Bool.and(sp.head.is(a0, "tc"), sp.is(sp.key(sp.sat(a0, 1n), sp.sat(a0, 2n)), "Control.Comonad.Cofree.Cofree"))
  Bool.pick(X.Sx, Bool.and(sp.is(k, "Data.Functor.Foldable.Base"), fixf), sp.at(a0, 3n), Bool.pick(X.Sx, Bool.and(sp.is(k, "Data.Functor.Foldable.Base"), cof), sp.tc(S.b("Control.Comonad.Trans.Cofree"), S.b("CofreeF"), [sp.at(a0, 3n), sp.at(a0, 4n)]), Bool.pick(X.Sx, Bool.or(sp.is(k, "GHC.Internal.Base.String"), sp.is(k, "GHC.Internal.IO.FilePath")), sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Types"), S.b("Char"), Nil{})]), sp.builtin.pc(k, args, d))))

# one node, its parts already normal
def sp.norm.tc(+m: List<&2, U32>, +n: List<&2, U32>, +args: List<&2, X.Sx>, +ix: Ix) -> X.Sx:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
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
  Bool.pick(List<&2, Fm>, S.prefix(k, S.b("GHC.Internal.Generics.")), fms, Fm{k, sp.norms(sp.els(sp.at(x, 3n)), Ix{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, sys, Nil{}, Nil{}}), sp.at(x, 4n)} <> fms)

# an instance's class, from its line's (cls (TV...) (METHOD...) NSUPER)
def sp.cl.add(+x: X.Sx, +cls: List<&2, Cl>) -> List<&2, Cl>:
  +c = sp.at(x, 6n)
  Bool.pick(List<&2, Cl>, sp.head.is(c, "cls"), Cl{sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), X.tsx.len(sp.at(c, 1n)), X.tsx.nat(sp.at(c, 3n)), sp.strs(sp.at(c, 2n))} <> cls, cls)

def sp.ix.item.go(top: Bool, ins: Bool, cl: Bool, sy: Bool, fm: Bool, +m: List<&2, U32>, +ds: List<&2, Dn>, +x: X.Sx, ix: Ix) -> Ix:
  match top ins cl sy fm ix:
    case True{} _ _ _ _ i:
      sp.ix.top(m, x, i)
    case False{} True{} _ _ _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns}:
      Ix{dfs, lcs, pss, List.append(&2, In, sp.ix.in.mk(x, m, sp.dn.find(ds, sp.key(sp.sat(sp.at(x, 4n), 1n), sp.sat(sp.at(x, 4n), 2n)))), iss), sp.cl.add(x, cls), sys, fms, fns}
    case False{} False{} True{} _ _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns}:
      Ix{dfs, lcs, pss, iss, Cl{sp.key(m, sp.sat(x, 1n)), X.tsx.len(sp.at(x, 2n)), X.tsx.len(sp.at(x, 4n)), sp.ms(sp.at(x, 3n))} <> cls, sys, fms, fns}
    case False{} False{} False{} True{} _ Ix{dfs, lcs, pss, iss, cls, sys, fms, fns}:
      Ix{dfs, lcs, pss, iss, cls, Sy{sp.key(m, sp.sat(x, 1n)), sp.strs(sp.at(x, 2n)), sp.at(x, 3n)} <> sys, fms, fns}
    case False{} False{} False{} False{} True{} Ix{dfs, lcs, pss, iss, cls, +sys, fms, fns}:
      Ix{dfs, lcs, pss, iss, cls, sys, sp.fm.add(sp.key(sp.sat(x, 1n), sp.sat(x, 2n)), x, fms, sys), fns}
    case _ _ _ _ _ i:
      i

def sp.ix.item(+m: List<&2, U32>, +ds: List<&2, Dn>, +x: X.Sx, ix: Ix) -> Ix:
  +h = sp.hd(x)
  sp.ix.item.go(sp.is(h, "top"), sp.is(h, "instance"), sp.is(h, "class"), sp.is(h, "synonym"), sp.is(h, "faminst"), m, ds, x, ix)

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
  Mi{impl: X.Sx, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, first: X.Sx}

def sp.mi.term(t: Maybe<&2, X.Sx>, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, first: X.Sx) -> Maybe<&2, Mi>:
  match t:
    case Some{x}:
      Some{Mi{x, m, sbs, ntv, first}}
    case None{}:
      None{}

def sp.mi.at(p: Maybe<&2, Nat>, +args: List<&2, X.Sx>, m: List<&2, U32>, sbs: List<&2, Sb>, ntv: Nat, nsup: Nat) -> Maybe<&2, Mi>:
  match p:
    case Some{k}:
      sp.mi.term(sp.nth(args, k), m, sbs, ntv, Maybe.default(&2, X.Sx, sp.nth(args, nsup), X.SxNil{}))
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
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      +c = sp.method.cls(h)
      +cl = sp.cl.find(cls, c)
      +ntv = Maybe.default(&2, Nat, Maybe.map(&2, Cl, Nat, x => sp.cl.ntv(x), cl), 0n)
      sp.mi.of(sp.resolve(ins, sp.in.hit(ins, c), c, sp.take(ts, ntv), Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}), cl, sp.sat(h, 2n))

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
def sp.p1.pat.at(m: Maybe<&2, Ps>, +x: X.Sx) -> X.Sx:
  match m:
    case Some{Ps{pm, pn, tvs, bs, pat}}:
      +args = sp.at(x, 3n)
      Bool.pick(X.Sx, sp.head.is(args, "args"), sp.pbind(sp.subst(pat, sp.zip(tvs, sp.els(sp.at(x, 2n)))), bs, sp.els(X.tsx.args(args))), x)
    case None{}:
      x

def sp.p1.pat(+x: X.Sx, +ix: Ix) -> X.Sx:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
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
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      sp.p1.expr.at(sp.ps.find(pss, sp.sat(x, 2n)), x)

# one pass: each use replaced by what it stands for (its parts in the next)
# what a node is to the pattern synonyms' pass
type P1k is Data:
  P1Pat{}
  P1Exp{}
  P1Gen{}

def sp.p1k(+x: X.Sx) -> P1k:
  Bool.pick(P1k, Bool.and(sp.head.is(x, "pcon"), sp.unsup(sp.at(x, 1n))), P1Pat{}, Bool.pick(P1k, sp.unsup(x), P1Exp{}, P1Gen{}))

def sp.p1(x: X.Sx, k: P1k, +ix: Ix) -> X.Sx:
  match x k:
    case y P1Pat{}:
      sp.p1.pat(y, ix)
    case y P1Exp{}:
      sp.p1.expr(y, ix)
    case X.SxCons{+h, +t} P1Gen{}:
      X.SxCons{sp.p1(h, sp.p1k(h), ix), sp.p1(t, sp.p1k(t), ix)}
    case y P1Gen{}:
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

# passes until no pattern synonym is left, at most n (one the index has
# not stays)
def sp.p1.go(n: Nat, +x: X.Sx, more: Bool, +ix: Ix) -> X.Sx:
  match n more:
    case Succ{k} True{}:
      +y = sp.p1(x, sp.p1k(x), ix)
      sp.p1.go(k, y, sp.has.str(y, S.b("PatSynCon")), ix)
    case _ _:
      x

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

def sp.sel.go(ms: List<&2, X.Sx>, acc: Sel) -> Sel:
  match ms acc:
    case +m <> t Sel{+hit, +n, +ok}:
      +ps = sp.els(sp.at(m, 1n))
      +body = sp.at(sp.at(sp.at(sp.at(m, 2n), 1n), 0n), 2n)
      +just = Bool.and(sp.head.is(body, "app"), Bool.and(sp.con.is(sp.at(body, 1n), "GHC.Internal.Maybe.Just"), sp.head.is(sp.at(body, 2n), "l")))
      +noth = Bool.and(Bool.not(sp.head.is(body, "app")), sp.con.is(body, "GHC.Internal.Maybe.Nothing"))
      +one = Nat.is_eq(List.length(&2, X.Sx, ps), 1n)
      sp.sel.go(t, Sel{Bool.pick(Maybe<&2, X.Sx>, just, Some{sp.l([sp.first(ps), sp.at(body, 2n)])}, hit), Bool.pick(Nat, just, Succ{n}, n), Bool.and(ok, Bool.and(one, Bool.or(just, noth)))})
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
    case Some{Mi{impl, m, sbs, ntv, first}} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
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
  +meth = Bool.and(Bool.not(app), Bool.and(Bool.not(S.eq(sp.method.cls(h), Nil{})), sp.all.closed(tys)))
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

def sp.p0.ms(+ms: X.Sx) -> X.Sx:
  +m0 = sp.first(sp.els(sp.at(ms, 4n)))
  +gs = sp.at(sp.at(m0, 2n), 1n)
  +g0 = sp.first(sp.els(gs))
  +body = sp.at(g0, 2n)
  +lm = sp.at(body, 2n)
  +bare = Bool.and(Nat.is_eq(X.tsx.len(sp.at(ms, 4n)), 1n), Bool.and(Nat.is_eq(X.tsx.len(gs), 1n), Bool.and(Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(sp.at(m0, 2n), 2n), sp.l([sp.a("binds")]))), Bool.and(sp.head.is(body, "lam"), Bool.not(sp.is(X.tsx.atom.of(sp.at(body, 1n)), "cases"))))))
  Bool.pick(X.Sx, bare, sp.l([sp.a("matches"), sp.l(List.append(&2, X.Sx, sp.els(sp.at(ms, 1n)), sp.els(sp.at(lm, 1n)))), sp.at(lm, 2n), sp.at(ms, 3n), sp.l(sp.p0.cl(sp.els(sp.at(lm, 4n)), sp.els(sp.at(m0, 1n))))]), ms)

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

# a node (a f e), its parts f2 and e2 rewritten
def sp.pc.three(+a: List<&2, U32>, +f: X.Sx, +e: X.Sx, +f2: X.Sx, +e2: X.Sx) -> X.Sx:
  +x = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}} : X.Sx}
  +chain = Bool.or(sp.is(a, "tyapp"), sp.is(a, "evapp"))
  +p = sp.pc.peel(x, Nil{}, Nil{})
  +m = sp.pc.find(sp.pc.tab(), sp.pc.key(p))
  +x2 = {X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}} : X.Sx}
  sp.if(X.Sx, Bool.and(chain, Maybe.is_some(&2, Pcr, m)), _ => sp.pc.model(m, sp.pc.tys(p), x), _ => sp.if(X.Sx, sp.is(a, "app"), _ => sp.pc.app(f2, e2), _ => x2))

def sp.pc(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      sp.pc.three(a, f, e, sp.pc(f), sp.pc(e))
    case X.SxCons{h, t}:
      X.SxCons{sp.pc(h), sp.pc(t)}
    case y:
      y

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
# type variables: its local V, else none
def sp.pl.cand(+g: X.Sx) -> Maybe<&2, X.Sx>:
  +ab = sp.at(g, 1n)
  +xps = sp.els(sp.at(ab, 3n))
  +one = Nat.is_eq(List.length(&2, X.Sx, xps), 1n)
  +ex = sp.first(xps)
  +ok = Bool.and(Bool.and(sp.head.is(g, "nonrec"), sp.head.is(ab, "abs")), Bool.and(Bool.not(sp.eq(sp.at(ab, 1n), X.SxNil{})), Bool.and(one, sp.head.is(sp.at(ex, 1n), "l"))))
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

def sp.pl.step(m: Maybe<&2, X.Sx>, +g: X.Sx, +body: X.Sx, +pre: List<&2, X.Sx>, +post: List<&2, X.Sx>, +ix: Ix) -> Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>:
  match m:
    case Some{+v}:
      +us = sp.pl.uses.all(body <> List.append(&2, X.Sx, pre, post), v, Nil{})
      +u0 = sp.pl.first(us)
      +ok = Bool.and(Bool.not(List.is_empty(&2, List<&2, X.Sx>, us)), Bool.and(sp.pl.same(us, u0), Bool.and(Bool.not(sp.eq(u0, X.SxNil{})), sp.closed(u0))))
      sp.if(Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>, ok, _ => (Pls{sp.pl.strip(body, v), sp.pl.at(g, sp.els(u0), ix) <> sp.pl.strips(pre, v)}, sp.pl.strips(post, v)), _ => (Pls{body, g <> pre}, post))
    case None{}:
      (Pls{body, g <> pre}, post)

def sp.pl.fst(st: Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>) -> Pls:
  (s, r) = st
  s

def sp.pl.go(n: Nat, st: Sigma<&2, &2, Pls, _ => List<&2, X.Sx>>, +ix: Ix) -> Pls:
  match n:
    case 1n+k:
      match st:
        case (Pls{+body, +pre}, +g <> t):
          sp.pl.go(k, sp.pl.step(sp.pl.cand(g), g, body, pre, t, ix), ix)
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

def sp.pl.scope(+body: X.Sx, +binds: X.Sx, +ix: Ix) -> Pls:
  +gs = sp.pl.tail(binds)
  sp.pl.go(List.length(&2, X.Sx, gs), (Pls{body, Nil{}}, gs), ix)

def sp.pl.grhss(s: Pls) -> X.Sx:
  match s:
    case Pls{b, pre}:
      sp.l([sp.a("grhss"), b, X.SxCons{sp.a("binds"), sp.l(List.reverse(&2, X.Sx, pre))}])

def sp.pl.let(s: Pls) -> X.Sx:
  match s:
    case Pls{b, pre}:
      sp.l([sp.a("let"), X.SxCons{sp.a("binds"), sp.l(List.reverse(&2, X.Sx, pre))}, b])

# (grhss GRHSS (binds G..)) and (let (binds G..) E), their scopes done
def sp.pl.node(+a: List<&2, U32>, +x: X.Sx, +ix: Ix) -> X.Sx:
  +gr = Bool.and(sp.is(a, "grhss"), sp.head.is(sp.at(x, 2n), "binds"))
  +lt = Bool.and(sp.is(a, "let"), sp.head.is(sp.at(x, 1n), "binds"))
  sp.if(X.Sx, gr, _ => sp.pl.grhss(sp.pl.scope(sp.at(x, 1n), sp.at(x, 2n), ix)), _ => sp.if(X.Sx, lt, _ => sp.pl.let(sp.pl.scope(sp.at(x, 2n), sp.at(x, 1n), ix)), _ => x))

# bottom up: a scope's parts first
def sp.pl(x: X.Sx, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, +t}:
      sp.pl.node(a, X.SxCons{X.SxAtom{a}, sp.pl(t, ix)}, ix)
    case X.SxCons{h, t}:
      X.SxCons{sp.pl(h, ix), sp.pl(t, ix)}
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

# a lambda's variable and body, if it is one such
def sp.beta.lam(+f: X.Sx) -> Maybe<&2, Sigma<&2, &2, X.Sx, _ => X.Sx>>:
  +ms = sp.at(f, 2n)
  +cls = sp.els(sp.at(ms, 4n))
  +m0 = sp.first(cls)
  +ps = sp.els(sp.at(m0, 1n))
  +p0 = sp.first(ps)
  +gr = sp.at(m0, 2n)
  +gs = sp.els(sp.at(gr, 1n))
  +g0 = sp.first(gs)
  +ok = Bool.and(Bool.and(sp.head.is(f, "lam"), sp.is(X.tsx.atom.of(sp.at(f, 1n)), "single")), Bool.and(Bool.and(Nat.is_eq(List.length(&2, X.Sx, cls), 1n), Nat.is_eq(List.length(&2, X.Sx, ps), 1n)), Bool.and(Bool.and(sp.head.is(p0, "pvar"), Nat.is_eq(List.length(&2, X.Sx, gs), 1n)), Bool.and(sp.eq(sp.at(g0, 1n), X.SxNil{}), sp.eq(sp.at(gr, 2n), sp.l([sp.a("binds")]))))))
  Bool.pick(Maybe<&2, Sigma<&2, &2, X.Sx, _ => X.Sx>>, ok, Some{(sp.at(sp.at(p0, 1n), 1n), sp.at(g0, 2n))}, None{})

def sp.beta.at(m: Maybe<&2, Sigma<&2, &2, X.Sx, _ => X.Sx>>, +a: X.Sx, +x: X.Sx) -> X.Sx:
  match m:
    case Some{(+v, +e)}:
      sp.beta.sub(e, v, a)
    case None{}:
      x

# bottom up: (app F A), its parts done
def sp.beta(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}}:
      +f2 = sp.beta(f)
      +e2 = sp.beta(e)
      +y = {X.SxCons{X.SxAtom{a}, X.SxCons{f2, X.SxCons{e2, X.SxNil{}}}} : X.Sx}
      sp.if(X.Sx, sp.is(a, "app"), _ => sp.beta.at(sp.beta.lam(sp.pc.strip(f2)), e2, y), _ => y)
    case X.SxCons{h, t}:
      X.SxCons{sp.beta(h), sp.beta(t)}
    case y:
      y

# Copies -------------------------------------------------------------------------------

# where a copy's binding is: a global def (M.N) or a module's top local
type Lo is Data:
  LoG{k: List<&2, U32>}
  LoL{m: List<&2, U32>, i: List<&2, U32>}
  LoF{k: List<&2, U32>, fas: List<&2, Fa>, fvt: List<&2, X.Sx>}

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
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      +k = sp.gkey(h)
      +nt = sp.df.tvs(sp.df.find(dfs, k))
      Bool.pick(Maybe<&2, Rw>, Bool.and(Maybe.is_some(&2, Nat, nt), Nat.is_eq(Maybe.default(&2, Nat, nt, 0n), List.length(&2, X.Sx, tys))), sp.ask(cur, sp.name(sp.sat(h, 2n), tys), LoG{k}, tys), None{})

# a method at an instance the package wrote by hand: a copy of the
# instance's method (a default method: a copy of it)
def sp.ask.impl(+impl: X.Sx, +m: List<&2, U32>, +sbs: List<&2, Sb>, +ntv: Nat, +cur: List<&2, U32>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Rw>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      +h = sp.vhead(impl)
      +itys = sp.norms(List.append(&2, X.Sx, sp.els(sp.subst(sp.l(sp.spine.tys(impl, Nil{})), sbs)), sp.dropn(tys, ntv)), Ix{dfs, lcs, pss, ins, cls, sys, fms, fns})
      +i = X.tsx.atom.of(sp.at(h, 2n))
      +top = sp.lc.find(lcs, m, i)
      +tt = Maybe.default(&2, X.Sx, top, X.SxNil{})
      +derived = Bool.and(sp.has(tt, S.b("generated")), Bool.not(Bool.or(sp.has.str(tt, S.b("coerce")), S.prefix(sp.sat(h, 1n), S.b("$cshow")))))
      Bool.pick(Maybe<&2, Rw>, Bool.and(sp.head.is(h, "l"), Bool.and(Maybe.is_some(&2, X.Sx, top), Bool.not(derived))), sp.ask(cur, sp.name(sp.sat(h, 1n), tys), LoL{m, i}, itys), Bool.pick(Maybe<&2, Rw>, sp.head.is(h, "g"), sp.ask.def(cur, h, itys, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}), None{}))

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

def sp.ask.meth(mi: Maybe<&2, Mi>, +cur: List<&2, U32>, +tys: List<&2, X.Sx>, +ix: Ix) -> Maybe<&2, Rw>:
  match mi:
    case Some{Mi{+impl, +m, +sbs, +ntv, +first}}:
      +k0 = sp.gkey(sp.vhead(impl))
      +k = Bool.pick(List<&2, U32>, sp.is(sp.hd(sp.vhead(impl)), "l"), sp.gkey(sp.vhead(sp.or(sp.impl.body(Some{Mi{impl, m, sbs, ntv, first}}, tys, ix), X.SxNil{}))), k0)
      +seq = Bool.or(sp.is(k, "GHC.Internal.Data.Traversable.$dmsequence"), sp.is(k, "GHC.Internal.Data.Traversable.$dmsequenceA"))
      +mapm = sp.is(k, "GHC.Internal.Data.Traversable.$dmmapM")
      +shw = sp.is(k, "GHC.Internal.Show.$dmshow")
      +shl = sp.is(k, "GHC.Internal.Show.$dmshowList")
      +t0 = Maybe.default(&2, X.Sx, sp.nth(tys, 0n), X.SxNil{})
      +f1 = Maybe.default(&2, X.Sx, sp.nth(tys, 1n), X.SxNil{})
      +a2 = Maybe.default(&2, X.Sx, sp.nth(tys, 2n), X.SxNil{})
      +fa = sp.norm(sp.l([sp.a("tapp"), f1, a2]), ix)
      Bool.pick(Maybe<&2, Rw>, Bool.or(shw, shl), sp.wrap.via(sp.ask.impl(first, m, sbs, ntv, cur, tys, ix), Bool.pick(List<&2, U32>, shw, S.b("showVia"), S.b("showListVia")), t0),       Bool.pick(Maybe<&2, Rw>, seq, sp.wrap.id(sp.ask.impl(first, m, sbs, ntv, cur, [t0, f1, fa, a2], ix), fa), Bool.pick(Maybe<&2, Rw>, mapm, sp.ask.impl(first, m, sbs, ntv, cur, tys, ix), sp.ask.impl(impl, m, sbs, ntv, cur, tys, ix))))
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

def sp.p4.decide(isp: Bool, +x: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Maybe<&2, Rw>:
  match isp:
    case True{}:
      +h = sp.vhead(x)
      +tys = sp.norms(sp.spine.tys(x, Nil{}), ix)
      +meth = Bool.not(S.eq(sp.method.cls(h), Nil{}))
      sp.p4.ask(Bool.pick(Dk, Bool.not(sp.all.closed(tys)), DkNo{}, Bool.pick(Dk, meth, DkMeth{}, Bool.pick(Dk, sp.head.is(h, "g"), DkDef{}, DkNo{}))), h, tys, cur, ix)
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
    case Rq{n, LoG{k}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      sp.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.df.find(dfs, k), t => sp.fun.of(t)), Nil{}, n, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns})
    case Rq{n, LoL{m, i}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}:
      +top = sp.lc.find(lcs, m, i)
      sp.copy.of(Maybe.bind(&2, X.Sx, X.Sx, top, t => sp.fun.of(t)), sp.strs(sp.at(sp.at(Maybe.default(&2, X.Sx, top, X.SxNil{}), 1n), 1n)), n, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns})
    case Rq{n, LoF{k, fas, fvt}, tys} i:
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

def sp.p7(x: X.Sx, +ix: Ix) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{f, X.SxCons{t, X.SxNil{}}}}:
      sp.p7.at(sp.is(a, "tyapp"), a, sp.p7(f, ix), sp.p7(t, ix), ix)
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
# copy, is a call of the copy. Bend calls a closure at most once and takes a
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

# (self V) as V, everywhere
def sp.fa.unself(x: X.Sx) -> X.Sx:
  match x:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+v, X.SxNil{}}}:
      Bool.pick(X.Sx, sp.is(a, "self"), sp.fa.unself(v), X.SxCons{X.SxAtom{a}, X.SxCons{sp.fa.unself(v), X.SxNil{}}})
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

def sp.fa.hash(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case c <> t:
      sp.fa.hash(t, (h * 33 + c : U32))

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

# the decision on a call x of the def fun: its copy's call and the copy
# asked for, or none
def sp.fa.at(m: Maybe<&2, X.Sx>, +h: X.Sx, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>) -> Maybe<&2, Fd>:
  match m:
    case Some{+fun}:
      +tys = sp.norms(sp.spine.tys(sp.fa.fn(x), Nil{}), ix)
      +tvs = sp.foralls(sp.at(fun, 2n))
      +tyok = Bool.and(Nat.is_eq(List.length(&2, List<&2, U32>, tvs), List.length(&2, X.Sx, tys)), sp.all.closed(tys))
      +sbs = sp.zip(tvs, tys)
      +ptys = sp.fa.params(sp.subst(sp.strip(sp.at(fun, 2n)), sbs))
      +ms = sp.at(fun, 4n)
      +args = sp.spine.args(x, Nil{})
      +fas0 = sp.fa.pick(args, ptys, sp.els(sp.at(ms, 4n)), 0n, X.tsx.len(sp.at(ms, 1n)), sp.ix.sys(ix))
      +frees = sp.fa.frees.all(fas0, Nil{})
      +fvt = sp.fa.tys(frees, env)
      +fas = sp.fa.canon(fas0, sp.fa.canon.map(frees, 0n))
      +base = sp.cat(sp.name(sp.sat(h, 2n), tys), S.b("_f"))
      +n = sp.cat(base, S.b(U32.show(sp.fa.hash(X.tsx.show(sp.fa.key(fas)), 5381))))
      +inself = Bool.or(S.eq(me, sp.sat(h, 2n)), Bool.and(S.prefix(me, base), Bool.not(S.eq(me, n))))
      +ok = Bool.and(tyok, Bool.and(Bool.not(List.is_empty(&2, Fa, fas0)), Bool.and(sp.fa.tys.ok(fvt), Bool.not(Bool.or(inself, sp.fa.hasev(sp.fa.fn(x)))))))
      +hd = sp.fa.apps(frees, sp.g(cur, n, "var"))
      Bool.pick(Maybe<&2, Fd>, ok, Some{Fd{hd, fas, [Rq{n, LoF{sp.gkey(h), fas, sp.fa.tys.get(fvt)}, tys}]}}, None{})
    case None{}:
      None{}

def sp.fa.decide(+x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>) -> Maybe<&2, Fd>:
  match ix:
    case Ix{dfs, lcs, pss, ins, cls, sys, fms, +fns}:
      +h = sp.fa.unself(sp.spine.head(x))
      +top = Bool.pick(Maybe<&2, X.Sx>, sp.head.is(h, "g"), sp.df.find(fns, sp.gkey(h)), None{})
      sp.fa.at(Maybe.bind(&2, X.Sx, X.Sx, top, t => sp.fun.of(t)), h, x, me, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns}, env)

def sp.rw.addq(r: Rw, q: List<&2, Rq>) -> Rw:
  match r:
    case Rw{x, p}:
      Rw{x, sp.rw.cat(p, q)}

# a call's decision: the copy's function part (its name applied to the free
# locals), the places of the arguments that go, the copy asked for
type Fd is Data:
  Fd{hd: X.Sx, fas: List<&2, Fa>, q: List<&2, Rq>}

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

def sp.fa.decide.if(isapp: Bool, +x: X.Sx, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>) -> Maybe<&2, Fd>:
  match isapp:
    case True{}:
      sp.fa.decide(x, me, cur, ix, env)
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
def sp.p10(x: X.Sx, m: Pm, +me: List<&2, U32>, +cur: List<&2, U32>, +ix: Ix, +env: List<&2, Asb>) -> Rw:
  match x m:
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} PmNode{top}:
      +n = {X.SxCons{X.SxAtom{a}, X.SxCons{f, X.SxCons{e, X.SxNil{}}}} : X.Sx}
      +k = List.length(&2, X.Sx, sp.spine.args(n, Nil{}))
      +d = sp.fa.decide.if(Bool.and(top, sp.is(a, "app")), n, me, cur, ix, env)
      sp.fd.fin(d, a, sp.p10(f, sp.fd.mode(d, k, sp.isapp(n)), me, cur, ix, env), sp.p10(e, PmNode{True{}}, me, cur, ix, env), k)
    case X.SxCons{X.SxAtom{+a}, X.SxCons{+f, X.SxCons{+e, X.SxNil{}}}} PmArgs{+hd, +i, +fas}:
      +j = Bool.pick(Nat, sp.is(a, "app"), sp.pred(i), i)
      sp.p10.spine(a, i, fas, hd, sp.p10(f, PmArgs{hd, j, fas}, me, cur, ix, env), sp.p10(e, PmNode{True{}}, me, cur, ix, env))
    case X.SxCons{+h, +t} PmNode{top}:
      sp.rw.cons(sp.p10(h, PmNode{True{}}, me, cur, ix, env), sp.p10(t, PmNode{True{}}, me, cur, ix, env))
    case _ PmArgs{hd, i, fas}:
      Rw{hd, Nil{}}
    case y PmNode{top}:
      Rw{y, Nil{}}

# the name a top exports first (its def's)
def sp.fa.me(+x: X.Sx) -> List<&2, U32>:
  +es = sp.exports(x)
  sp.sat(sp.at(sp.or(sp.nth(es, 0n), X.SxNil{}), 1n), 2n)

def sp.rw.p10(r: Rw, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match r:
    case Rw{+x, q}:
      +env = sp.fa.binds(x, Nil{})
      sp.rw.addq(sp.p10(x, PmNode{True{}}, sp.fa.me(x), cur, ix, env), q)

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
    case Rq{n, LoF{k, fas, fvt}, tys} Ix{dfs, lcs, pss, ins, cls, sys, fms, +fns}:
      sp.fa.copy.of(Maybe.bind(&2, X.Sx, X.Sx, sp.df.find(fns, k), t => sp.fun.of(t)), n, fas, fvt, tys, cur, Ix{dfs, lcs, pss, ins, cls, sys, fms, fns})
    case r i:
      sp.copy(r, cur, i)

# a binding's passes: pattern synonyms, views, copies' calls, normal type
# arguments
def sp.passes(+x: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  +xp = sp.beta(sp.pl(sp.pc(x), ix))
  +x0 = sp.p0(xp, sp.isfun(xp))
  +y = sp.p1.go(12n, x0, sp.has.str(x0, S.b("PatSynCon")), ix)
  sp.rw.p10(sp.rw.p9(sp.rw.p7(sp.p4(sp.p8(sp.p3(y, sp.ispv(y), ix), False{}), True{}, cur, ix), ix)), cur, ix)

def sp.rq.name(rq: Rq) -> List<&2, U32>:
  match rq:
    case Rq{n, lo, tys}:
      n

def sp.work.at(m: Maybe<&2, X.Sx>, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match m:
    case Some{top}:
      sp.passes(top, cur, ix)
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
      +r = sp.work.at(sp.copy.any(rq, cur, ix), cur, ix)
      +todo2 = List.append(&2, Rq, rest, sp.work.rq(r))
      +done2 = sp.names.cons(nm, done)
      sp.work(k, todo2, sp.work.seen(todo2, done2), done2, sp.work.put(r, acc), cur, ix)
    case _ _ _:
      List.reverse(&2, X.Sx, acc)

# A module: each top's passes, then the copies they ask for
def sp.items.one(top: Bool, +x: X.Sx, +cur: List<&2, U32>, +ix: Ix) -> Rw:
  match top:
    case True{}:
      sp.passes(x, cur, ix)
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

def sp.module(+xs: List<&2, X.Sx>, +ix: Ix) -> List<&2, X.Sx>:
  +cur = sp.modname(xs)
  +r = sp.items(xs, cur, ix)
  List.append(&2, X.Sx, sp.els(sp.rw.x(r)), sp.work(4000n, sp.work.rq(r), False{}, Nil{}, Nil{}, cur, ix))

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

def sp.p5.tc(+k: List<&2, U32>, +x: X.Sx) -> X.Sx:
  +integer = sp.is(k, "GHC.Num.Integer.Integer")
  +int = Bool.or(sp.is(k, "GHC.Types.Int"), Bool.or(False{}, Bool.or(sp.is(k, "Data.IntSet.Internal.Key"), sp.is(k, "Data.IntMap.Internal.Key"))))
  +im = sp.is(k, "Data.IntMap.Internal.IntMap")
  +iset = sp.is(k, "Data.IntSet.Internal.IntSet")
  +dig = sp.is(k, "Crypto.Hash.Types.Digest")
  +sha = Bool.or(sp.is(k, "Crypto.Hash.SHA256.SHA256"), sp.is(k, "Crypto.Hash.Algorithms.SHA256"))
  +bs = Bool.or(Bool.or(sp.is(k, "Data.ByteString.Internal.Type.ByteString"), sp.is(k, "Data.ByteString.Internal.Type.StrictByteString")), Bool.or(sp.is(k, "Data.ByteString.Lazy.Internal.ByteString"), sp.is(k, "Data.ByteString.Lazy.Internal.LazyByteString")))
  Bool.pick(X.Sx, dig, sp.tc(S.b("HsPrelude"), S.b("HsDigest"), Nil{}), Bool.pick(X.Sx, sha, sp.tc(S.b("GHC.Tuple"), S.b("Unit"), Nil{}), Bool.pick(X.Sx, bs, sp.tc(S.b("GHC.Types"), S.b("List"), [sp.tc(S.b("GHC.Internal.Word"), S.b("Word8"), Nil{})]), Bool.pick(X.Sx, int, sp.hsint(), Bool.pick(X.Sx, integer, sp.tc(S.b("HsPrelude"), S.b("HsInteger"), Nil{}), Bool.pick(X.Sx, im, sp.tc(S.b("Data.Map.Internal"), S.b("Map"), sp.hsint() <> sp.els(X.tsx.args(X.tsx.args(X.tsx.args(x))))), Bool.pick(X.Sx, iset, sp.tc(S.b("Data.Set.Internal"), S.b("Set"), [sp.hsint()]), x)))))))

# an IntMap or IntSet function's Map or Set name, and where its key goes
def sp.p5.mod(+m: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, sp.is(m, "Data.IntMap.Internal"), S.b("Data.Map.Internal"), Bool.pick(List<&2, U32>, sp.is(m, "Data.IntMap.Strict.Internal"), S.b("Data.Map.Strict.Internal"), Bool.pick(List<&2, U32>, sp.is(m, "Data.IntSet.Internal"), S.b("Data.Set.Internal"), Nil{})))

def sp.p5.last(+m: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  Bool.or(Bool.and(Bool.not(sp.is(m, "Data.IntSet.Internal")), Bool.or(sp.is(n, "map"), Bool.or(sp.is(n, "filter"), sp.is(n, "foldr")))), Bool.and(sp.is(m, "Data.IntSet.Internal"), sp.is(n, "unions")))

def sp.mkspine(ts: List<&2, X.Sx>, h: X.Sx) -> X.Sx:
  match ts:
    case Nil{}:
      h
    case t <> r:
      sp.mkspine(r, sp.l([sp.a("tyapp"), h, t]))

# a spine (or a bare name) whose head is an IntMap or IntSet function
def sp.p5.call(+x: X.Sx) -> Maybe<&2, X.Sx>:
  +h = sp.vhead(x)
  +m = sp.sat(h, 1n)
  +n = sp.sat(h, 2n)
  +nm = sp.p5.mod(m)
  +tys = sp.spine.tys(x, Nil{})
  +ks = Bool.pick(List<&2, X.Sx>, sp.p5.last(m, n), List.append(&2, X.Sx, tys, [sp.hsint()]), sp.hsint() <> tys)
  Bool.pick(Maybe<&2, X.Sx>, Bool.and(sp.head.is(h, "g"), Bool.not(S.eq(nm, Nil{}))), Some{sp.mkspine(ks, sp.g(nm, n, "var"))}, None{})

def sp.p5.isg(+x: X.Sx) -> Bool:
  Bool.or(sp.isty(x), sp.head.is(x, "g"))

# Identity's constructor and runIdentity are id (the fold erases the
# newtype), a pattern Identity p is p; base's functions whose Int is HsInt
# here (length, take, drop, replicate, ord, chr) are HsPrelude.Z's
def sp.p5.ident(+y: X.Sx) -> X.Sx:
  +k = sp.gkey(y)
  +idc = Bool.or(sp.is(k, "GHC.Internal.Data.Functor.Identity.Identity"), sp.is(k, "GHC.Internal.Data.Functor.Identity.runIdentity"))
  +pid = Bool.and(sp.head.is(y, "pcon"), sp.is(sp.gkey(sp.at(y, 1n)), "GHC.Internal.Data.Functor.Identity.Identity"))
  +z = Bool.or(Bool.or(sp.is(k, "GHC.Internal.Data.Foldable.length"), sp.is(k, "GHC.Internal.List.take")), Bool.or(Bool.or(sp.is(k, "GHC.Internal.List.drop"), sp.is(k, "GHC.Internal.List.replicate")), Bool.or(sp.is(k, "GHC.Internal.Base.ord"), sp.is(k, "GHC.Internal.Char.chr"))))
  Bool.pick(X.Sx, idc, sp.g(S.b("GHC.Internal.Base"), S.b("id"), "var"), Bool.pick(X.Sx, pid, sp.at(sp.at(y, 3n), 1n), Bool.pick(X.Sx, z, sp.l([sp.a("g"), X.SxStr{S.b("HsPrelude.Z")}, sp.at(y, 2n), sp.at(y, 3n)]), y)))

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

# top: x is no spine's function (so a spine is judged whole)
def sp.p5(x: X.Sx, top: Bool) -> X.Sx:
  match x:
    case X.SxCons{+h, X.SxCons{+e, +r}}:
      +a = X.tsx.atom.of(h)
      +inner = sp.isty(X.SxCons{h, X.SxCons{e, r}})
      +y = sp.cons(sp.p5(h, True{}), sp.cons(sp.p5(e, Bool.not(inner)), sp.p5(r, True{})))
      +c = Bool.pick(Maybe<&2, X.Sx>, Bool.and(top, sp.p5.isg(X.SxCons{h, X.SxCons{e, r}})), sp.p5.call(y), None{})
      Bool.pick(X.Sx, Maybe.is_some(&2, X.Sx, c), sp.or(c, X.SxNil{}), Bool.pick(X.Sx, sp.is(a, "tc"), sp.p5.tc(sp.key(sp.sat(y, 1n), sp.sat(y, 2n)), y), sp.zf(sp.p5.ident(y))))
    case X.SxCons{+h, X.SxNil{}}:
      X.SxCons{sp.p5(h, True{}), X.SxNil{}}
    case y:
      y

def sp.p5s(xs: List<&2, X.Sx>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.p5(sp.p6(x), True{}) <> sp.p5s(t)

# The program ------------------------------------------------------------------------

def sp.text(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      sp.cat(X.tsx.show(x), 10 <> sp.text(t))

def sp.run(fs: List<String>, +out: String, ix: Ix, list: List<&2, U32>) -> IO(Unit):
  match fs:
    case Nil{}:
      S.write(out ++ "/modules.txt", list)
    case +f <> t:
      do IO<Unit>:
        bytes : List<&2, U32> <- S.read(f)
        +xs : List<&2, X.Sx> <- IO.pure(List<&2, X.Sx>, sp.p5s(X.tsx.read(bytes)))
        +ix2 : Ix <- IO.pure(Ix, sp.ix.module(xs, ix))
        +p : String <- IO.pure(String, out ++ "/" ++ S.base(f))
        S.write(p, sp.text(sp.module(xs, ix2)))
        sp.run(t, out, ix2, sp.cat(list, sp.cat(S.b(p), [10])))

def sp.main(args: List<String>) -> IO(Unit):
  match args:
    case out <> files:
      sp.run(files, out, sp.ix0(), Nil{})
    case Nil{}:
      IO.print("usage: spec OUTDIR FILE.sexp...")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    sp.main(List.tail(&1, String, argv))

