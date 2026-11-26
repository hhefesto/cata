import Base
import ./a2b/Sys.bend as S
import ./a2b/ToBend/Sexp.bend as X

# Prune: a package as one program runs it.  `prune ROOTS OUTDIR FILE.sexp...`
# reads a package's specialised modules (spec's output, in dependency order)
# and writes them again to OUTDIR (same names, and modules.txt) as the
# program whose entry points ROOTS names runs them:
#
#   - a binding nothing from the roots reaches is left out (its name is
#     never called, its dictionary never passed);
#   - a constructor's field that nothing reached reads (no pattern binds it
#     to more than a wildcard, no selector of it is reached, the
#     constructor is never applied to fewer arguments than reach it) is
#     left out of its data type, of each construction (and the term built
#     for it with it) and of each pattern;
#   - a local binding (a where's or a let's group) nothing in its scope
#     names is left out, unless a bang makes it strict;
#   - a parameter of a def that none of its clauses uses is left out of
#     the def, its type and every call, when every use of the def is a
#     call that gives it (a def passed as a value keeps its parameters);
#
# again until nothing changes (a field left out can leave a def's
# parameter unused, the call's argument then unbuilt, the defs it alone
# called unreached).  Haskell never evaluates a field nothing reads, nor
# an argument a def ignores; Bend evaluates both where they are built, so
# a run of the fold of the package as it was builds what GHC's run never
# does (telomare's CompiledProgram's cpGuidance and cpVerdict, a second
# EAL inference of the sized program, hours in Bend, never forced by the
# reference evaluator).  This is for a program's run; the laws are told on
# the package as it is.
#
# ROOTS is a file of lines: `M.N`, a binding the program's entry calls (a
# Bend front, written by hand, calls these, so they keep their parameters);
# `type M.T`, a data type whose fields the entry reads or builds (they stay).
# A line starting with `#` is a comment.
#
# Every def is prefixed `pr.`.

# Trees ---------------------------------------------------------------------

def pr.a(s: String) -> X.Sx:
  X.SxAtom{S.b(s)}

def pr.l(xs: List<&2, X.Sx>) -> X.Sx:
  match xs:
    case Nil{}:
      X.SxNil{}
    case +h <> +t:
      X.SxCons{h, pr.l(t)}

def pr.els(x: X.Sx) -> List<&2, X.Sx>:
  match x:
    case X.SxCons{+h, +t}:
      h <> pr.els(t)
    case _:
      Nil{}

# an if whose branches are thunks
def pr.if(-R: Type, c: Bool, t: Unit -> R, e: Unit -> R) -> R:
  match c:
    case True{}:
      t(Unit{})
    case False{}:
      e(Unit{})

def pr.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def pr.ascii(+s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{c}, t}:
      Bool.and(U32.is_lt(c, 128), pr.ascii(t))

def pr.is.go(x: List<&2, U32>, s: String, ok: Bool) -> Bool:
  match x s ok:
    case _ _ False{}:
      False{}
    case Nil{} SNil{} True{}:
      True{}
    case b <> xt SCon{Chr{c}, st} True{}:
      pr.is.go(xt, st, U32.is_eq(b, c))
    case _ _ True{}:
      False{}

def pr.is.at(asc: Bool, +x: List<&2, U32>, s: String) -> Bool:
  match asc:
    case True{}:
      pr.is.go(x, s, True{})
    case False{}:
      S.eq(x, S.b(s))

# whether the bytes x are the string s
def pr.is(+x: List<&2, U32>, +s: String) -> Bool:
  pr.is.at(pr.ascii(s), x, s)

def pr.hd(+x: X.Sx) -> List<&2, U32>:
  X.tsx.head(x)

def pr.head.is(+x: X.Sx, s: String) -> Bool:
  pr.is(pr.hd(x), s)

def pr.at(+x: X.Sx, +i: Nat) -> X.Sx:
  X.tsx.at(i, x)

def pr.sat(+x: X.Sx, +i: Nat) -> List<&2, U32>:
  X.tsx.str.of(X.tsx.at(i, x))

def pr.fuel() -> Nat:
  U32.to_nat(4294967295)

def pr.nb(n: Nat) -> List<&2, U32>:
  S.b(Nat.show(n))

# Maps keyed by bytes -------------------------------------------------------

def pr.has.got(r: Map<&2, Bool> & Bool) -> Bool:
  match r:
    case Tuple{m, b}:
      b

def pr.has(+m: Map<&2, Bool>, +k: List<&2, U32>) -> Bool:
  pr.has.got(Map.has(&2, Bool, m, S.str(k)))

def pr.set(m: Map<&2, Bool>, +k: List<&2, U32>) -> Map<&2, Bool>:
  Map.set(&2, Bool, m, S.str(k), True{})

def pr.sets.go(ks: List<&2, List<&2, U32>>, m: Map<&2, Bool>) -> Map<&2, Bool>:
  match ks:
    case Nil{}:
      m
    case +k <> +t:
      pr.sets.go(t, pr.set(m, k))

def pr.sets(m: Map<&2, Bool>, ks: List<&2, List<&2, U32>>) -> Map<&2, Bool>:
  pr.sets.go(ks, m)

def pr.refs.got(r: Map<&2, List<&2, List<&2, U32>>> & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match r:
    case Tuple{m, v}:
      v

def pr.nat.got(r: Map<&2, Nat> & Nat) -> Nat:
  match r:
    case Tuple{m, v}:
      v

def pr.nat(+m: Map<&2, Nat>, +k: List<&2, U32>, +d: Nat) -> Nat:
  pr.nat.got(Map.get(Nat, d, m, S.str(k)))

# Names ---------------------------------------------------------------------

# a global's key, M.N, of (g M N K)
def pr.gk(+x: X.Sx) -> List<&2, U32>:
  pr.cat(pr.sat(x, 1n), 46 <> pr.sat(x, 2n))

# a local's key in module m, m#N#n, of (l N n): a local is the file's
def pr.lk(+m: List<&2, U32>, +x: X.Sx) -> List<&2, U32>:
  pr.cat(m, 35 <> pr.cat(pr.sat(x, 1n), 35 <> X.tsx.atom.of(pr.at(x, 2n))))

# a name node's key: (g ..), (l ..), (self X); else none
def pr.nk.go(fuel: Nat, +m: List<&2, U32>, +x: X.Sx) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+p):
      +h = pr.hd(x)
      pr.if(List<&2, U32>, pr.is(h, "g"), _ => pr.gk(x), _ => pr.if(List<&2, U32>, pr.is(h, "l"), _ => pr.lk(m, x), _ => pr.if(List<&2, U32>, pr.is(h, "self"), _ => pr.nk.go(p, m, pr.at(x, 1n)), _ => Nil{})))

def pr.nk(+m: List<&2, U32>, +x: X.Sx) -> List<&2, U32>:
  pr.nk.go(4n, m, x)

# whether a (g M N K) node is of kind k
def pr.gkind.is(+x: X.Sx, k: String) -> Bool:
  Bool.and(pr.head.is(x, "g"), pr.is(X.tsx.atom.of(pr.at(x, 3n)), k))

# Items ---------------------------------------------------------------------

# A module: its name, its file, its forms.
type Md is Data:
  Md{n: List<&2, U32>, f: String, xs: List<&2, X.Sx>}

def pr.md.n(+d: Md) -> List<&2, U32>:
  match d:
    case Md{n, f, xs}:
      n

def pr.modname(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      pr.if(List<&2, U32>, pr.head.is(x, "module"), _ => pr.sat(x, 1n), _ => pr.modname(t))

# the names an export list (export NAME TYPE)... binds
def pr.exports(+m: List<&2, U32>, xs: X.Sx) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{+e, t}:
      pr.nk(m, pr.at(e, 1n)) <> pr.exports(m, t)
    case _:
      Nil{}

# the binders (bv NAME TYPE) of a tree (a pattern binding's)
def pr.bvs(fuel: Nat, +m: List<&2, U32>, +x: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      acc
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          pr.if(List<&2, List<&2, U32>>, pr.head.is(x, "bv"), _ => pr.nk(m, pr.at(x, 1n)) <> acc, _ => pr.bvs(p, m, t, pr.bvs(p, m, h, acc)))
        case _:
          acc

# an evbinds list's binders: (evbind (bv NAME T) E)...
def pr.evbs(+m: List<&2, U32>, xs: X.Sx) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{+e, t}:
      pr.nk(m, pr.at(pr.at(e, 1n), 1n)) <> pr.evbs(m, t)
    case _:
      Nil{}

# the names a top-level form binds (none: a declaration, always kept)
def pr.keys(+m: List<&2, U32>, +x: X.Sx) -> List<&2, List<&2, U32>>:
  +b = pr.at(x, 1n)
  +h = pr.hd(b)
  pr.if(List<&2, List<&2, U32>>, pr.head.is(x, "top-evbinds"), _ => pr.evbs(m, X.tsx.args(x)), _ => pr.if(List<&2, List<&2, U32>>, Bool.not(pr.head.is(x, "top")), _ => Nil{}, _ => pr.if(List<&2, List<&2, U32>>, pr.is(h, "abs"), _ => pr.exports(m, pr.at(b, 3n)), _ => pr.if(List<&2, List<&2, U32>>, Bool.or(pr.is(h, "fun"), pr.is(h, "varbind")), _ => [pr.nk(m, pr.at(b, 1n))], _ => pr.bvs(pr.fuel(), m, pr.at(b, 1n), Nil{})))))

# every name a tree refers to, but a record field's selector (a pattern
# C{f = p} reads f only as p does)
def pr.refs(fuel: Nat, +m: List<&2, U32>, +x: X.Sx, +node: Bool, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      acc
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          +hd = X.tsx.atom.of(h)
          +nm = Bool.and(node, Bool.or(pr.is(hd, "g"), pr.is(hd, "l")))
          +pf = Bool.and(node, pr.is(hd, "pfield"))
          pr.if(List<&2, List<&2, U32>>, nm, _ => pr.nk(m, x) <> acc, _ => pr.if(List<&2, List<&2, U32>>, pf, _ => pr.refs(p, m, pr.at(x, 2n), True{}, acc), _ => pr.refs(p, m, t, False{}, pr.refs(p, m, h, True{}, acc))))
        case _:
          acc

def pr.idx.put(ks: List<&2, List<&2, U32>>, +rs: List<&2, List<&2, U32>>, ix: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, List<&2, List<&2, U32>>>:
  match ks:
    case Nil{}:
      ix
    case +k <> +t:
      pr.idx.put(t, rs, Map.set(&2, List<&2, List<&2, U32>>, ix, S.str(k), rs))

def pr.idx.forms(+m: List<&2, U32>, xs: List<&2, X.Sx>, ix: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, List<&2, List<&2, U32>>>:
  match xs:
    case Nil{}:
      ix
    case +x <> +t:
      pr.idx.forms(m, t, pr.idx.put(pr.keys(m, x), pr.refs(pr.fuel(), m, x, True{}, Nil{}), ix))

# each binding's name to the names it refers to
def pr.idx(ds: List<&2, Md>, ix: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, List<&2, List<&2, U32>>>:
  match ds:
    case Nil{}:
      ix
    case Md{+n, f, xs} <> t:
      pr.idx(t, pr.idx.forms(n, xs, ix))

def pr.reach.at(seen: Bool, +k: List<&2, U32>, t: List<&2, List<&2, U32>>, s: Map<&2, Bool>, +ix: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, U32>> & Map<&2, Bool>:
  match seen:
    case True{}:
      (t, s)
    case False{}:
      (List.append(&2, List<&2, U32>, pr.refs.got(Map.get(List<&2, List<&2, U32>>, Nil{}, ix, S.str(k))), t), pr.set(s, k))

def pr.reach.step(r: Map<&2, Bool> & Bool, +k: List<&2, U32>, t: List<&2, List<&2, U32>>, +ix: Map<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, U32>> & Map<&2, Bool>:
  match r:
    case Tuple{s, b}:
      pr.reach.at(b, k, t, s, ix)

# the names reached from todo
def pr.reach(fuel: Nat, st: List<&2, List<&2, U32>> & Map<&2, Bool>, +ix: Map<&2, List<&2, List<&2, U32>>>) -> Map<&2, Bool>:
  match fuel:
    case 0n:
      match st:
        case Tuple{todo, s}:
          s
    case 1n+(+p):
      match st:
        case Tuple{todo, s}:
          match todo:
            case Nil{}:
              s
            case +k <> +t:
              pr.reach(p, pr.reach.step(Map.has(&2, Bool, s, S.str(k)), k, t, ix), ix)

def pr.any(ks: List<&2, List<&2, U32>>, +s: Map<&2, Bool>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case +k <> +t:
      pr.if(Bool, pr.has(s, k), _ => True{}, _ => pr.any(t, s))

# the forms kept: the declarations, and the bindings reached
def pr.keep.forms(+m: List<&2, U32>, xs: List<&2, X.Sx>, +s: Map<&2, Bool>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      +ks = pr.keys(m, x)
      +k = Bool.or(List.is_empty(&2, List<&2, U32>, ks), pr.any(ks, s))
      pr.if(List<&2, X.Sx>, k, _ => x <> pr.keep.forms(m, t, s), _ => pr.keep.forms(m, t, s))

def pr.keep(ds: List<&2, Md>, +s: Map<&2, Bool>) -> List<&2, Md>:
  match ds:
    case Nil{}:
      Nil{}
    case Md{+n, f, xs} <> t:
      Md{n, f, pr.keep.forms(n, xs, s)} <> pr.keep(t, s)

def pr.count(ds: List<&2, Md>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Md{n, f, xs} <> t:
      Nat.add(List.length(&2, X.Sx, xs), pr.count(t))

# Fields --------------------------------------------------------------------

# A constructor: its key M.C, its fields' names (none: positional), its arity.
type Cn is Data:
  Cn{k: List<&2, U32>, fs: List<&2, List<&2, U32>>, n: Nat}

def pr.strs(xs: X.Sx) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{+h, +t}:
      X.tsx.str.of(h) <> pr.strs(t)
    case _:
      Nil{}

# (con NAME (FIELD...) (ARGTYPE...) (ex NEX NTHETA)): existentials and
# constraints keep their fields
def pr.cn.of(+m: List<&2, U32>, +c: X.Sx) -> List<&2, Cn>:
  +ex = pr.at(c, 4n)
  +plain = Bool.and(pr.is(X.tsx.atom.of(pr.at(ex, 1n)), "0"), pr.is(X.tsx.atom.of(pr.at(ex, 2n)), "0"))
  pr.if(List<&2, Cn>, plain, _ => [Cn{pr.cat(m, 46 <> pr.sat(c, 1n)), pr.strs(pr.at(c, 2n)), X.tsx.len(pr.at(c, 3n))}], _ => Nil{})

def pr.cns.of(+m: List<&2, U32>, cs: X.Sx) -> List<&2, Cn>:
  match cs:
    case X.SxCons{+c, t}:
      List.append(&2, Cn, pr.cn.of(m, c), pr.cns.of(m, t))
    case _:
      Nil{}

# a data type's (not a newtype's) constructors, with its key M.T
type Dt is Data:
  Dt{k: List<&2, U32>, cs: List<&2, Cn>}

def pr.dts.forms(+m: List<&2, U32>, xs: List<&2, X.Sx>) -> List<&2, Dt>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      pr.if(List<&2, Dt>, pr.head.is(x, "data"), _ => Dt{pr.cat(m, 46 <> pr.sat(x, 1n)), pr.cns.of(m, pr.at(x, 3n))} <> pr.dts.forms(m, t), _ => pr.dts.forms(m, t))

def pr.dts(ds: List<&2, Md>) -> List<&2, Dt>:
  match ds:
    case Nil{}:
      Nil{}
    case Md{+n, f, xs} <> t:
      List.append(&2, Dt, pr.dts.forms(n, xs), pr.dts(t))

def pr.cns(ts: List<&2, Dt>) -> List<&2, Cn>:
  match ts:
    case Nil{}:
      Nil{}
    case Dt{k, cs} <> t:
      List.append(&2, Cn, cs, pr.cns(t))

def pr.ar.put(cs: List<&2, Cn>, m: Map<&2, Nat>) -> Map<&2, Nat>:
  match cs:
    case Nil{}:
      m
    case Cn{+k, fs, n} <> t:
      pr.ar.put(t, Map.set(&2, Nat, m, S.str(k), n))

# a field's read mark: C#i, and C@f for a named one
def pr.mark.i(+c: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  pr.cat(c, 35 <> pr.nb(i))

def pr.mark.f(+c: List<&2, U32>, f: List<&2, U32>) -> List<&2, U32>:
  pr.cat(c, 64 <> f)

# the marks of fields k.. of a constructor of arity n
def pr.from(fuel: Nat, +c: List<&2, U32>, +k: Nat, +n: Nat, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      acc
    case 1n+(+p):
      pr.if(List<&2, List<&2, U32>>, Nat.is_lt(k, n), _ => pr.from(p, c, 1n+k, n, pr.mark.i(c, k) <> acc), _ => acc)

# a pattern's (args P...) marks: each field bound to more than _
def pr.pa.marks(+c: List<&2, U32>, xs: X.Sx, +i: Nat, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{+h, +t}:
      pr.pa.marks(c, t, 1n+i, pr.if(List<&2, List<&2, U32>>, pr.head.is(h, "pwild"), _ => acc, _ => pr.mark.i(c, i) <> acc))
    case _:
      acc

# a field's name: (l f n), or the selector (g M f sel) its lambda calls
def pr.first(+a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  pr.if(List<&2, U32>, List.is_empty(&2, U32, a), _ => b, _ => a)

# the first selector's name in a tree
def pr.selname(fuel: Nat, +x: X.Sx) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          pr.if(List<&2, U32>, pr.gkind.is(x, "sel"), _ => pr.sat(x, 2n), _ => pr.first(pr.selname(p, h), pr.selname(p, t)))
        case _:
          Nil{}

def pr.selname.one(+x: X.Sx) -> List<&2, U32>:
  pr.if(List<&2, U32>, pr.head.is(x, "l"), _ => pr.sat(x, 1n), _ => pr.selname(100000n, x))

# a pattern's (fields (pfield SEL P)...) marks
def pr.pf.marks(+c: List<&2, U32>, xs: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case X.SxCons{+h, +t}:
      pr.pf.marks(c, t, pr.if(List<&2, List<&2, U32>>, pr.head.is(pr.at(h, 2n), "pwild"), _ => acc, _ => pr.mark.f(c, pr.selname.one(pr.at(h, 1n))) <> acc))
    case _:
      acc

def pr.pc.marks(+c: List<&2, U32>, +ps: X.Sx, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  pr.if(List<&2, List<&2, U32>>, pr.head.is(ps, "args"), _ => pr.pa.marks(c, X.tsx.args(ps), 0n, acc), _ => pr.pf.marks(c, X.tsx.args(ps), acc))

# a spine's head and how many terms it is applied to (types and
# dictionaries are not counted): (app (tyapp (g ..) T) a) is (g ..), 1
def pr.spine(fuel: Nat, +x: X.Sx, +k: Nat) -> X.Sx & Nat:
  match fuel:
    case 0n:
      (x, k)
    case 1n+(+p):
      +h = pr.hd(x)
      pr.if(X.Sx & Nat, pr.is(h, "app"), _ => pr.spine(p, pr.at(x, 1n), 1n+k), _ => pr.if(X.Sx & Nat, Bool.or(pr.is(h, "tyapp"), pr.is(h, "evapp")), _ => pr.spine(p, pr.at(x, 1n), k), _ => (x, k)))

def pr.is.spine(+h: List<&2, U32>) -> Bool:
  Bool.or(pr.is(h, "app"), Bool.or(pr.is(h, "tyapp"), pr.is(h, "evapp")))

# a construction's marks: C applied to k terms reads fields k.. (it is a
# function of them)
def pr.con.marks(r: X.Sx & Nat, +ar: Map<&2, Nat>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match r:
    case Tuple{+h, +k}:
      pr.if(List<&2, List<&2, U32>>, pr.gkind.is(h, "con"), _ => pr.from(1000000n, pr.gk(h), k, pr.nat(ar, pr.gk(h), 0n), acc), _ => acc)

# the read marks of a tree: node, whether x is a node (a tail of a list
# else); sp, whether x is on a spine whose head was seen
def pr.mk(fuel: Nat, +x: X.Sx, +node: Bool, +sp: Bool, +ar: Map<&2, Nat>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      acc
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          +hd = X.tsx.atom.of(h)
          pr.if(List<&2, List<&2, U32>>, Bool.not(node), _ => pr.mk(p, t, False{}, False{}, ar, pr.mk(p, h, True{}, False{}, ar, acc)), _ => pr.if(List<&2, List<&2, U32>>, pr.is.spine(hd), _ => pr.if(List<&2, List<&2, U32>>, sp, _ => pr.if(List<&2, List<&2, U32>>, pr.is(hd, "tyapp"), _ => pr.mk(p, pr.at(x, 1n), True{}, True{}, ar, acc), _ => pr.mk(p, pr.at(x, 1n), True{}, True{}, ar, pr.mk(p, pr.at(x, 2n), True{}, False{}, ar, acc))), _ => pr.mk(p, x, True{}, True{}, ar, pr.con.marks(pr.spine(1000000n, x, 0n), ar, acc))), _ => pr.if(List<&2, List<&2, U32>>, pr.is(hd, "g"), _ => pr.if(List<&2, List<&2, U32>>, Bool.and(Bool.not(sp), pr.gkind.is(x, "con")), _ => pr.from(1000000n, pr.gk(x), 0n, pr.nat(ar, pr.gk(x), 0n), acc), _ => acc), _ => pr.if(List<&2, List<&2, U32>>, pr.is(hd, "pcon"), _ => pr.mk(p, pr.at(x, 3n), True{}, False{}, ar, pr.pc.marks(pr.gk(pr.at(x, 1n)), pr.at(x, 3n), acc)), _ => pr.if(List<&2, List<&2, U32>>, Bool.or(Bool.or(pr.is(hd, "pfield"), pr.is(hd, "expanded")), pr.is(hd, "field")), _ => pr.mk(p, pr.at(x, 2n), True{}, False{}, ar, acc), _ => pr.if(List<&2, List<&2, U32>>, pr.is(hd, "reccon"), _ => pr.mk(p, pr.at(x, 2n), False{}, False{}, ar, acc), _ => pr.if(List<&2, List<&2, U32>>, Bool.or(pr.is(hd, "tc"), pr.is(hd, "bv")), _ => acc, _ => pr.mk(p, t, False{}, False{}, ar, pr.mk(p, h, True{}, False{}, ar, acc)))))))))
        case _:
          acc

def pr.mk.forms(xs: List<&2, X.Sx>, +ar: Map<&2, Nat>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case +x <> +t:
      pr.mk.forms(t, ar, pr.if(List<&2, List<&2, U32>>, pr.head.is(x, "data"), _ => acc, _ => pr.mk(pr.fuel(), x, True{}, False{}, ar, acc)))

def pr.mk.mds(ds: List<&2, Md>, +ar: Map<&2, Nat>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ds:
    case Nil{}:
      acc
    case Md{n, f, xs} <> t:
      pr.mk.mds(t, ar, pr.mk.forms(xs, ar, acc))

def pr.cnmarks(cs: List<&2, Cn>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      acc
    case Cn{+k, fs, +n} <> t:
      pr.cnmarks(t, pr.from(1000000n, k, 0n, n, acc))

# the roots' types: every field of each of their constructors is read
def pr.tymarks(ts: List<&2, Dt>, +keep: Map<&2, Bool>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      acc
    case Dt{+k, cs} <> t:
      pr.tymarks(t, keep, pr.if(List<&2, List<&2, U32>>, pr.has(keep, k), _ => pr.cnmarks(cs, acc), _ => acc))

# the drop marks of a constructor's fields: C#i and C@f of each field i
# (named f) nothing reads
def pr.drops.step(fs: List<&2, List<&2, U32>>, +c: List<&2, U32>, +i: Nat, +rd: Map<&2, Bool>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>> & List<&2, List<&2, U32>>:
  match fs:
    case Nil{}:
      (Nil{}, pr.if(List<&2, List<&2, U32>>, pr.has(rd, pr.mark.i(c, i)), _ => acc, _ => pr.mark.i(c, i) <> acc))
    case +f <> +t:
      (t, pr.if(List<&2, List<&2, U32>>, Bool.or(pr.has(rd, pr.mark.i(c, i)), pr.has(rd, pr.mark.f(c, f))), _ => acc, _ => pr.mark.i(c, i) <> pr.mark.f(c, f) <> acc))

def pr.drops.cn(fuel: Nat, +c: List<&2, U32>, st: List<&2, List<&2, U32>> & List<&2, List<&2, U32>>, +i: Nat, +n: Nat, +rd: Map<&2, Bool>) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      match st:
        case Tuple{fs, acc}:
          acc
    case 1n+(+p):
      match st:
        case Tuple{fs, +acc}:
          pr.if(List<&2, List<&2, U32>>, Nat.is_lt(i, n), _ => pr.drops.cn(p, c, pr.drops.step(fs, c, i, rd, acc), 1n+i, n, rd), _ => acc)

def pr.drops(cs: List<&2, Cn>, +rd: Map<&2, Bool>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      acc
    case Cn{+k, fs, +n} <> t:
      pr.drops(t, rd, pr.drops.cn(1000000n, k, (fs, acc), 0n, n, rd))

# Parameters ----------------------------------------------------------------

# A def whose parameters some clause leaves unused: its key, its arity, and
# for each parameter whether every clause leaves it unused.
type Pu is Data:
  Pu{k: List<&2, U32>, us: List<&2, Bool>}

# whether a clause's pattern leaves its parameter unused, given the names
# its right-hand sides refer to
def pr.pat.unused(+m: List<&2, U32>, +x: X.Sx, +used: Map<&2, Bool>) -> Bool:
  pr.if(Bool, pr.head.is(x, "pwild"), _ => True{}, _ => pr.if(Bool, pr.head.is(x, "pvar"), _ => Bool.not(pr.has(used, pr.nk(m, pr.at(pr.at(x, 1n), 1n)))), _ => False{}))

def pr.pats.unused(+m: List<&2, U32>, ps: X.Sx, +used: Map<&2, Bool>) -> List<&2, Bool>:
  match ps:
    case X.SxCons{+h, +t}:
      pr.pat.unused(m, h, used) <> pr.pats.unused(m, t, used)
    case _:
      Nil{}

def pr.and.lists(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case x <> s y <> r:
      Bool.and(x, y) <> pr.and.lists(s, r)
    case _ _:
      Nil{}

# (match (P...) GRHSS): each parameter, whether this clause leaves it unused
def pr.match.unused(+m: List<&2, U32>, +x: X.Sx) -> List<&2, Bool>:
  pr.pats.unused(m, pr.at(x, 1n), pr.sets(Map.new(&2, Bool), pr.refs(pr.fuel(), m, pr.at(x, 2n), True{}, Nil{})))

def pr.trues(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+(+p):
      True{} <> pr.trues(p)

def pr.matches.unused(+m: List<&2, U32>, ms: X.Sx, +acc: List<&2, Bool>) -> List<&2, Bool>:
  match ms:
    case X.SxCons{+h, +t}:
      pr.matches.unused(m, t, pr.and.lists(acc, pr.match.unused(m, h)))
    case _:
      acc

def pr.any.true(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> +t:
      Bool.or(x, pr.any.true(t))

def pr.pu.put(k: List<&2, U32>, +us: List<&2, Bool>) -> List<&2, Pu>:
  pr.if(List<&2, Pu>, pr.any.true(us), _ => [Pu{k, us}], _ => Nil{})

# a top form that is one def: (top (abs TVS EVS ((export X T)) EVB ((fun
# (self X) T SPAN (matches ARGTYS RES ORIGIN (MATCH...)))) SPAN))
def pr.pu.of(+m: List<&2, U32>, +x: X.Sx) -> List<&2, Pu>:
  +b = pr.at(x, 1n)
  +ex = pr.at(b, 3n)
  +bs = pr.at(b, 5n)
  +f = pr.at(bs, 0n)
  +ms = pr.at(f, 4n)
  +one = Bool.and(Bool.and(pr.head.is(x, "top"), pr.head.is(b, "abs")), Bool.and(Bool.and(Nat.is_eq(X.tsx.len(ex), 1n), Nat.is_eq(X.tsx.len(bs), 1n)), Bool.and(pr.head.is(f, "fun"), pr.head.is(ms, "matches"))))
  +g = Bool.and(one, pr.head.is(pr.at(pr.at(ex, 0n), 1n), "g"))
  pr.if(List<&2, Pu>, g, _ => pr.pu.put(pr.gk(pr.at(pr.at(ex, 0n), 1n)), pr.matches.unused(m, pr.at(ms, 4n), pr.trues(X.tsx.len(pr.at(ms, 1n))))), _ => Nil{})

def pr.pu.forms(+m: List<&2, U32>, xs: List<&2, X.Sx>, +acc: List<&2, Pu>) -> List<&2, Pu>:
  match xs:
    case Nil{}:
      acc
    case +x <> +t:
      pr.pu.forms(m, t, List.append(&2, Pu, pr.pu.of(m, x), acc))

def pr.pu.mds(ds: List<&2, Md>, +acc: List<&2, Pu>) -> List<&2, Pu>:
  match ds:
    case Nil{}:
      acc
    case Md{+n, f, xs} <> t:
      pr.pu.mds(t, pr.pu.forms(n, xs, acc))

# A use of a global def: its key, and how many terms it is applied to.
type Oc is Data:
  Oc{k: List<&2, U32>, n: Nat}

def pr.oc.head(r: X.Sx & Nat, +acc: List<&2, Oc>) -> List<&2, Oc>:
  match r:
    case Tuple{+h, +k}:
      +g = pr.if(X.Sx, pr.head.is(h, "self"), _ => pr.at(h, 1n), _ => h)
      pr.if(List<&2, Oc>, pr.gkind.is(g, "var"), _ => Oc{pr.gk(g), k} <> acc, _ => acc)

# every use of a global def (a binder, (export X T) or a fun's name, is none)
def pr.oc(fuel: Nat, +x: X.Sx, +node: Bool, +sp: Bool, +acc: List<&2, Oc>) -> List<&2, Oc>:
  match fuel:
    case 0n:
      acc
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          +hd = X.tsx.atom.of(h)
          pr.if(List<&2, Oc>, Bool.not(node), _ => pr.oc(p, t, False{}, False{}, pr.oc(p, h, True{}, False{}, acc)), _ => pr.if(List<&2, Oc>, pr.is.spine(hd), _ => pr.if(List<&2, Oc>, sp, _ => pr.if(List<&2, Oc>, pr.is(hd, "tyapp"), _ => pr.oc(p, pr.at(x, 1n), True{}, True{}, acc), _ => pr.oc(p, pr.at(x, 1n), True{}, True{}, pr.oc(p, pr.at(x, 2n), True{}, False{}, acc))), _ => pr.oc(p, x, True{}, True{}, pr.oc.head(pr.spine(1000000n, x, 0n), acc))), _ => pr.if(List<&2, Oc>, Bool.or(pr.is(hd, "g"), pr.is(hd, "self")), _ => pr.if(List<&2, Oc>, sp, _ => acc, _ => pr.oc.head((x, 0n), acc)), _ => pr.if(List<&2, Oc>, Bool.or(pr.is(hd, "export"), Bool.or(pr.is(hd, "tc"), pr.is(hd, "bv"))), _ => acc, _ => pr.if(List<&2, Oc>, Bool.or(pr.is(hd, "fun"), pr.is(hd, "varbind")), _ => pr.oc(p, X.tsx.args(t), False{}, False{}, acc), _ => pr.oc(p, t, False{}, False{}, pr.oc(p, h, True{}, False{}, acc)))))))
        case _:
          acc

def pr.oc.forms(xs: List<&2, X.Sx>, +acc: List<&2, Oc>) -> List<&2, Oc>:
  match xs:
    case Nil{}:
      acc
    case +x <> +t:
      pr.oc.forms(t, pr.oc(pr.fuel(), x, True{}, False{}, acc))

def pr.oc.mds(ds: List<&2, Md>, +acc: List<&2, Oc>) -> List<&2, Oc>:
  match ds:
    case Nil{}:
      acc
    case Md{n, f, xs} <> t:
      pr.oc.mds(t, pr.oc.forms(xs, acc))

# the fewest terms each def is applied to
def pr.oc.min(os: List<&2, Oc>, +m: Map<&2, Nat>) -> Map<&2, Nat>:
  match os:
    case Nil{}:
      m
    case Oc{+k, +n} <> t:
      pr.oc.min(t, Map.set(&2, Nat, m, S.str(k), Nat.min(n, pr.nat(m, k, 1000000n))))

# the parameter drop marks X%j: unused by every clause, given at every use,
# not a root's
def pr.pd.us(+k: List<&2, U32>, us: List<&2, Bool>, +j: Nat, +lim: Nat, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match us:
    case Nil{}:
      acc
    case +u <> +t:
      pr.pd.us(k, t, 1n+j, lim, pr.if(List<&2, List<&2, U32>>, Bool.and(u, Nat.is_lt(j, lim)), _ => pr.cat(k, 37 <> pr.nb(j)) <> acc, _ => acc))

def pr.pd(ps: List<&2, Pu>, +mins: Map<&2, Nat>, +roots: Map<&2, Bool>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      acc
    case Pu{+k, us} <> t:
      pr.pd(t, mins, roots, pr.if(List<&2, List<&2, U32>>, pr.has(roots, k), _ => acc, _ => pr.pd.us(k, us, 0n, pr.nat(mins, k, 0n), acc)))

# Rewriting -----------------------------------------------------------------

# a spine with the terms at the dropped places left out: j, the place of
# the outermost term; k, the head's key; sep, `#` (a constructor's
# fields) or `%` (a def's parameters)
def pr.cut(fuel: Nat, +x: X.Sx, +j: Nat, +k: List<&2, U32>, +sep: U32, +d: Map<&2, Bool>) -> X.Sx:
  match fuel:
    case 0n:
      x
    case 1n+(+p):
      +h = pr.hd(x)
      pr.if(X.Sx, pr.is(h, "app"), _ => pr.if(X.Sx, pr.has(d, pr.cat(k, sep <> pr.nb(j))), _ => pr.cut(p, pr.at(x, 1n), Nat.sub(j, 1n), k, sep, d), _ => pr.l([pr.at(x, 0n), pr.cut(p, pr.at(x, 1n), Nat.sub(j, 1n), k, sep, d), pr.at(x, 2n)])), _ => pr.if(X.Sx, Bool.or(pr.is(h, "tyapp"), pr.is(h, "evapp")), _ => pr.l([pr.at(x, 0n), pr.cut(p, pr.at(x, 1n), j, k, sep, d), pr.at(x, 2n)]), _ => x))

# a list's elements but the dropped places (marks k SEP i)
def pr.cut.els(xs: X.Sx, +i: Nat, +k: List<&2, U32>, +sep: U32, +d: Map<&2, Bool>) -> X.Sx:
  match xs:
    case X.SxCons{+h, +t}:
      pr.if(X.Sx, pr.has(d, pr.cat(k, sep <> pr.nb(i))), _ => pr.cut.els(t, 1n+i, k, sep, d), _ => X.SxCons{h, pr.cut.els(t, 1n+i, k, sep, d)})
    case _:
      X.SxNil{}

# a type's arrows but the dropped places: (tforall ..), (tctx ..) go through
def pr.cut.ty(fuel: Nat, +t: X.Sx, +i: Nat, +k: List<&2, U32>, +d: Map<&2, Bool>) -> X.Sx:
  match fuel:
    case 0n:
      t
    case 1n+(+p):
      +h = pr.hd(t)
      pr.if(X.Sx, Bool.or(pr.is(h, "tforall"), pr.is(h, "tctx")), _ => pr.l([pr.at(t, 0n), pr.at(t, 1n), pr.cut.ty(p, pr.at(t, 2n), i, k, d)]), _ => pr.if(X.Sx, pr.is(h, "tfun"), _ => pr.if(X.Sx, pr.has(d, pr.cat(k, 37 <> pr.nb(i))), _ => pr.cut.ty(p, pr.at(t, 2n), 1n+i, k, d), _ => pr.l([pr.at(t, 0n), pr.at(t, 1n), pr.cut.ty(p, pr.at(t, 2n), 1n+i, k, d)])), _ => t))

# (pfield SEL P)... and (field SEL E)... but the dropped fields (C@f)
def pr.cut.named(xs: X.Sx, +c: List<&2, U32>, +d: Map<&2, Bool>) -> X.Sx:
  match xs:
    case X.SxCons{+h, +t}:
      pr.if(X.Sx, pr.has(d, pr.mark.f(c, pr.selname.one(pr.at(h, 1n)))), _ => pr.cut.named(t, c, d), _ => X.SxCons{h, pr.cut.named(t, c, d)})
    case _:
      X.SxNil{}

def pr.cut.pcon(+x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  +c = pr.gk(pr.at(x, 1n))
  +ps = pr.at(x, 3n)
  +ps2 = pr.if(X.Sx, pr.head.is(ps, "args"), _ => X.SxCons{pr.at(ps, 0n), pr.cut.els(X.tsx.args(ps), 0n, c, 35, d)}, _ => X.SxCons{pr.at(ps, 0n), pr.cut.named(X.tsx.args(ps), c, d)})
  pr.l([pr.at(x, 0n), pr.at(x, 1n), pr.at(x, 2n), ps2])

def pr.cut.reccon(+x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  X.SxCons{pr.at(x, 0n), X.SxCons{pr.at(x, 1n), X.SxCons{pr.cut.named(pr.at(x, 2n), pr.gk(pr.at(x, 1n)), d), X.tsx.args(X.tsx.args(X.tsx.args(x)))}}}

# a spine's head's drops, the spine cut
def pr.cut.spine(r: X.Sx & Nat, +x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  match r:
    case Tuple{+h, +k}:
      +g = pr.if(X.Sx, pr.head.is(h, "self"), _ => pr.at(h, 1n), _ => h)
      pr.if(X.Sx, Bool.and(pr.gkind.is(g, "con"), Nat.is_lt(0n, k)), _ => pr.cut(1000000n, x, Nat.sub(k, 1n), pr.gk(g), 35, d), _ => pr.if(X.Sx, Bool.and(pr.gkind.is(g, "var"), Nat.is_lt(0n, k)), _ => pr.cut(1000000n, x, Nat.sub(k, 1n), pr.gk(g), 37, d), _ => x))

# (fun NAME T SPAN (matches ARGTYS RES ORIGIN (MATCH...)) ..): a def whose
# parameters drop, without them (its patterns, its type's arrows)
def pr.cut.match(+m: X.Sx, +k: List<&2, U32>, +d: Map<&2, Bool>) -> X.Sx:
  X.SxCons{pr.at(m, 0n), X.SxCons{pr.cut.els(pr.at(m, 1n), 0n, k, 37, d), X.tsx.args(X.tsx.args(m))}}

def pr.cut.ms(xs: X.Sx, +k: List<&2, U32>, +d: Map<&2, Bool>) -> X.Sx:
  match xs:
    case X.SxCons{+h, +t}:
      X.SxCons{pr.cut.match(h, k, d), pr.cut.ms(t, k, d)}
    case _:
      X.SxNil{}

def pr.cut.matches(+ms: X.Sx, +k: List<&2, U32>, +d: Map<&2, Bool>) -> X.Sx:
  pr.l([pr.at(ms, 0n), pr.cut.els(pr.at(ms, 1n), 0n, k, 37, d), pr.at(ms, 2n), pr.at(ms, 3n), pr.cut.ms(pr.at(ms, 4n), k, d)])

def pr.cut.fun(+x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  +n = pr.at(x, 1n)
  +g = pr.if(X.Sx, pr.head.is(n, "self"), _ => pr.at(n, 1n), _ => n)
  pr.if(X.Sx, pr.gkind.is(g, "var"), _ => X.SxCons{pr.at(x, 0n), X.SxCons{n, X.SxCons{pr.cut.ty(1000000n, pr.at(x, 2n), 0n, pr.gk(g), d), X.SxCons{pr.at(x, 3n), X.SxCons{pr.cut.matches(pr.at(x, 4n), pr.gk(g), d), X.tsx.args(X.tsx.args(X.tsx.args(X.tsx.args(X.tsx.args(x)))))}}}}}, _ => x)

def pr.cut.export(+x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  +g = pr.at(x, 1n)
  pr.if(X.Sx, pr.gkind.is(g, "var"), _ => pr.l([pr.at(x, 0n), g, pr.cut.ty(1000000n, pr.at(x, 2n), 0n, pr.gk(g), d)]), _ => x)

# Local bindings: a group (nonrec BIND) or (rec BIND...) of a where or a
# let that nothing in its scope (the right-hand sides, the let's body, the
# other groups) names is left out, as GHC never builds it; a strict one
# (a bang pattern) stays.

# a group's names
def pr.grp.names(+m: List<&2, U32>, bs: X.Sx) -> List<&2, List<&2, U32>>:
  match bs:
    case X.SxCons{+b, +t}:
      List.append(&2, List<&2, U32>, pr.keys(m, pr.l([pr.a("top"), b])), pr.grp.names(m, t))
    case _:
      Nil{}

# whether a group binds with a bang: (patbind (pbang ..) ..)
def pr.grp.strict(bs: X.Sx) -> Bool:
  match bs:
    case X.SxCons{+b, +t}:
      Bool.or(Bool.and(pr.head.is(b, "patbind"), pr.head.is(pr.at(b, 1n), "pbang")), pr.grp.strict(t))
    case _:
      False{}

# the names the groups refer to, but group skip's
def pr.lb.refs(gs: X.Sx, +m: List<&2, U32>, +skip: Nat, +i: Nat, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match gs:
    case X.SxCons{+g, +t}:
      pr.lb.refs(t, m, skip, 1n+i, pr.if(List<&2, List<&2, U32>>, Nat.is_eq(i, skip), _ => acc, _ => pr.refs(pr.fuel(), m, g, True{}, acc)))
    case _:
      acc

# the groups kept: all is the whole list, body the scope's own names
def pr.lb.keep(gs: X.Sx, +m: List<&2, U32>, +all: X.Sx, +i: Nat, +body: List<&2, List<&2, U32>>) -> X.Sx:
  match gs:
    case X.SxCons{+g, +t}:
      +used = pr.any(pr.grp.names(m, X.tsx.args(g)), pr.sets(Map.new(&2, Bool), pr.lb.refs(all, m, i, 0n, body)))
      +keep = Bool.or(Bool.or(used, pr.grp.strict(X.tsx.args(g))), List.is_empty(&2, List<&2, U32>, pr.grp.names(m, X.tsx.args(g))))
      pr.if(X.Sx, keep, _ => X.SxCons{g, pr.lb.keep(t, m, all, 1n+i, body)}, _ => pr.lb.keep(t, m, all, 1n+i, body))
    case _:
      X.SxNil{}

# (binds G...) with its unused groups left out, body the scope's names
def pr.lb(+m: List<&2, U32>, +lb: X.Sx, +body: List<&2, List<&2, U32>>) -> X.Sx:
  pr.if(X.Sx, pr.head.is(lb, "binds"), _ => X.SxCons{pr.at(lb, 0n), pr.lb.keep(X.tsx.args(lb), m, X.tsx.args(lb), 0n, body)}, _ => lb)

# (grhss (GRHS...) LOCALBINDS)
def pr.lb.grhss(+m: List<&2, U32>, +y: X.Sx) -> X.Sx:
  pr.l([pr.at(y, 0n), pr.at(y, 1n), pr.lb(m, pr.at(y, 2n), pr.refs(pr.fuel(), m, pr.at(y, 1n), True{}, Nil{}))])

# (let LOCALBINDS E): E alone when no group is left
def pr.lb.let(+m: List<&2, U32>, +y: X.Sx) -> X.Sx:
  +lb = pr.lb(m, pr.at(y, 1n), pr.refs(pr.fuel(), m, pr.at(y, 2n), True{}, Nil{}))
  pr.if(X.Sx, Nat.is_eq(X.tsx.len(lb), 1n), _ => pr.at(y, 2n), _ => pr.l([pr.at(y, 0n), lb, pr.at(y, 2n)]))

# a tree with the drops made: node and sp as pr.mk's
def pr.rw(fuel: Nat, +m: List<&2, U32>, +x: X.Sx, +node: Bool, +sp: Bool, +d: Map<&2, Bool>) -> X.Sx:
  match fuel:
    case 0n:
      x
    case 1n+(+p):
      match x:
        case X.SxCons{+h, +t}:
          +hd = X.tsx.atom.of(h)
          pr.if(X.Sx, Bool.not(node), _ => X.SxCons{pr.rw(p, m, h, True{}, False{}, d), pr.rw(p, m, t, False{}, False{}, d)}, _ => pr.if(X.Sx, pr.is.spine(hd), _ => pr.if(X.Sx, sp, _ => pr.if(X.Sx, pr.is(hd, "tyapp"), _ => pr.l([h, pr.rw(p, m, pr.at(x, 1n), True{}, True{}, d), pr.at(x, 2n)]), _ => pr.l([h, pr.rw(p, m, pr.at(x, 1n), True{}, True{}, d), pr.rw(p, m, pr.at(x, 2n), True{}, False{}, d)])), _ => pr.rw(p, m, pr.cut.spine(pr.spine(1000000n, x, 0n), x, d), True{}, True{}, d)), _ => pr.if(X.Sx, Bool.or(Bool.or(pr.is(hd, "g"), pr.is(hd, "l")), Bool.or(pr.is(hd, "tc"), pr.is(hd, "self"))), _ => x, _ => pr.if(X.Sx, pr.is(hd, "pcon"), _ => X.SxCons{h, pr.rw(p, m, X.tsx.args(pr.cut.pcon(x, d)), False{}, False{}, d)}, _ => pr.if(X.Sx, pr.is(hd, "reccon"), _ => X.SxCons{h, pr.rw(p, m, X.tsx.args(pr.cut.reccon(x, d)), False{}, False{}, d)}, _ => pr.if(X.Sx, pr.is(hd, "fun"), _ => X.SxCons{h, pr.rw(p, m, X.tsx.args(pr.cut.fun(x, d)), False{}, False{}, d)}, _ => pr.if(X.Sx, pr.is(hd, "export"), _ => pr.cut.export(x, d), _ => pr.if(X.Sx, pr.is(hd, "grhss"), _ => pr.lb.grhss(m, X.SxCons{h, pr.rw(p, m, t, False{}, False{}, d)}), _ => pr.if(X.Sx, pr.is(hd, "let"), _ => pr.lb.let(m, X.SxCons{h, pr.rw(p, m, t, False{}, False{}, d)}), _ => X.SxCons{pr.rw(p, m, h, True{}, False{}, d), pr.rw(p, m, t, False{}, False{}, d)})))))))))
        case _:
          x

# (data NAME TVS ((con NAME (FIELD...) (ARGTYPE...) EX)...) SPAN) without
# its dropped fields
def pr.rw.con(+m: List<&2, U32>, +c: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  +k = pr.cat(m, 46 <> pr.sat(c, 1n))
  pr.l([pr.at(c, 0n), pr.at(c, 1n), pr.cut.els(pr.at(c, 2n), 0n, k, 35, d), pr.cut.els(pr.at(c, 3n), 0n, k, 35, d), pr.at(c, 4n)])

def pr.rw.cons(+m: List<&2, U32>, cs: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  match cs:
    case X.SxCons{+c, t}:
      X.SxCons{pr.rw.con(m, c, d), pr.rw.cons(m, t, d)}
    case _:
      X.SxNil{}

def pr.rw.form(+m: List<&2, U32>, +x: X.Sx, +d: Map<&2, Bool>) -> X.Sx:
  pr.if(X.Sx, pr.head.is(x, "data"), _ => pr.l([pr.at(x, 0n), pr.at(x, 1n), pr.at(x, 2n), pr.rw.cons(m, pr.at(x, 3n), d), pr.at(x, 4n)]), _ => pr.if(X.Sx, Bool.or(pr.head.is(x, "top"), pr.head.is(x, "top-evbinds")), _ => pr.rw(pr.fuel(), m, x, True{}, False{}, d), _ => x))

def pr.rw.forms(+m: List<&2, U32>, xs: List<&2, X.Sx>, +d: Map<&2, Bool>) -> List<&2, X.Sx>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      pr.rw.form(m, x, d) <> pr.rw.forms(m, t, d)

def pr.rw.mds(ds: List<&2, Md>, +d: Map<&2, Bool>) -> List<&2, Md>:
  match ds:
    case Nil{}:
      Nil{}
    case Md{+n, f, xs} <> t:
      Md{n, f, pr.rw.forms(n, xs, d)} <> pr.rw.mds(t, d)

# Rounds --------------------------------------------------------------------

def pr.show.marks(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      pr.cat(32 <> x, pr.show.marks(t))

# a round: the bindings reached, then the fields and parameters dropped;
# its report line, and the package
def pr.round(+ds: List<&2, Md>, +roots: List<&2, List<&2, U32>>, +rmap: Map<&2, Bool>, +keep: Map<&2, Bool>) -> List<&2, U32> & List<&2, Md>:
  +ix = pr.idx(ds, Map.new(&2, List<&2, List<&2, U32>>))
  +seen = pr.reach(pr.fuel(), (roots, Map.new(&2, Bool)), ix)
  +kept = pr.keep(ds, seen)
  +dts = pr.dts(kept)
  +cns = pr.cns(dts)
  +ar = pr.ar.put(cns, Map.new(&2, Nat))
  +rd = pr.sets(Map.new(&2, Bool), pr.tymarks(dts, keep, pr.mk.mds(kept, ar, Nil{})))
  +fd = pr.drops(cns, rd, Nil{})
  +mins = pr.oc.min(pr.oc.mds(kept, Nil{}), Map.new(&2, Nat))
  +pd = pr.pd(pr.pu.mds(kept, Nil{}), mins, rmap, Nil{})
  +d = pr.sets(Map.new(&2, Bool), List.append(&2, List<&2, U32>, fd, pd))
  +rep = pr.cat(S.b("forms " ++ Nat.show(pr.count(kept)) ++ " fields"), pr.cat(pr.show.marks(fd), pr.cat(S.b(" params"), pr.show.marks(pd))))
  (rep, pr.rw.mds(kept, d))

# a round that dropped no field and no parameter
def pr.is.quiet(+rep: List<&2, U32>) -> Bool:
  S.suffix(rep, S.b(" fields params"))

# rounds until one drops nothing: r, the last round's report and package
def pr.rounds(fuel: Nat, r: List<&2, U32> & List<&2, Md>, +roots: List<&2, List<&2, U32>>, +rmap: Map<&2, Bool>, +keep: Map<&2, Bool>, +last: Nat) -> IO(List<&2, Md>):
  match fuel:
    case 0n:
      match r:
        case Tuple{rep, ds}:
          IO.pure(List<&2, Md>, ds)
    case 1n+(+p):
      match r:
        case Tuple{+rep, +ds}:
          +n = pr.count(ds)
          do IO<List<&2, Md>>:
            IO.print(S.str(rep))
            pr.if(IO(List<&2, Md>), Bool.and(Nat.is_eq(n, last), pr.is.quiet(rep)), _ => IO.pure(List<&2, Md>, ds), _ => pr.rounds(p, pr.round(ds, roots, rmap, keep), roots, rmap, keep, n))

# I/O -----------------------------------------------------------------------

def pr.text(xs: List<&2, X.Sx>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      pr.cat(X.tsx.show(x), 10 <> pr.text(t))

def pr.read(fs: List<String>) -> IO(List<&2, Md>):
  match fs:
    case Nil{}:
      IO.pure(List<&2, Md>, Nil{})
    case +f <> t:
      do IO<List<&2, Md>>:
        bytes : List<&2, U32> <- S.read(f)
        +xs : List<&2, X.Sx> <- IO.pure(List<&2, X.Sx>, X.tsx.read(bytes))
        rest : List<&2, Md> <- pr.read(t)
        IO.pure(List<&2, Md>, Md{pr.modname(xs), f, xs} <> rest)

def pr.write(+out: String, ds: List<&2, Md>, list: List<&2, U32>) -> IO(Unit):
  match ds:
    case Nil{}:
      S.write(out ++ "/modules.txt", list)
    case Md{n, f, xs} <> t:
      +p = out ++ "/" ++ S.base(f)
      do IO<Unit>:
        S.write(p, pr.text(xs))
        pr.write(out, t, pr.cat(list, pr.cat(S.b(p), [10])))

# ROOTS's lines: names, and `type M.T` lines
def pr.roots.names(ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +t:
      pr.if(List<&2, List<&2, U32>>, Bool.or(Bool.or(List.is_empty(&2, U32, l), S.prefix(l, S.b("#"))), S.prefix(l, S.b("type "))), _ => pr.roots.names(t), _ => l <> pr.roots.names(t))

def pr.roots.types(ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +t:
      pr.if(List<&2, List<&2, U32>>, S.prefix(l, S.b("type ")), _ => List.drop(&2, U32, l, 5n) <> pr.roots.types(t), _ => pr.roots.types(t))

def pr.main(args: List<String>) -> IO(Unit):
  match args:
    case r <> +out <> files:
      do IO<Unit>:
        rb : List<&2, U32> <- S.read(r)
        +ls : List<&2, List<&2, U32>> <- IO.pure(List<&2, List<&2, U32>>, S.split.lines(rb))
        +roots : List<&2, List<&2, U32>> <- IO.pure(List<&2, List<&2, U32>>, pr.roots.names(ls))
        ds : List<&2, Md> <- pr.read(files)
        S.mkdir(out)
        +rmap : Map<&2, Bool> <- IO.pure(Map<&2, Bool>, pr.sets(Map.new(&2, Bool), roots))
        +keep : Map<&2, Bool> <- IO.pure(Map<&2, Bool>, pr.sets(Map.new(&2, Bool), pr.roots.types(ls)))
        ds2 : List<&2, Md> <- pr.rounds(12n, pr.round(ds, roots, rmap, keep), roots, rmap, keep, 0n)
        pr.write(out, ds2, Nil{})
    case _:
      IO.print("usage: prune ROOTS OUTDIR FILE.sexp...")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    pr.main(List.tail(&1, String, argv))
