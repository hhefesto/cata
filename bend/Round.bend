import Base
import ./a2b/Sys.bend as S
import ./Adj.bend as A

# Round: the other half of the round trip, F(G(b)) against b (PLAN.md,
# "cata as a functor", flavour 3).  b is cata's Bend of a Haskell module h
# (a law run's OUT/NAME.bend), G(b) bend/Back.bend's Haskell of it
# (OUT/hs/NAME.hs), and F(G(b)) cata's Bend of that again (law on G(b) and
# BendRt.hs as a package: tests/back/round.zsh).  For each def of b (its
# laws aside) Round says:
#
#   same     F(G(b)) has it and its text is b's, up to the normalisation;
#   differ   F(G(b)) has it and its text is not b's (its laws are b's to
#            check: Round writes them into a copy of F(G(b)), see below);
#   missing  F(G(b)) has no such def: the ledger's reason.
#
# The normalisation, all of it: (1) a def's name: G writes b's def n as
# c' and n with its dots as primes, F writes a prime as _q, so F(G(b))'s
# c_qN (N: n's dots as _q) is read as n, wherever it occurs; (2) a def's
# parameters (its type parameters too: G writes no signatures, so GHC
# names them again) are renamed by their position, in both; (3) only the
# def's own lines (its header and its body) are compared, its comments
# not.  Nothing else: a local cata invents (x_1, eta_0, pt_0) is compared
# as it is.
#
#   round B GHS FGB LEDGER OUT: B b's file, GHS G(b)'s, FGB F(G(b))'s,
#   LEDGER its ledger; prints one line per def of b (NAME, its status, the
#   ledger's reason when missing), and writes OUT/NAME.txt with each
#   differing def's two normalised texts, and, for the differing defs that
#   have laws in b, FGB's directory's round_K.bend: F(G(b))'s file with
#   the def's laws from b (their names as F(G(b))'s), one file per def,
#   for tests/back/round.zsh to check.
#
# Every def is prefixed `rd.`.

def rd.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

# n as F(G(b)) names it: c_q, and n's dots as _q
def rd.fgname(+n: List<&2, U32>) -> List<&2, U32>:
  rd.cat(S.b("c_q"), S.replace(n, S.b("."), S.b("_q")))

# Defs ----------------------------------------------------------------------------

# a def of a file: its name and its lines (its header first)
type Df is Data:
  Df{n: List<&2, U32>, ls: List<&2, List<&2, U32>>}

def rd.isdef(+l: List<&2, U32>) -> Bool:
  S.prefix(l, S.b("def "))

def rd.isbody(+l: List<&2, U32>) -> Bool:
  S.prefix(l, S.b("  "))

def rd.hd(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case h <> t:
      h
    case Nil{}:
      Nil{}

def rd.close(in: Bool, +cur: List<&2, List<&2, U32>>, rest: List<&2, Df>) -> List<&2, Df>:
  match in:
    case True{}:
      +r = List.reverse(&2, List<&2, U32>, cur)
      Df{A.aj.dname(rd.hd(r)), r} <> rest
    case False{}:
      rest

# the file's defs: a block is a def line and the indented lines after it
# (in: inside a block; cur: its lines so far, reversed).  A def line closes
# the block before it and opens its own; an indented line inside a block
# goes on with it; any other line closes it.
def rd.blocks(ls: List<&2, List<&2, U32>>, +in: Bool, +cur: List<&2, List<&2, U32>>) -> List<&2, Df>:
  match ls:
    case Nil{}:
      rd.close(in, cur, Nil{})
    case +l <> t:
      +isd = rd.isdef(l)
      +go = Bool.and(in, rd.isbody(l))
      +in2 = Bool.or(isd, go)
      +cur2 = Bool.pick(List<&2, List<&2, U32>>, isd, [l], Bool.pick(List<&2, List<&2, U32>>, go, l <> cur, Nil{}))
      rd.close(Bool.and(in, Bool.not(go)), cur, rd.blocks(t, in2, cur2))

# a law: its type an equation (def f.exK() -> {..})
def rd.islaw(+d: Df) -> Bool:
  match d:
    case Df{n, ls}:
      S.infix(rd.hd(ls), S.b(") -> {"))

def rd.find(ds: List<&2, Df>, +n: List<&2, U32>) -> Maybe<&2, Df>:
  match ds:
    case Nil{}:
      None{}
    case Df{+k, ls} <> t:
      Bool.pick(Maybe<&2, Df>, S.eq(k, n), Some{Df{k, ls}}, rd.find(t, n))

# G(b)'s defs (lines c'NAME ...; not an alias, h's name = b'up ..: h's own
# names may start c'): b's names, each c'NAME's primes as dots
def rd.gnames(ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      +r = rd.gnames(t)
      Bool.pick(List<&2, List<&2, U32>>, Bool.and(S.prefix(l, S.b("c'")), Bool.not(S.infix(l, S.b(" = b'up ")))), S.replace(S.until(List.drop(&2, U32, l, 2n), 32), [39], [46]) <> r, r)

# Parameters ----------------------------------------------------------------------

# a header's parameters, from just after its name's (: split at the commas
# at depth 0, where (, [, { and < open and ), ], } and > close (not the >
# of ->); stop at the ) that closes them
def rd.dep(+d: Nat, +p: U32, +c: U32) -> Nat:
  +open = Bool.or(Bool.or(U32.is_eq(c, 40), U32.is_eq(c, 91)), Bool.or(U32.is_eq(c, 123), U32.is_eq(c, 60)))
  +shut = Bool.or(Bool.or(U32.is_eq(c, 41), U32.is_eq(c, 93)), Bool.or(U32.is_eq(c, 125), Bool.and(U32.is_eq(c, 62), U32.is_ne(p, 45))))
  Bool.pick(Nat, open, 1n+d, Bool.pick(Nat, shut, Nat.sub(d, 1n), d))

# (k: what the byte is at depth d: the closing ), a comma, another; at the
# end of the text, the end)
type Rk is Data:
  RkEnd{}
  RkSep{}
  RkByte{}

def rd.rk(+d: Nat, +c: U32) -> Rk:
  Bool.pick(Rk, Bool.and(Nat.is_eq(d, 0n), U32.is_eq(c, 41)), RkEnd{}, Bool.pick(Rk, Bool.and(Nat.is_eq(d, 0n), U32.is_eq(c, 44)), RkSep{}, RkByte{}))

def rd.rk.n(+d: Nat, +xs: List<&2, U32>) -> Rk:
  match xs:
    case Nil{}:
      RkEnd{}
    case +c <> t:
      rd.rk(d, c)

# (p: the byte before; k: the next byte's kind)
def rd.ps.go(xs: List<&2, U32>, k: Rk, +d: Nat, +p: U32, +cur: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs k:
    case Nil{} _:
      [List.reverse(&2, U32, cur)]
    case _ RkEnd{}:
      [List.reverse(&2, U32, cur)]
    case +c <> +t RkSep{}:
      List.reverse(&2, U32, cur) <> rd.ps.go(t, rd.rk.n(d, t), d, c, Nil{})
    case +c <> +t RkByte{}:
      +d2 = rd.dep(d, p, c)
      rd.ps.go(t, rd.rk.n(d2, t), d2, c, c <> cur)

# a parameter's name: its mark (- ~ +) dropped, up to its :
def rd.pname(+x: List<&2, U32>) -> List<&2, U32>:
  +y = A.aj.trim(x)
  +z = Bool.pick(List<&2, U32>, Bool.or(S.head.is(y, 45), Bool.or(S.head.is(y, 126), S.head.is(y, 43))), List.drop(&2, U32, y, 1n), y)
  A.aj.trim(S.until(z, 58))

def rd.pnames(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      +n = rd.pname(x)
      +r = rd.pnames(t)
      Bool.pick(List<&2, List<&2, U32>>, List.is_empty(&2, U32, n), r, n <> r)

def rd.ps.from(+xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  rd.ps.go(xs, rd.rk.n(0n, xs), 0n, 0, Nil{})

# a def's parameters' names
def rd.params(+d: Df) -> List<&2, List<&2, U32>>:
  match d:
    case Df{n, ls}:
      rd.pnames(rd.ps.from(A.aj.after(rd.hd(ls), rd.cat(S.b("def "), rd.cat(n, [40])))))

# each parameter renamed by its position (p'1, p'2, ..), before vs
def rd.pos(xs: List<&2, List<&2, U32>>, +i: Nat, vs: List<&2, A.Av>) -> List<&2, A.Av>:
  match xs:
    case Nil{}:
      vs
    case x <> t:
      A.Av{x, rd.cat(S.b("p'"), S.b(Nat.show(i)))} <> rd.pos(t, 1n+i, vs)

# each name once, in its first place (G writes a def's signature and
# each of its equations on lines of their own)
def rd.uniq(xs: List<&2, List<&2, U32>>, +seen: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      +hit = S.mem(x, seen)
      +rest = rd.uniq(t, x <> seen)
      Bool.pick(List<&2, List<&2, U32>>, hit, rest, x <> rest)

# F(G(b))'s names of b's defs read as b's
def rd.names(ns: List<&2, List<&2, U32>>) -> List<&2, A.Av>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> t:
      A.Av{rd.fgname(n), n} <> rd.names(t)

# a def's lines normalised: its parameters by position, then names by vs
def rd.norm(+d: Df, +vs: List<&2, A.Av>) -> List<&2, U32>:
  match d:
    case Df{n, +ls}:
      A.aj.tx(S.join(ls, 10), A.AeSub{rd.pos(rd.params(Df{n, ls}), 1n, vs), Nil{}})

# Laws ------------------------------------------------------------------------------

def rd.flip(vs: List<&2, A.Av>) -> List<&2, A.Av>:
  match vs:
    case Nil{}:
      Nil{}
    case A.Av{k, v} <> t:
      A.Av{v, k} <> rd.flip(t)

# in a law: its own name as F(G(b))'s def's law, the other names as vs
def rd.lawnames(+vs: List<&2, A.Av>, +k: List<&2, U32>, +n: List<&2, U32>) -> List<&2, A.Av>:
  A.Av{k, rd.cat(rd.fgname(n), rd.cat(S.b(".round."), A.aj.after(k, rd.cat(n, S.b(".")))))} <> rd.flip(vs)

# A law's call of F(G(b))'s def with each argument marked as that def's
# parameter is: ~ (a template) or not.  b and F(G(b)) may differ there
# without differing in meaning (a template type parameter is one Bend
# inlines at compile time: b's partial def calls HsList.error(~A, ..), which
# makes its A a template, where F(G(b)) has BendRt's error folded to
# Inl{msg} and A erased), and b's law, written for b's, would not parse at
# F(G(b))'s.  fl: the def's parameters, whether each is a template.  Only
# where the call has as many arguments as the def parameters (not a
# curried one, f()(x), whose groups A.aj.call reads as one).
def rd.tpls(xs: List<&2, List<&2, U32>>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      S.head.is(A.aj.trim(x), 126) <> rd.tpls(t)

def rd.flags(+d: Df) -> List<&2, Bool>:
  match d:
    case Df{n, ls}:
      rd.tpls(rd.ps.from(A.aj.after(rd.hd(ls), rd.cat(S.b("def "), rd.cat(n, [40])))))

def rd.mark1(+t: Bool, +a: List<&2, U32>) -> List<&2, U32>:
  +b = Bool.pick(List<&2, U32>, S.head.is(a, 126), List.drop(&2, U32, a, 1n), a)
  Bool.pick(List<&2, U32>, t, 126 <> b, b)

def rd.mark(as: List<&2, List<&2, U32>>, fl: List<&2, Bool>) -> List<&2, List<&2, U32>>:
  match as fl:
    case +a <> t +f <> u:
      rd.mark1(f, a) <> rd.mark(t, u)
    case xs _:
      xs

def rd.joinc(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> Nil{}:
      x
    case x <> t:
      rd.cat(x, rd.cat(S.b(", "), rd.joinc(t)))

def rd.remark.call(m: Maybe<&2, A.Ap>, +pre: List<&2, U32>, +fl: List<&2, Bool>, +d: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{A.Ap{+as, +rest}}:
      +xs = A.aj.args(as)
      +ok = Nat.is_eq(List.length(&2, List<&2, U32>, xs), List.length(&2, Bool, fl))
      Bool.pick(List<&2, U32>, ok, rd.cat(pre, rd.cat(rd.joinc(rd.mark(xs, fl)), rd.cat([41], rest))), d)
    case None{}:
      d

def rd.remark.at(m: Maybe<&2, Nat>, +x: List<&2, U32>, +p: List<&2, U32>, +fl: List<&2, Bool>) -> List<&2, U32>:
  match m:
    case Some{+i}:
      +k = Nat.add(i, List.length(&2, U32, p))
      rd.remark.call(A.aj.call(List.drop(&2, U32, x, k)), List.take(&2, U32, x, k), fl, x)
    case None{}:
      x

# the law's first call of F(G(b))'s def (its equation's left side)
def rd.remark(+x: List<&2, U32>, +f: List<&2, U32>, +fl: List<&2, Bool>) -> List<&2, U32>:
  +p = rd.cat(S.b("{"), rd.cat(f, [40]))
  rd.remark.at(S.find(x, p, 0n), x, p, fl)

# b's laws of def n (named n.exK), each a def block, its names as F(G(b))'s
def rd.laws(ds: List<&2, Df>, +n: List<&2, U32>, +vs: List<&2, A.Av>, +fl: List<&2, Bool>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Df{+k, +ls} <> t:
      +mine = Bool.and(rd.islaw(Df{k, ls}), S.prefix(k, rd.cat(n, S.b(".ex"))))
      +r = rd.laws(t, n, vs, fl)
      Bool.pick(List<&2, U32>, mine, rd.cat(rd.remark(A.aj.tx(S.join(ls, 10), A.AeSub{rd.lawnames(vs, k, n), Nil{}}), rd.fgname(n), fl), rd.cat([10, 10], r)), r)

def rd.haslaws(ds: List<&2, Df>, +n: List<&2, U32>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Df{+k, +ls} <> t:
      Bool.or(Bool.and(rd.islaw(Df{k, ls}), S.prefix(k, rd.cat(n, S.b(".ex")))), rd.haslaws(t, n))

# The ledger ------------------------------------------------------------------------

# F(G(b))'s ledger line of def k: its status and reason
def rd.ledger(ls: List<&2, List<&2, U32>>, +k: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      S.b("not in the ledger")
    case +l <> t:
      +fs = S.split(l, 9)
      +hit = Bool.and(S.eq(rd.hd(List.drop(&2, List<&2, U32>, fs, 1n)), k), Bool.not(S.infix(rd.hd(fs), S.b("BendRt"))))
      Bool.pick(List<&2, U32>, hit, S.join(List.drop(&2, List<&2, U32>, fs, 2n), 32), rd.ledger(t, k))

# Comparing -------------------------------------------------------------------------

# what a difference is, read off the two normalised texts: the type (the
# headers differ), a BendRt name F did not take back (F(G(b)) still calls
# BendRt.N), a def F lifted out (F(G(b)) calls one of its own N.lK that b
# has not), or the body
def rd.why(+x: List<&2, U32>, +y: List<&2, U32>) -> List<&2, U32>:
  +hx = rd.hd(S.split(x, 10))
  +hy = rd.hd(S.split(y, 10))
  +rt = S.infix(y, S.b("BendRt."))
  +lift = Bool.and(S.infix(y, S.b(".l1(")), Bool.not(S.infix(x, S.b(".l1("))))
  Bool.pick(List<&2, U32>, Bool.not(S.eq(hx, hy)), S.b("type"), Bool.pick(List<&2, U32>, rt, S.b("bendrt"), Bool.pick(List<&2, U32>, lift, S.b("lifted"), S.b("body"))))

# one def of b: its line; the texts and the laws' file when it differs
type Rr is Data:
  Rr{line: List<&2, U32>, diff: List<&2, U32>, laws: List<&2, U32>}

def rd.one(+n: List<&2, U32>, +bd: Df, m: Maybe<&2, Df>, +vs: List<&2, A.Av>, +bds: List<&2, Df>, +led: List<&2, List<&2, U32>>) -> Rr:
  match m:
    case None{}:
      Rr{rd.cat(n, rd.cat(S.b("\tmissing\t"), rd.ledger(led, rd.fgname(n)))), Nil{}, Nil{}}
    case Some{+fd}:
      +x = rd.norm(bd, Nil{})
      +y = rd.norm(fd, vs)
      +same = S.eq(x, y)
      +hl = rd.haslaws(bds, n)
      Rr{rd.cat(n, Bool.pick(List<&2, U32>, same, S.b("\tsame\t"), rd.cat(Bool.pick(List<&2, U32>, hl, S.b("\tdiffer\tlaws\t"), S.b("\tdiffer\tno-laws\t")), rd.why(x, y)))), Bool.pick(List<&2, U32>, same, Nil{}, rd.cat(S.b("== b: "), rd.cat(n, rd.cat([10], rd.cat(x, rd.cat(S.b("\n== F(G(b)):\n"), rd.cat(y, S.b("\n\n")))))))), Bool.pick(List<&2, U32>, Bool.and(Bool.not(same), hl), rd.laws(bds, n, vs, rd.flags(fd)), Nil{})}

def rd.got(+n: List<&2, U32>, m: Maybe<&2, Df>, +bds: List<&2, Df>, +fds: List<&2, Df>, +vs: List<&2, A.Av>, +led: List<&2, List<&2, U32>>) -> Rr:
  match m:
    case Some{+bd}:
      rd.one(n, bd, rd.find(fds, rd.fgname(n)), vs, bds, led)
    case None{}:
      Rr{rd.cat(n, S.b("\tnot-in-b\t")), Nil{}, Nil{}}

def rd.all(ns: List<&2, List<&2, U32>>, +bds: List<&2, Df>, +fds: List<&2, Df>, +vs: List<&2, A.Av>, +led: List<&2, List<&2, U32>>) -> List<&2, Rr>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> t:
      rd.got(n, rd.find(bds, n), bds, fds, vs, led) <> rd.all(t, bds, fds, vs, led)

def rd.lines(rs: List<&2, Rr>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Rr{l, d, w} <> t:
      rd.cat(l, 10 <> rd.lines(t))

def rd.diffs(rs: List<&2, Rr>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Rr{l, d, w} <> t:
      rd.cat(d, rd.diffs(t))

# the laws' files: F(G(b))'s text with one def's laws, round_K.bend
def rd.write.one(none: Bool, +dir: String, +ftext: List<&2, U32>, +k: Nat, +w: List<&2, U32>) -> IO(Nat):
  match none:
    case True{}:
      IO.pure(Nat, k)
    case False{}:
      do IO<Nat>:
        S.write(dir ++ "/round_" ++ Nat.show(k) ++ ".bend", rd.cat(ftext, rd.cat(S.b("\n# Round (bend/Round.bend): b's laws of the def\n"), w)))
        return 1n+k

def rd.write(rs: List<&2, Rr>, +dir: String, +ftext: List<&2, U32>, +k: Nat) -> IO(Nat):
  match rs:
    case Nil{}:
      IO.pure(Nat, k)
    case Rr{l, d, +w} <> t:
      do IO<Nat>:
        k2 : Nat <- rd.write.one(List.is_empty(&2, U32, w), dir, ftext, k, w)
        rd.write(t, dir, ftext, k2)

def rd.go(+out: String, +name: String, +fdir: String, btext: List<&2, U32>, gtext: List<&2, U32>, +ftext: List<&2, U32>, ltext: List<&2, U32>) -> IO(Unit):
  +bds = rd.blocks(S.split(btext, 10), False{}, Nil{})
  +fds = rd.blocks(S.split(ftext, 10), False{}, Nil{})
  +ns = rd.uniq(rd.gnames(S.split(gtext, 10)), Nil{})
  +vs = rd.names(ns)
  +rs = rd.all(ns, bds, fds, vs, S.split(ltext, 10))
  do IO<Unit>:
    S.write(out ++ "/" ++ name ++ ".txt", rd.diffs(rs))
    k : Nat <- rd.write(rs, fdir, ftext, 0n)
    IO.print(S.str(rd.lines(rs)) ++ "laws-files\t" ++ Nat.show(k))

def rd.main(+b: String, +g: String, +f: String, +l: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    bt : List<&2, U32> <- S.read(b)
    gt : List<&2, U32> <- S.read(g)
    ft : List<&2, U32> <- S.read(f)
    lt : List<&2, U32> <- S.read(l)
    rd.go(out, S.str(S.until(S.b(S.base(b)), 46)), S.parent(f), bt, gt, ft, lt)

def rd.argv(args: List<String>) -> IO(Unit):
  match args:
    case b <> g <> f <> l <> o <> t:
      rd.main(b, g, f, l, o)
    case _:
      IO.print("usage: round B.bend G.hs FGB.bend LEDGER OUTDIR")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    rd.argv(List.drop(&1, String, argv, 1n))
