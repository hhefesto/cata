import Base
import ./a2b/Sys.bend as S

# Adj: whether a hand-written Bend function b implements a Haskell function
# h, checked on the side where it is easy (PLAN.md, "cata as a functor",
# flavour 4).  The pairing is a square, a law the human writes in a
# PROPOSED.bend (tests/square), phi taking cata's types to b's:
#
#   law sq.NAME:
#     for x: ...
#     {phi(F.h(x)) == W.b(phi(x)) : T}
#
# F is cata's Bend of h's module (a law run's OUT/MOD.bend, imported as F).
# For every x, a square is PROOF.bend's to prove (bend --check-only, then
# --verdict: tests/adjoint/run.zsh).  Here, the GHC side: law's run asked
# GHC for h's answers on small inputs, written into F as example laws
# `def h.exK() -> {h(a) == v : R}: {==}`.  Each one gives an instance of
# each square that calls F.h, with GHC's answer in F.h(a)'s place:
#
#   def adj.sq.NAME.exK() -> {phi(v) == W.b(phi(a)) : T}: {==}
#
# so b is checked against GHC's h itself, not against F's translation of
# it.  An instance is checked by bend computing both sides.  Then the
# mutants: two squares of the same shape (their T and their b's arguments
# the same) with their b's swapped; the instances must fail, and how many
# do says how much the examples tell apart.
#
#   adj WORK MOD: WORK holds PROPOSED.bend, PROOF.bend and l/MOD.bend (F)
#   with F's imports; writes WORK/adj.*.bend (the instances), WORK/adj_phi.bend
#   (PROPOSED.bend without its laws, which the instances import: an open law
#   would fail their check) and WORK/mut.X.as.Y/ (a mutant's squares), and
#   prints, by square, what held.  BEND names the bend.  Run it compiled
#   (bend Adj.bend -o adj, as tests/adjoint/run.zsh does): bend's
#   interpreter overflows its stack on it.
#
# Every def is prefixed `aj.`.

# Bytes ---------------------------------------------------------------------------

def aj.cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def aj.cat3(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> List<&2, U32>:
  aj.cat(a, aj.cat(b, c))

def aj.s(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  aj.cat(S.b(s), acc)

def aj.len(+xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def aj.take(xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.take(&2, U32, xs, n)

def aj.drop(xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.drop(&2, U32, xs, n)

def aj.isspace(+c: U32) -> Bool:
  U32.is_eq(c, 32)

# leading spaces dropped
def aj.ltrim.go(xs: List<&2, U32>, sp: Bool) -> List<&2, U32>:
  match xs sp:
    case h <> +t True{}:
      aj.ltrim.go(t, S.head.is(t, 32))
    case ys False{}:
      ys
    case Nil{} _:
      Nil{}

def aj.ltrim(+xs: List<&2, U32>) -> List<&2, U32>:
  aj.ltrim.go(xs, S.head.is(xs, 32))

def aj.trim(+xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, aj.ltrim(List.reverse(&2, U32, aj.ltrim(xs))))

# the text after the first p (none: Nil)
def aj.after.at(m: Maybe<&2, Nat>, xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match m:
    case Some{k}:
      aj.drop(xs, Nat.add(k, n))
    case None{}:
      Nil{}

def aj.after(+xs: List<&2, U32>, +p: List<&2, U32>) -> List<&2, U32>:
  aj.after.at(S.find(xs, p, 0n), xs, aj.len(p))

# Scanning ------------------------------------------------------------------------

# what a byte is to the scan (worked out before the call that takes it,
# then matched: Bool.pick runs both its branches): the end, a name's byte
# (a letter, a digit, _ or .), a quote opening a literal, another byte; in
# a literal (q its quote): a byte, a backslash, the byte after it, the
# closing quote
type Ak is Data:
  AkEnd{}
  AkId{}
  AkOpen{q: U32}
  AkOther{}
  AkLit{q: U32}
  AkEsc{q: U32}
  AkEscd{q: U32}
  AkClose{}

def aj.idc(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90))), Bool.or(Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), Bool.or(U32.is_eq(c, 95), U32.is_eq(c, 46))))

def aj.ak.at(+c: U32) -> Ak:
  Bool.pick(Ak, aj.idc(c), AkId{}, Bool.pick(Ak, Bool.or(U32.is_eq(c, 34), U32.is_eq(c, 39)), AkOpen{c}, AkOther{}))

def aj.ak.n(+xs: List<&2, U32>) -> Ak:
  match xs:
    case Nil{}:
      AkEnd{}
    case +c <> t:
      aj.ak.at(c)

def aj.ak.lat(+q: U32, +c: U32) -> Ak:
  Bool.pick(Ak, U32.is_eq(c, q), AkClose{}, Bool.pick(Ak, U32.is_eq(c, 92), AkEsc{q}, AkLit{q}))

def aj.ak.l(+q: U32, +xs: List<&2, U32>) -> Ak:
  match xs:
    case Nil{}:
      AkEnd{}
    case +c <> t:
      aj.ak.lat(q, c)

# A name's rewrite: F's own types qualified (an example's terms are F's,
# written inside F: Stack.Stack{..} is F.Stack.Stack{..} outside it), or a
# square's variables replaced by an example's arguments and the
# PROPOSED.bend defs it calls (phi) qualified by P
type Av is Data:
  Av{k: List<&2, U32>, v: List<&2, U32>}

type Ae is Data:
  AeOwn{own: List<&2, List<&2, U32>>}
  AeSub{vs: List<&2, Av>, pd: List<&2, List<&2, U32>>}

def aj.look(vs: List<&2, Av>, +k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match vs:
    case Nil{}:
      None{}
    case Av{+a, v} <> t:
      Bool.pick(Maybe<&2, List<&2, U32>>, S.eq(a, k), Some{v}, aj.look(t, k))

def aj.tr.sub(m: Maybe<&2, List<&2, U32>>, +tok: List<&2, U32>, pd: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case Some{v}:
      v
    case None{}:
      Bool.pick(List<&2, U32>, S.mem(tok, pd), aj.cat(S.b("P."), tok), tok)

def aj.tr(+tok: List<&2, U32>, +e: Ae) -> List<&2, U32>:
  match e:
    case AeOwn{own}:
      Bool.pick(List<&2, U32>, S.mem(S.until(tok, 46), own), aj.cat(S.b("F."), tok), tok)
    case AeSub{vs, pd}:
      aj.tr.sub(aj.look(vs, tok), tok, pd)

# xs with each name rewritten (tok: the name so far, reversed), literals
# left as they are
def aj.tk(xs: List<&2, U32>, k: Ak, tok: List<&2, U32>, +e: Ae) -> List<&2, U32>:
  match xs k:
    case Nil{} _:
      aj.tr(List.reverse(&2, U32, tok), e)
    case h <> +t AkId{}:
      aj.tk(t, aj.ak.n(t), h <> tok, e)
    case h <> +t AkOpen{+q}:
      aj.cat(aj.tr(List.reverse(&2, U32, tok), e), h <> aj.tk(t, aj.ak.l(q, t), Nil{}, e))
    case h <> +t AkLit{+q}:
      h <> aj.tk(t, aj.ak.l(q, t), tok, e)
    case h <> +t AkEsc{q}:
      h <> aj.tk(t, AkEscd{q}, tok, e)
    case h <> +t AkEscd{+q}:
      h <> aj.tk(t, aj.ak.l(q, t), tok, e)
    case h <> +t AkClose{}:
      h <> aj.tk(t, aj.ak.n(t), tok, e)
    case h <> +t _:
      aj.cat(aj.tr(List.reverse(&2, U32, tok), e), h <> aj.tk(t, aj.ak.n(t), Nil{}, e))

def aj.tx(+xs: List<&2, U32>, +e: Ae) -> List<&2, U32>:
  aj.tk(xs, aj.ak.n(xs), Nil{}, e)

# a bracket's depth after c: ( { [ open, ) } ] close (< > are not: -> and
# => hold a >)
def aj.dep(+d: Nat, +c: U32) -> Nat:
  Bool.pick(Nat, Bool.or(U32.is_eq(c, 40), Bool.or(U32.is_eq(c, 123), U32.is_eq(c, 91))), 1n+d, Bool.pick(Nat, Bool.or(U32.is_eq(c, 41), Bool.or(U32.is_eq(c, 125), U32.is_eq(c, 93))), Nat.sub(d, 1n), d))

# where a term ends or splits, outside literals and at depth 0: sep, or
# (close) the ) that closes a call, h(a) or h(a)(b), not followed by (
def aj.hit(close: Bool, +sep: List<&2, U32>, +xs: List<&2, U32>) -> Bool:
  match close:
    case True{}:
      Bool.and(S.prefix(xs, S.b(")")), Bool.not(S.prefix(xs, S.b(")("))))
    case False{}:
      S.prefix(xs, sep)

# its position from i
def aj.pos(xs: List<&2, U32>, k: Ak, +close: Bool, +sep: List<&2, U32>, +d: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match xs k:
    case Nil{} _:
      None{}
    case +h <> +t AkOther{}:
      Bool.pick(Maybe<&2, Nat>, Bool.and(Nat.is_eq(d, 0n), aj.hit(close, sep, h <> t)), Some{i}, aj.pos(t, aj.ak.n(t), close, sep, aj.dep(d, h), 1n+i))
    case h <> +t AkId{}:
      aj.pos(t, aj.ak.n(t), close, sep, d, 1n+i)
    case h <> +t AkOpen{+q}:
      aj.pos(t, aj.ak.l(q, t), close, sep, d, 1n+i)
    case h <> +t AkLit{+q}:
      aj.pos(t, aj.ak.l(q, t), close, sep, d, 1n+i)
    case h <> +t AkEsc{q}:
      aj.pos(t, AkEscd{q}, close, sep, d, 1n+i)
    case h <> +t AkEscd{+q}:
      aj.pos(t, aj.ak.l(q, t), close, sep, d, 1n+i)
    case h <> +t AkClose{}:
      aj.pos(t, aj.ak.n(t), close, sep, d, 1n+i)
    case h <> t AkEnd{}:
      None{}

def aj.find(+close: Bool, +sep: List<&2, U32>, +xs: List<&2, U32>) -> Maybe<&2, Nat>:
  aj.pos(xs, aj.ak.n(xs), close, sep, 0n, 0n)

# two parts
type Ap is Data:
  Ap{a: List<&2, U32>, b: List<&2, U32>}

def aj.cut.at(m: Maybe<&2, Nat>, +xs: List<&2, U32>, +n: Nat) -> Maybe<&2, Ap>:
  match m:
    case Some{+k}:
      Some{Ap{aj.take(xs, k), aj.drop(xs, Nat.add(k, n))}}
    case None{}:
      None{}

# before and after the first sep at depth 0
def aj.cut(+sep: List<&2, U32>, +xs: List<&2, U32>) -> Maybe<&2, Ap>:
  aj.cut.at(aj.find(False{}, sep, xs), xs, aj.len(sep))

# a call's arguments, from just after its first (: the text before the )
# that closes it (h(a)(b)'s groups joined, a, b) and the text after
def aj.call.at(m: Maybe<&2, Nat>, +ys: List<&2, U32>, +xs: List<&2, U32>) -> Maybe<&2, Ap>:
  match m:
    case Some{+k}:
      Some{Ap{aj.take(ys, k), aj.drop(xs, 1n+k)}}
    case None{}:
      None{}

# (h(a)(b): its groups are found as one, each )( read as ", ", which keeps
# the positions)
def aj.call(+xs: List<&2, U32>) -> Maybe<&2, Ap>:
  +ys = S.replace(xs, S.b(")("), S.b(", "))
  aj.call.at(aj.find(True{}, Nil{}, ys), ys, xs)

# the arguments split at ", " at depth 0 (fuel: one per byte)
def aj.args.go(fuel: Nat, m: Maybe<&2, Nat>, +xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match fuel m:
    case 1n+p Some{+n}:
      +rest = aj.drop(xs, Nat.add(n, 2n))
      aj.trim(aj.take(xs, n)) <> aj.args.go(p, aj.find(False{}, S.b(", "), rest), rest)
    case _ None{}:
      Bool.pick(List<&2, List<&2, U32>>, List.is_empty(&2, U32, aj.trim(xs)), Nil{}, [aj.trim(xs)])
    case 0n _:
      [xs]

def aj.args(+xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  aj.args.go(aj.len(xs), aj.find(False{}, S.b(", "), xs), xs)

# Squares and examples ------------------------------------------------------------

# a line of PROPOSED.bend (law NAME:, for VAR: T, the equation, a def's
# name) or of F (an import, a type's name, an example law: h, its name
# exK, its statement)
type Ln is Data:
  LnLaw{n: List<&2, U32>}
  LnFor{v: List<&2, U32>}
  LnEq{s: List<&2, U32>}
  LnDef{n: List<&2, U32>}
  LnImp{s: List<&2, U32>}
  LnType{n: List<&2, U32>}
  LnEx{h: List<&2, U32>, k: List<&2, U32>, s: List<&2, U32>}
  LnNo{}

# a for's variable: its name without its mark
def aj.var(+l: List<&2, U32>) -> List<&2, U32>:
  +v = S.until(aj.after(l, S.b("for ")), 58)
  Bool.pick(List<&2, U32>, Bool.or(S.head.is(v, 45), Bool.or(S.head.is(v, 43), S.head.is(v, 126))), List.drop(&2, U32, v, 1n), v)

# a def's name (up to its ( or :)
def aj.dname(+l: List<&2, U32>) -> List<&2, U32>:
  S.until(S.until(aj.after(l, S.b("def ")), 40), 58)

# a type's name (up to < or a space)
def aj.tname(+l: List<&2, U32>) -> List<&2, U32>:
  S.until(S.until(aj.after(l, S.b("type ")), 60), 32)

def aj.cut.a(m: Maybe<&2, Ap>, +d: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{Ap{a, b}}:
      a
    case None{}:
      d

# def h.exK() -> {STATEMENT}:
def aj.ex(+l: List<&2, U32>) -> Ln:
  +n = aj.dname(l)
  +s = aj.after(l, S.b("() -> {"))
  LnEx{aj.cut.a(aj.cut.at(S.find(n, S.b(".ex"), 0n), n, 3n), n), aj.cat(S.b("ex"), aj.after(n, S.b(".ex"))), aj.take(s, Nat.sub(aj.len(s), 2n))}

def aj.cls(+l: List<&2, U32>) -> Ln:
  Bool.pick(Ln, S.prefix(l, S.b("law ")), LnLaw{S.until(aj.after(l, S.b("law ")), 58)}, Bool.pick(Ln, S.prefix(l, S.b("  for ")), LnFor{aj.var(l)}, Bool.pick(Ln, S.prefix(l, S.b("  {")), LnEq{aj.trim(l)}, Bool.pick(Ln, Bool.and(S.prefix(l, S.b("def ")), Bool.and(S.infix(l, S.b(".ex")), S.infix(l, S.b("() -> {")))), aj.ex(l), Bool.pick(Ln, S.prefix(l, S.b("def ")), LnDef{aj.dname(l)}, Bool.pick(Ln, S.prefix(l, S.b("import ./")), LnImp{l}, Bool.pick(Ln, S.prefix(l, S.b("type ")), LnType{aj.tname(l)}, LnNo{})))))))

def aj.clss(ls: List<&2, List<&2, U32>>) -> List<&2, Ln>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      aj.cls(l) <> aj.clss(t)

# a square: its name, its variables, its equation's sides and type
type Sq is Data:
  Sq{n: List<&2, U32>, vs: List<&2, List<&2, U32>>, eq: List<&2, U32>}

def aj.sqs(ls: List<&2, Ln>, +n: List<&2, U32>, vs: List<&2, List<&2, U32>>) -> List<&2, Sq>:
  match ls:
    case Nil{}:
      Nil{}
    case LnLaw{m} <> t:
      aj.sqs(t, m, Nil{})
    case LnFor{v} <> t:
      aj.sqs(t, n, v <> vs)
    case LnEq{s} <> t:
      Sq{n, List.reverse(&2, List<&2, U32>, vs), s} <> aj.sqs(t, Nil{}, Nil{})
    case _ <> t:
      aj.sqs(t, n, vs)

def aj.defs(ls: List<&2, Ln>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case LnDef{n} <> t:
      n <> aj.defs(t)
    case _ <> t:
      aj.defs(t)

def aj.imps(ls: List<&2, Ln>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case LnImp{s} <> t:
      s <> aj.imps(t)
    case _ <> t:
      aj.imps(t)

def aj.types(ls: List<&2, Ln>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case LnType{n} <> t:
      n <> aj.types(t)
    case _ <> t:
      aj.types(t)

# an example law: h, its name (exK), h's arguments and GHC's answer (F's
# own types qualified)
type Ex is Data:
  Ex{h: List<&2, U32>, k: List<&2, U32>, args: List<&2, List<&2, U32>>, v: List<&2, U32>}

def aj.qual(xs: List<&2, List<&2, U32>>, +own: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      aj.tx(x, AeOwn{own}) <> aj.qual(t, own)

def aj.ex.mk(+h: List<&2, U32>, +k: List<&2, U32>, m: Maybe<&2, Ap>, +rest: List<&2, U32>, +own: List<&2, List<&2, U32>>) -> List<&2, Ex>:
  match m:
    case Some{Ap{as, r2}}:
      [Ex{h, k, aj.qual(aj.args(as), own), aj.tx(aj.cut.a(aj.cut(S.b(" : "), rest), rest), AeOwn{own})}]
    case None{}:
      Nil{}

# h(ARGS) == V : R
def aj.ex.of(+h: List<&2, U32>, +k: List<&2, U32>, m: Maybe<&2, Ap>, +own: List<&2, List<&2, U32>>) -> List<&2, Ex>:
  match m:
    case Some{Ap{call, rest}}:
      aj.ex.mk(h, k, aj.call(aj.after(call, S.b("("))), rest, own)
    case None{}:
      Nil{}

def aj.exs(ls: List<&2, Ln>, +own: List<&2, List<&2, U32>>) -> List<&2, Ex>:
  match ls:
    case Nil{}:
      Nil{}
    case LnEx{h, k, +s} <> t:
      List.append(&2, Ex, aj.ex.of(h, k, aj.cut(S.b(" == "), s), own), aj.exs(t, own))
    case _ <> t:
      aj.exs(t, own)

# the examples' functions, each once
def aj.hs(xs: List<&2, Ex>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, acc)
    case Ex{+h, k, a, v} <> t:
      aj.hs(t, Bool.pick(List<&2, List<&2, U32>>, S.mem(h, acc), acc, h <> acc))

def aj.exs.of(xs: List<&2, Ex>, +h: List<&2, U32>) -> List<&2, Ex>:
  match xs:
    case Nil{}:
      Nil{}
    case Ex{+g, k, a, v} <> t:
      +r = aj.exs.of(t, h)
      Bool.pick(List<&2, Ex>, S.eq(g, h), Ex{g, k, a, v} <> r, r)

# Instances -----------------------------------------------------------------------

# a square's equation, {LHS == RHS : T}: its sides and type; the F call in
# LHS: the text before it, h, its arguments, the text after
type Eq is Data:
  Eq{lhs: List<&2, U32>, rhs: List<&2, U32>, ty: List<&2, U32>}

type Cl is Data:
  Cl{pre: List<&2, U32>, h: List<&2, U32>, args: List<&2, List<&2, U32>>, post: List<&2, U32>}

def aj.eq.rt(+l: List<&2, U32>, m: Maybe<&2, Ap>) -> Maybe<&2, Eq>:
  match m:
    case Some{Ap{r, t}}:
      Some{Eq{l, r, t}}
    case None{}:
      None{}

def aj.eq.at(m: Maybe<&2, Ap>) -> Maybe<&2, Eq>:
  match m:
    case Some{Ap{l, rest}}:
      aj.eq.rt(l, aj.cut(S.b(" : "), rest))
    case None{}:
      None{}

def aj.eq(+s: List<&2, U32>) -> Maybe<&2, Eq>:
  +body = aj.drop(s, 1n)
  aj.eq.at(aj.cut(S.b(" == "), aj.take(body, Nat.sub(aj.len(body), 1n))))

# the first of hs called in xs as F.h(
def aj.which(hs: List<&2, List<&2, U32>>, +xs: List<&2, U32>) -> List<&2, U32>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> t:
      Bool.pick(List<&2, U32>, S.infix(xs, aj.cat3(S.b("F."), h, S.b("("))), h, aj.which(t, xs))

def aj.cl.at(+h: List<&2, U32>, +pre: List<&2, U32>, m: Maybe<&2, Ap>) -> Maybe<&2, Cl>:
  match m:
    case Some{Ap{as, post}}:
      Some{Cl{pre, h, aj.args(as), post}}
    case None{}:
      None{}

def aj.cl.find(m: Maybe<&2, Nat>, +h: List<&2, U32>, +lhs: List<&2, U32>, +n: Nat) -> Maybe<&2, Cl>:
  match m:
    case Some{+i}:
      aj.cl.at(h, aj.take(lhs, i), aj.call(aj.drop(lhs, Nat.add(i, n))))
    case None{}:
      None{}

def aj.cl(+h: List<&2, U32>, +lhs: List<&2, U32>) -> Maybe<&2, Cl>:
  +p = aj.cat3(S.b("F."), h, S.b("("))
  aj.cl.find(S.find(lhs, p, 0n), h, lhs, aj.len(p))

# the call's arguments bound to an example's (each must be a variable of
# the square, and every variable bound)
def aj.bind(cs: List<&2, List<&2, U32>>, as: List<&2, List<&2, U32>>) -> List<&2, Av>:
  match cs as:
    case c <> ct a <> at:
      Av{c, a} <> aj.bind(ct, at)
    case _ _:
      Nil{}

def aj.allin(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.and(S.mem(x, ys), aj.allin(t, ys))

def aj.nlen(+xs: List<&2, List<&2, U32>>) -> Nat:
  List.length(&2, List<&2, U32>, xs)

# whether the call's arguments are exactly the square's variables (in some
# order, each once)
def aj.binds(+cs: List<&2, List<&2, U32>>, +vs: List<&2, List<&2, U32>>) -> Bool:
  Bool.and(Nat.is_eq(aj.nlen(cs), aj.nlen(vs)), Bool.and(aj.allin(cs, vs), aj.allin(vs, cs)))

# one instance: the square at example x, GHC's answer in F.h(x)'s place;
# rhs: the right side (a mutant's, or the square's own)
def aj.inst(+pfx: List<&2, U32>, +c: Cl, +q: Eq, +rhs: List<&2, U32>, +pd: List<&2, List<&2, U32>>, x: Ex) -> List<&2, U32>:
  match c q x:
    case Cl{pre, h, cs, post} Eq{l, r, ty} Ex{g, k, as, v}:
      +e = {AeSub{aj.bind(cs, as), pd} : Ae}
      aj.s("def adj.", aj.cat3(pfx, 46 <> k, aj.s("() -> {", aj.cat3(aj.tx(pre, e), v, aj.cat3(aj.tx(post, e), S.b(" == "), aj.cat3(aj.tx(rhs, e), S.b(" : "), aj.cat(aj.tx(ty, e), S.b("}:\n  {==}\n\n"))))))))

def aj.insts(+pfx: List<&2, U32>, +c: Cl, +q: Eq, +rhs: List<&2, U32>, +pd: List<&2, List<&2, U32>>, xs: List<&2, Ex>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      aj.cat(aj.inst(pfx, c, q, rhs, pd, x), aj.insts(pfx, c, q, rhs, pd, t))

# What a square gives: its call of F.h, its equation and examples, or why
# none
type Pr is Data:
  Pr{sq: List<&2, U32>, c: Cl, q: Eq, xs: List<&2, Ex>}
  PrNo{sq: List<&2, U32>, why: List<&2, U32>}

def aj.pr.cl(+n: List<&2, U32>, +vs: List<&2, List<&2, U32>>, q: Eq, m: Maybe<&2, Cl>, +xs: List<&2, Ex>) -> Pr:
  match m:
    case Some{Cl{pre, +h, +cs, post}}:
      Bool.pick(Pr, aj.binds(cs, vs), Pr{n, Cl{pre, h, cs, post}, q, aj.exs.of(xs, h)}, PrNo{n, S.b("the call's arguments are not the square's variables")})
    case None{}:
      PrNo{n, S.b("no call of F.h")}

def aj.pr.h(+n: List<&2, U32>, +vs: List<&2, List<&2, U32>>, +h: List<&2, U32>, q: Eq, +xs: List<&2, Ex>) -> Pr:
  match q:
    case Eq{+l, r, t}:
      Bool.pick(Pr, List.is_empty(&2, U32, h), PrNo{n, S.b("F's function has no example laws")}, aj.pr.cl(n, vs, Eq{l, r, t}, aj.cl(h, l), xs))

def aj.pr.eq(+n: List<&2, U32>, +vs: List<&2, List<&2, U32>>, m: Maybe<&2, Eq>, +hs: List<&2, List<&2, U32>>, +xs: List<&2, Ex>) -> Pr:
  match m:
    case Some{Eq{+l, r, t}}:
      aj.pr.h(n, vs, aj.which(hs, l), Eq{l, r, t}, xs)
    case None{}:
      PrNo{n, S.b("the equation is not {LHS == RHS : T}")}

def aj.prs(qs: List<&2, Sq>, +hs: List<&2, List<&2, U32>>, +xs: List<&2, Ex>) -> List<&2, Pr>:
  match qs:
    case Nil{}:
      Nil{}
    case Sq{n, vs, s} <> t:
      aj.pr.eq(n, vs, aj.eq(s), hs, xs) <> aj.prs(t, hs, xs)

# Mutants: a square's b (the right side's function, up to its first () and
# its shape (its type and b's arguments)
def aj.rfun(+r: List<&2, U32>) -> List<&2, U32>:
  S.until(r, 40)

def aj.rargs(+r: List<&2, U32>) -> List<&2, U32>:
  aj.drop(r, aj.len(S.until(r, 40)))

def aj.shape(+q: Eq) -> List<&2, U32>:
  match q:
    case Eq{l, r, t}:
      aj.cat3(t, S.b(" | "), aj.rargs(r))

def aj.rhs(+q: Eq) -> List<&2, U32>:
  match q:
    case Eq{l, r, t}:
      r

# Checking --------------------------------------------------------------------------

def aj.head(+n: List<&2, U32>, imps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  aj.s("# Adj (bend/Adj.bend): ", aj.cat(n, aj.s("'s instances at GHC's example answers\nimport Base\n", aj.cat(S.join(imps, 10), S.b("\nimport ./adj_phi.bend as P\n\n")))))

type Rs is Data:
  Rs{ok: Bool, text: List<&2, U32>}

def aj.rs.of(+t: List<&2, U32>) -> Rs:
  Rs{S.prefix(t, S.b("ALL PROOFS CHECK")), S.lines.first(t)}

def aj.check(+bend: String, +dir: String, +file: String, +flag: String) -> IO(Rs):
  do IO<Rs>:
    o : S.Out <- S.run(dir, ["BEND_NO_TELEMETRY=1"], 600, bend, [file, flag], Nil{})
    return aj.rs.of(S.Out.text(o))

def aj.ok.s(ok: Bool) -> String:
  match ok:
    case True{}:
      "ALL PROOFS CHECK"
    case False{}:
      "SOME PROOFS FAIL"

def aj.count(+x: Pr) -> Nat:
  match x:
    case Pr{n, c, q, xs}:
      List.length(&2, Ex, xs)
    case PrNo{n, w}:
      0n

def aj.npfx(+n: List<&2, U32>) -> String:
  S.str(n)

def aj.rs.s(+r: Rs) -> String:
  match r:
    case Rs{ok, t}:
      S.str(t)

def aj.rs.n(+r: Rs, +k: Nat) -> Nat:
  match r:
    case Rs{ok, t}:
      Bool.pick(Nat, ok, k, 0n)

# a square's instances: written, checked, verdict
def aj.one(+bend: String, +dir: String, +imps: List<&2, List<&2, U32>>, +pd: List<&2, List<&2, U32>>, x: Pr) -> IO(Nat):
  match x:
    case PrNo{n, why}:
      do IO<Nat>:
        IO.print(S.str(n) ++ "\tno instances: " ++ S.str(why))
        return 0n
    case Pr{+n, +c, +q, +xs}:
      +k = List.length(&2, Ex, xs)
      +f = "adj." ++ S.str(n) ++ ".bend"
      do IO<Nat>:
        S.write(dir ++ "/" ++ f, aj.cat(aj.head(n, imps), aj.insts(n, c, q, aj.rhs(q), pd, xs)))
        +c1 : Rs <- aj.check(bend, dir, f, "--check-only")
        v1 : Rs <- aj.check(bend, dir, f, "--verdict")
        IO.print(S.str(n) ++ "\t" ++ Nat.show(k) ++ " instances at GHC's answers\tcheck: " ++ aj.rs.s(c1) ++ "\tverdict: " ++ aj.rs.s(v1))
        return aj.rs.n(c1, k)

def aj.all(+bend: String, +dir: String, +imps: List<&2, List<&2, U32>>, +pd: List<&2, List<&2, U32>>, xs: List<&2, Pr>) -> IO(Nat):
  match xs:
    case Nil{}:
      IO.pure(Nat, 0n)
    case x <> t:
      do IO<Nat>:
        a : Nat <- aj.one(bend, dir, imps, pd, x)
        b : Nat <- aj.all(bend, dir, imps, pd, t)
        return Nat.add(a, b)

# Mutants.  Two squares of one shape (their T and their b's arguments the
# same), b swapped: square x with y's b.  Its instances at GHC's answers
# should fail (ex: whether they do), and so should PROOF.bend, run on a
# copy of PROPOSED.bend whose square x has y's b (pf: the squares for
# every input; the copy sits in WORK/mut.X.as.Y, beside links to WORK's
# directories)
type Mu is Data:
  Mu{n: Nat, ex: Nat, pf: Nat}

def aj.mu.add(+a: Mu, +b: Mu) -> Mu:
  match a b:
    case Mu{n, k, p} Mu{m, j, q}:
      Mu{Nat.add(n, m), Nat.add(k, j), Nat.add(p, q)}

def aj.rs.ok(+r: Rs) -> Bool:
  match r:
    case Rs{ok, t}:
      ok

# what a mutant needs of the run: the bend, WORK, the instances' imports,
# PROPOSED.bend's defs and lines, PROOF.bend, and the directories
# PROPOSED.bend imports from
type Cx is Data:
  Cx{bend: String, dir: String, imps: List<&2, List<&2, U32>>, pd: List<&2, List<&2, U32>>, pl: List<&2, List<&2, U32>>, proof: List<&2, U32>, dirs: List<&2, List<&2, U32>>}

def aj.cx.bend(+c: Cx) -> String:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      b

def aj.cx.dir(+c: Cx) -> String:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      d

def aj.cx.imps(+c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      i

def aj.cx.pd(+c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      p

def aj.cx.pl(+c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      l

def aj.cx.proof(+c: Cx) -> List<&2, U32>:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      f

def aj.cx.dirs(+c: Cx) -> List<&2, List<&2, U32>>:
  match c:
    case Cx{b, d, i, p, l, f, ds}:
      ds

# a square's equation as its line has it (trimmed)
def aj.eq.text(+q: Eq) -> List<&2, U32>:
  match q:
    case Eq{l, r, t}:
      aj.s("{", aj.cat3(l, S.b(" == "), aj.cat3(r, S.b(" : "), aj.cat(t, S.b("}")))))

# a square's equation line again, with rhs for its right side
def aj.eq.line(+q: Eq, +rhs: List<&2, U32>) -> List<&2, U32>:
  match q:
    case Eq{l, r, t}:
      aj.s("  {", aj.cat3(l, S.b(" == "), aj.cat3(rhs, S.b(" : "), aj.cat(t, S.b("}")))))

# PROPOSED.bend's lines with the line old (trimmed) replaced by new
def aj.relines(ls: List<&2, List<&2, U32>>, +old: List<&2, U32>, +new: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      Bool.pick(List<&2, U32>, S.eq(aj.trim(l), old), new, l) <> aj.relines(t, old, new)

def aj.links(+bend: String, +d: String, ds: List<&2, List<&2, U32>>) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +x <> t:
      do IO<Unit>:
        o : S.Out <- S.run(d, [], 30, "ln", ["-sfn", "../" ++ S.str(x), S.str(x)], Nil{})
        aj.links(bend, d, t)

def aj.mu.w(+n: List<&2, U32>, +m: List<&2, U32>, +rhs: List<&2, U32>) -> String:
  "mutant\t" ++ S.str(n) ++ " with " ++ S.str(m) ++ "'s b (" ++ S.str(aj.rfun(rhs)) ++ ")"

def aj.kill(ok: Bool) -> Nat:
  match ok:
    case True{}:
      0n
    case False{}:
      1n

def aj.kill.s(ok: Bool) -> String:
  match ok:
    case True{}:
      "SURVIVED"
    case False{}:
      "killed"

def aj.mu.done(+ex: Bool, +pf: Bool, +n: List<&2, U32>, +m: List<&2, U32>, +rhs: List<&2, U32>) -> IO(Mu):
  do IO<Mu>:
    IO.print(aj.mu.w(n, m, rhs) ++ "\tat GHC's answers: " ++ aj.kill.s(ex) ++ "\tfor every input (PROOF.bend): " ++ aj.kill.s(pf))
    return Mu{1n, aj.kill(ex), aj.kill(pf)}

def aj.mu.run(go: Bool, +cx: Cx, +n: List<&2, U32>, +m: List<&2, U32>, +c: Cl, +q: Eq, +rhs: List<&2, U32>, +xs: List<&2, Ex>) -> IO(Mu):
  match go:
    case True{}:
      +f = "adj.mutant." ++ S.str(n) ++ ".as." ++ S.str(m) ++ ".bend"
      +dir = aj.cx.dir(cx)
      +md = dir ++ "/mut." ++ S.str(n) ++ ".as." ++ S.str(m)
      +bend = aj.cx.bend(cx)
      do IO<Mu>:
        S.write(dir ++ "/" ++ f, aj.cat(aj.head(n, aj.cx.imps(cx)), aj.insts(n, c, q, rhs, aj.cx.pd(cx), xs)))
        r : Rs <- aj.check(bend, dir, f, "--check-only")
        S.mkdir(md)
        aj.links(bend, md, aj.cx.dirs(cx))
        S.write(md ++ "/PROPOSED.bend", S.join(aj.relines(aj.cx.pl(cx), aj.eq.text(q), aj.eq.line(q, rhs)), 10))
        S.write(md ++ "/PROOF.bend", aj.cx.proof(cx))
        p : Rs <- aj.check(bend, md, "PROOF.bend", "--check-only")
        aj.mu.done(aj.rs.ok(r), aj.rs.ok(p), n, m, rhs)
    case False{}:
      IO.pure(Mu, Mu{0n, 0n, 0n})

def aj.mu.one(+cx: Cx, +x: Pr, y: Pr) -> IO(Mu):
  match x y:
    case Pr{+n, +c, +q, +xs} Pr{+m, d, +r, ys}:
      +same = Bool.and(S.eq(aj.shape(q), aj.shape(r)), Bool.not(S.eq(aj.rfun(aj.rhs(q)), aj.rfun(aj.rhs(r)))))
      aj.mu.run(same, cx, n, m, c, q, aj.cat(aj.rfun(aj.rhs(r)), aj.rargs(aj.rhs(q))), xs)
    case _ _:
      IO.pure(Mu, Mu{0n, 0n, 0n})

def aj.mu.row(+cx: Cx, +x: Pr, ys: List<&2, Pr>) -> IO(Mu):
  match ys:
    case Nil{}:
      IO.pure(Mu, Mu{0n, 0n, 0n})
    case y <> t:
      do IO<Mu>:
        a : Mu <- aj.mu.one(cx, x, y)
        b : Mu <- aj.mu.row(cx, x, t)
        return aj.mu.add(a, b)

def aj.mu.all(+cx: Cx, xs: List<&2, Pr>, +ys: List<&2, Pr>) -> IO(Mu):
  match xs:
    case Nil{}:
      IO.pure(Mu, Mu{0n, 0n, 0n})
    case +x <> t:
      do IO<Mu>:
        a : Mu <- aj.mu.row(cx, x, ys)
        b : Mu <- aj.mu.all(cx, t, ys)
        return aj.mu.add(a, b)

def aj.total(xs: List<&2, Pr>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(aj.count(x), aj.total(t))

# the directories PROPOSED.bend imports from (import ./D/X.bend as A), each
# once
def aj.idir(+l: List<&2, U32>) -> List<&2, U32>:
  +p = S.until(aj.after(l, S.b("import ./")), 32)
  Bool.pick(List<&2, U32>, S.infix(p, S.b("/")), S.until(p, 47), Nil{})

def aj.dirs(ls: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      acc
    case +l <> t:
      +d = aj.idir(l)
      aj.dirs(t, Bool.pick(List<&2, List<&2, U32>>, Bool.or(List.is_empty(&2, U32, d), S.mem(d, acc)), acc, d <> acc))

# PROPOSED.bend's lines without its laws (a law: from its line to the next
# blank one)
def aj.nolaws(ls: List<&2, List<&2, U32>>, in: Bool) -> List<&2, List<&2, U32>>:
  match ls in:
    case Nil{} _:
      Nil{}
    case +l <> t True{}:
      aj.nolaws(t, Bool.not(List.is_empty(&2, U32, l)))
    case +l <> t False{}:
      +r = aj.nolaws(t, S.prefix(l, S.b("law ")))
      Bool.pick(List<&2, List<&2, U32>>, S.prefix(l, S.b("law ")), r, l <> r)

# F's imports, from the importing file beside it (./l/): ./X as A is ./l/X
# as A
def aj.rebase(xs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      S.replace.first(x, S.b("import ./"), S.b("import ./l/")) <> aj.rebase(t)

def aj.mu.s(+m: Mu) -> String:
  match m:
    case Mu{n, k, p}:
      Nat.show(n) ++ ", killed at GHC's answers " ++ Nat.show(k) ++ ", killed by PROOF.bend " ++ Nat.show(p)

def aj.go(+bend: String, +dir: String, ptext: List<&2, U32>, ftext: List<&2, U32>, proof: List<&2, U32>) -> IO(Unit):
  +plines = S.split(ptext, 10)
  +pl = aj.clss(plines)
  +fl = aj.clss(S.split(ftext, 10))
  +own = aj.types(fl)
  +xs = aj.exs(fl, own)
  +prs = aj.prs(aj.sqs(pl, Nil{}, Nil{}), aj.hs(xs, Nil{}), xs)
  +imps = List.append(&2, List<&2, U32>, aj.imps(pl), aj.rebase(aj.imps(fl)))
  +pd = aj.defs(pl)
  do IO<Unit>:
    S.write(dir ++ "/adj_phi.bend", aj.s("# Adj (bend/Adj.bend): PROPOSED.bend without its laws (open, they would fail the checks of the defs that import it)\n", S.join(aj.nolaws(plines, False{}), 10)))
    ok : Nat <- aj.all(bend, dir, imps, pd, prs)
    mu : Mu <- aj.mu.all(Cx{bend, dir, imps, pd, plines, proof, aj.dirs(aj.imps(pl), Nil{})}, prs, prs)
    IO.print("instances at GHC's answers: " ++ Nat.show(aj.total(prs)) ++ ", in files that check: " ++ Nat.show(ok) ++ "; mutants: " ++ aj.mu.s(mu))

def aj.main(+bend: String, +dir: String, +mod: String) -> IO(Unit):
  do IO<Unit>:
    ptext : List<&2, U32> <- S.read(dir ++ "/PROPOSED.bend")
    ftext : List<&2, U32> <- S.read(dir ++ "/l/" ++ mod)
    proof : List<&2, U32> <- S.read(dir ++ "/PROOF.bend")
    aj.go(bend, dir, ptext, ftext, proof)

def aj.argv(+bend: String, args: List<String>) -> IO(Unit):
  match args:
    case dir <> mod <> t:
      aj.main(bend, dir, mod)
    case _:
      IO.print("usage: adj WORK MOD.bend  (WORK: PROPOSED.bend and l/MOD.bend, cata's Bend of h's module with its example laws; BEND: the bend)")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    +bend : String <- S.env("BEND", "bend")
    aj.argv(bend, List.drop(&1, String, argv, 1n))
