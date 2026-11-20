
# Text.Megaparsec's Parsec Void String (megaparsec 9.7.0, parser-combinators
# 1.3.1): a parser is a function of the state to a reply, HsPcSt ->
# HsPcRep<A>, the reply megaparsec's four continuations folded into one
# value: whether input was consumed, and a result with the hints (what an
# error at that offset would also have expected) or an error. Positions are
# counted as megaparsec's reachOffset counts them (tab width 8; a wide
# character is one column here, two there). A parser is a closure, called at
# most once, so the combinators that run a parser again (many, sepBy,
# manyTill, ...) take it as a template, given an environment E of the
# caller's data it names (Unit when none).

type HsPcItem is Data:
  HsPcItem.Tokens{ts: List<&2, Char>}
  HsPcItem.Label{l: List<&2, Char>}
  HsPcItem.Eoi{}

type HsPcFancy is Data:
  HsPcFancy.Fail{msg: List<&2, Char>}
  HsPcFancy.Indent{ord: Cmp, ref: Nat, act: Nat}

type HsPcError is Data:
  HsPcError.Trivial{off: Nat, un: Maybe<&2, HsPcItem>, ex: List<&2, HsPcItem>}
  HsPcError.Fancy{off: Nat, xs: List<&2, HsPcFancy>}

# the input left, its offset, the line and column there, the source's name
type HsPcSt is Data:
  HsPcSt{inp: List<&2, Char>, off: Nat, line: Nat, col: Nat, name: List<&2, Char>}

type HsPcRes<-A: Data> is Data:
  HsPcRes.Ok{x: A, s: HsPcSt, hs: List<&2, HsPcItem>}
  HsPcRes.Bad{e: HsPcError, s: HsPcSt}

type HsPcRep<-A: Data> is Data:
  HsPcRep{c: Bool, r: HsPcRes<A>}

# SourcePos: the name, the line and the column (each Pos a Nat from 1)
type HsPcPos is Data:
  HsPcPos{name: List<&2, Char>, line: Nat, col: Nat}

# ParseErrorBundle: the error and the input and name the run started with
type HsPcBundle is Data:
  HsPcBundle{e: HsPcError, inp: List<&2, Char>, name: List<&2, Char>}

# Sets as ascending lists: ErrorItem's derived Ord (Tokens < Label < end of
# input), ErrorFancy's (ErrorFail < ErrorIndentation)

def HsPc.cmp.cmp(a: Cmp, b: Cmp) -> Cmp:
  match a b:
    case LT{} LT{}:
      EQ{}
    case LT{} _:
      LT{}
    case EQ{} LT{}:
      GT{}
    case EQ{} EQ{}:
      EQ{}
    case EQ{} GT{}:
      LT{}
    case GT{} GT{}:
      EQ{}
    case GT{} _:
      GT{}

# a lexicographic compare: the first's unless EQ
def HsPc.cmp.then(a: Cmp, b: Cmp) -> Cmp:
  match a:
    case EQ{}:
      b
    case o:
      o

def HsPc.cmp.str(a: List<&2, Char>, b: List<&2, Char>) -> Cmp:
  HsCmp.list(~Char, ~HsCmp.char, a, b)

# == at strings
def HsPc.str.eq(xs: List<&2, Char>, ys: List<&2, Char>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Bool.and(Char.is_eq(x, y), HsPc.str.eq(xt, yt))
    case _ _:
      False{}

def HsPc.cmp.item(a: HsPcItem, b: HsPcItem) -> Cmp:
  match a b:
    case HsPcItem.Tokens{x} HsPcItem.Tokens{y}:
      HsPc.cmp.str(x, y)
    case HsPcItem.Tokens{x} _:
      LT{}
    case HsPcItem.Label{x} HsPcItem.Tokens{y}:
      GT{}
    case HsPcItem.Label{x} HsPcItem.Label{y}:
      HsPc.cmp.str(x, y)
    case HsPcItem.Label{x} HsPcItem.Eoi{}:
      LT{}
    case HsPcItem.Eoi{} HsPcItem.Eoi{}:
      EQ{}
    case HsPcItem.Eoi{} _:
      GT{}

def HsPc.cmp.fancy(a: HsPcFancy, b: HsPcFancy) -> Cmp:
  match a b:
    case HsPcFancy.Fail{x} HsPcFancy.Fail{y}:
      HsPc.cmp.str(x, y)
    case HsPcFancy.Fail{x} _:
      LT{}
    case HsPcFancy.Indent{o1, r1, a1} HsPcFancy.Fail{y}:
      GT{}
    case HsPcFancy.Indent{o1, r1, a1} HsPcFancy.Indent{o2, r2, a2}:
      HsPc.cmp.then(HsPc.cmp.cmp(o1, o2), HsPc.cmp.then(Nat.cmp(r1, r2), Nat.cmp(a1, a2)))

def HsPc.iset.ins(+x: HsPcItem, xs: List<&2, HsPcItem>) -> List<&2, HsPcItem>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      HsCmp.on(List<&2, HsPcItem>, HsPc.cmp.item(x, h), _ => x <> h <> t, _ => h <> t, _ => h <> HsPc.iset.ins(x, t))

def HsPc.iset.union(xs: List<&2, HsPcItem>, ys: List<&2, HsPcItem>) -> List<&2, HsPcItem>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      HsPc.iset.ins(h, HsPc.iset.union(t, ys))

def HsPc.fset.ins(+x: HsPcFancy, xs: List<&2, HsPcFancy>) -> List<&2, HsPcFancy>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      HsCmp.on(List<&2, HsPcFancy>, HsPc.cmp.fancy(x, h), _ => x <> h <> t, _ => h <> t, _ => h <> HsPc.fset.ins(x, t))

def HsPc.fset.union(xs: List<&2, HsPcFancy>, ys: List<&2, HsPcFancy>) -> List<&2, HsPcFancy>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      HsPc.fset.ins(h, HsPc.fset.union(t, ys))

def HsPc.sset.ins(+x: List<&2, Char>, xs: List<&2, List<&2, Char>>) -> List<&2, List<&2, Char>>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      HsCmp.on(List<&2, List<&2, Char>>, HsPc.cmp.str(x, h), _ => x <> h <> t, _ => h <> t, _ => h <> HsPc.sset.ins(x, t))

# the larger of two items (mergeError's max of the unexpected ones)
def HsPc.item.max(+a: HsPcItem, +b: HsPcItem) -> HsPcItem:
  HsCmp.on(HsPcItem, HsPc.cmp.item(a, b), _ => b, _ => b, _ => a)

def HsPc.un.merge(a: Maybe<&2, HsPcItem>, b: Maybe<&2, HsPcItem>) -> Maybe<&2, HsPcItem>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{x} Some{y}:
      Some{HsPc.item.max(x, y)}

def HsPc.err.off(e: HsPcError) -> Nat:
  match e:
    case HsPcError.Trivial{o, u, p}:
      o
    case HsPcError.Fancy{o, xs}:
      o

# errors at one offset merge; else the later one stands (ParseError's <>)
def HsPc.err.same(e1: HsPcError, e2: HsPcError) -> HsPcError:
  match e1 e2:
    case HsPcError.Trivial{s1, u1, p1} HsPcError.Trivial{s2, u2, p2}:
      HsPcError.Trivial{s1, HsPc.un.merge(u1, u2), HsPc.iset.union(p1, p2)}
    case HsPcError.Fancy{s1, x1} HsPcError.Trivial{s2, u2, p2}:
      HsPcError.Fancy{s1, x1}
    case HsPcError.Trivial{s1, u1, p1} HsPcError.Fancy{s2, x2}:
      HsPcError.Fancy{s2, x2}
    case HsPcError.Fancy{s1, x1} HsPcError.Fancy{s2, x2}:
      HsPcError.Fancy{s1, HsPc.fset.union(x1, x2)}

def HsPc.err.merge(+e1: HsPcError, +e2: HsPcError) -> HsPcError:
  HsCmp.on(HsPcError, Nat.cmp(HsPc.err.off(e1), HsPc.err.off(e2)), _ => e2, _ => HsPc.err.same(e1, e2), _ => e1)

# the later of two states (longestMatch)
def HsPc.st.off(s: HsPcSt) -> Nat:
  match s:
    case HsPcSt{i, o, l, c, n}:
      o

def HsPc.longest(+s1: HsPcSt, +s2: HsPcSt) -> HsPcSt:
  Bool.pick(HsPcSt, Nat.is_gt(HsPc.st.off(s1), HsPc.st.off(s2)), s1, s2)

# an error's expected items as hints, if it is at the offset (toHints)
def HsPc.hints(+o: Nat, e: HsPcError) -> List<&2, HsPcItem>:
  match e:
    case HsPcError.Trivial{+eo, u, ps}:
      Bool.pick(List<&2, HsPcItem>, Nat.is_eq(o, eo), ps, Nil{})
    case HsPcError.Fancy{eo, xs}:
      Nil{}

# hints added to an error's expected items (withHints)
def HsPc.err.hint(+hs: List<&2, HsPcItem>, e: HsPcError) -> HsPcError:
  match e:
    case HsPcError.Trivial{o, u, ps}:
      HsPcError.Trivial{o, u, HsPc.iset.union(ps, hs)}
    case f:
      f

# The core ------------------------------------------------------------------

def HsPc.pure(-A: Data, x: A) -> HsPcSt -> HsPcRep<A>:
  s => HsPcRep{False{}, HsPcRes.Ok{x, s, Nil{}}}

# hints hs of the first parser, before a second that did not consume
def HsPc.res.hint(-B: Data, +hs: List<&2, HsPcItem>, r: HsPcRes<B>) -> HsPcRes<B>:
  match r:
    case HsPcRes.Ok{x, s, h2}:
      HsPcRes.Ok{x, s, HsPc.iset.union(hs, h2)}
    case HsPcRes.Bad{e, s}:
      HsPcRes.Bad{HsPc.err.hint(hs, e), s}

def HsPc.bind.k(-B: Data, c1: Bool, +hs: List<&2, HsPcItem>, r: HsPcRep<B>) -> HsPcRep<B>:
  match r:
    case HsPcRep{True{}, r2}:
      HsPcRep{True{}, r2}
    case HsPcRep{False{}, r2}:
      HsPcRep{c1, HsPc.res.hint(B, hs, r2)}

def HsPc.bind.go(-A: Data, -B: Data, r: HsPcRep<A>, k: A -> HsPcSt -> HsPcRep<B>) -> HsPcRep<B>:
  match r:
    case HsPcRep{c, HsPcRes.Ok{x, s, hs}}:
      HsPc.bind.k(B, c, hs, k(x)(s))
    case HsPcRep{c, HsPcRes.Bad{e, s}}:
      HsPcRep{c, HsPcRes.Bad{e, s}}

def HsPc.bind(-A: Data, -B: Data, m: HsPcSt -> HsPcRep<A>, k: A -> HsPcSt -> HsPcRep<B>) -> HsPcSt -> HsPcRep<B>:
  s => HsPc.bind.go(A, B, m(s), k)

def HsPc.map.go(-A: Data, -B: Data, f: A -> B, r: HsPcRep<A>) -> HsPcRep<B>:
  match r:
    case HsPcRep{c, HsPcRes.Ok{x, s, hs}}:
      HsPcRep{c, HsPcRes.Ok{f(x), s, hs}}
    case HsPcRep{c, HsPcRes.Bad{e, s}}:
      HsPcRep{c, HsPcRes.Bad{e, s}}

def HsPc.map(-A: Data, -B: Data, f: A -> B, m: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<B>:
  s => HsPc.map.go(A, B, f, m(s))

# m >> n, m <* n, m *> n, x <$ m
def HsPc.then(-A: Data, -B: Data, m: HsPcSt -> HsPcRep<A>, n: HsPcSt -> HsPcRep<B>) -> HsPcSt -> HsPcRep<B>:
  HsPc.bind(A, B, m, _ => n)

def HsPc.left(-A: Data, -B: Data, m: HsPcSt -> HsPcRep<A>, n: HsPcSt -> HsPcRep<B>) -> HsPcSt -> HsPcRep<A>:
  HsPc.bind(A, A, m, x => HsPc.map(B, A, _ => x, n))

def HsPc.const(-A: Data, -B: Data, x: A, m: HsPcSt -> HsPcRep<B>) -> HsPcSt -> HsPcRep<A>:
  HsPc.map(B, A, _ => x, m)

def HsPc.void(-A: Data, m: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<Unit>:
  HsPc.map(A, Unit, _ => Unit{}, m)

# m <|> n: n at the state m began at, if m failed without consuming
def HsPc.alt.n(-A: Data, +err: HsPcError, +ms: HsPcSt, r: HsPcRep<A>) -> HsPcRep<A>:
  match r:
    case HsPcRep{True{}, HsPcRes.Ok{x, s, hs}}:
      HsPcRep{True{}, HsPcRes.Ok{x, s, hs}}
    case HsPcRep{True{}, HsPcRes.Bad{e, s}}:
      HsPcRep{True{}, HsPcRes.Bad{HsPc.err.merge(e, err), HsPc.longest(ms, s)}}
    case HsPcRep{False{}, HsPcRes.Ok{x, +s, hs}}:
      HsPcRep{False{}, HsPcRes.Ok{x, s, HsPc.iset.union(HsPc.hints(HsPc.st.off(s), err), hs)}}
    case HsPcRep{False{}, HsPcRes.Bad{e, s}}:
      HsPcRep{False{}, HsPcRes.Bad{HsPc.err.merge(e, err), HsPc.longest(ms, s)}}

def HsPc.alt.go(-A: Data, r: HsPcRep<A>, n: HsPcSt -> HsPcRep<A>, s: HsPcSt) -> HsPcRep<A>:
  match r:
    case HsPcRep{False{}, HsPcRes.Bad{e, ms}}:
      HsPc.alt.n(A, e, ms, n(s))
    case other:
      other

def HsPc.alt(-A: Data, m: HsPcSt -> HsPcRep<A>, n: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  +s => HsPc.alt.go(A, m(s), n, s)

def HsPc.st.err(+s: HsPcSt, e: HsPcError) -> HsPcRes<Unit>:
  HsPcRes.Bad{e, s}

# empty (mzero): fails where it is, expecting nothing
def HsPc.empty(-A: Data) -> HsPcSt -> HsPcRep<A>:
  +s => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), None{}, Nil{}}, s}}

def HsPc.fail(-A: Data, msg: List<&2, Char>) -> HsPcSt -> HsPcRep<A>:
  +s => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Fancy{HsPc.st.off(s), [HsPcFancy.Fail{msg}]}, s}}

# the parser no run reaches (where Haskell's loops forever)
def HsPc.bottom(-A: Data) -> HsPcSt -> HsPcRep<A>:
  +s => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Fancy{HsPc.st.off(s), Nil{}}, s}}

def HsPc.try.go(-A: Data, r: HsPcRep<A>, +s: HsPcSt) -> HsPcRep<A>:
  match r:
    case HsPcRep{c, HsPcRes.Bad{e, s1}}:
      HsPcRep{False{}, HsPcRes.Bad{e, s}}
    case other:
      other

def HsPc.try(-A: Data, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  +s => HsPc.try.go(A, p(s), s)

# label l p (p <?> l); hidden is label ""
def HsPc.label.refresh(+el: Maybe<&2, HsPcItem>, hs: List<&2, HsPcItem>) -> List<&2, HsPcItem>:
  match el hs:
    case None{} _:
      Nil{}
    case Some{m} Nil{}:
      Nil{}
    case Some{m} _:
      [m]

def HsPc.label.ex(el: Maybe<&2, HsPcItem>) -> List<&2, HsPcItem>:
  match el:
    case None{}:
      Nil{}
    case Some{m}:
      [m]

def HsPc.label.go(-A: Data, +el: Maybe<&2, HsPcItem>, r: HsPcRep<A>) -> HsPcRep<A>:
  match r:
    case HsPcRep{True{}, HsPcRes.Ok{x, s, hs}}:
      HsPcRep{True{}, HsPcRes.Ok{x, s, Bool.pick(List<&2, HsPcItem>, Maybe.is_none(&2, HsPcItem, el), Nil{}, hs)}}
    case HsPcRep{False{}, HsPcRes.Ok{x, s, hs}}:
      HsPcRep{False{}, HsPcRes.Ok{x, s, HsPc.label.refresh(el, hs)}}
    case HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{o, u, ps}, s}}:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{o, u, HsPc.label.ex(el)}, s}}
    case other:
      other

def HsPc.label.of(l: List<&2, Char>) -> Maybe<&2, HsPcItem>:
  match l:
    case Nil{}:
      None{}
    case h <> t:
      Some{HsPcItem.Label{h <> t}}

def HsPc.label(-A: Data, l: List<&2, Char>, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  s => HsPc.label.go(A, HsPc.label.of(l), p(s))

def HsPc.hidden(-A: Data, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  HsPc.label(A, Nil{}, p)

# p <?> l (Text.Megaparsec's): label l p
def HsPc.labelf(-A: Data, p: HsPcSt -> HsPcRep<A>, l: List<&2, Char>) -> HsPcSt -> HsPcRep<A>:
  HsPc.label(A, l, p)

# Tokens ----------------------------------------------------------------------

# the state after one character: a newline starts a line, a tab goes to the
# next multiple of 8 plus 1
def HsPc.col.tab(+c: Nat) -> Nat:
  Nat.sub(Nat.add(c, 8n), Nat.mod(Nat.sub(c, 1n), 8n))

def HsPc.adv(+ch: Char, +rest: List<&2, Char>, +o: Nat, +l: Nat, +c: Nat, +n: List<&2, Char>) -> HsPcSt:
  +k = Char.to_u32(ch)
  Bool.pick(HsPcSt, U32.is_eq(k, 10), HsPcSt{rest, 1n+o, 1n+l, 1n, n}, HsPcSt{rest, 1n+o, l, Bool.pick(Nat, U32.is_eq(k, 9), HsPc.col.tab(c), 1n+c), n})

# token test ps: one character test takes, else the error expecting ps
def HsPc.sat.in(f: Char -> Bool, +ps: List<&2, HsPcItem>, inp: List<&2, Char>, +o: Nat, +l: Nat, +c: Nat, +n: List<&2, Char>) -> HsPcRep<Char>:
  match inp:
    case Nil{}:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{o, Some{HsPcItem.Eoi{}}, ps}, HsPcSt{Nil{}, o, l, c, n}}}
    case +h <> +t:
      HsBool.if(HsPcRep<Char>, f(h), _ => HsPcRep{True{}, HsPcRes.Ok{h, HsPc.adv(h, t, o, l, c, n), Nil{}}}, _ => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{o, Some{HsPcItem.Tokens{[h]}}, ps}, HsPcSt{h <> t, o, l, c, n}}})

def HsPc.sat.go(f: Char -> Bool, +ps: List<&2, HsPcItem>, s: HsPcSt) -> HsPcRep<Char>:
  match s:
    case HsPcSt{i, o, l, c, n}:
      HsPc.sat.in(f, ps, i, o, l, c, n)

def HsPc.satisfy(f: Char -> Bool) -> HsPcSt -> HsPcRep<Char>:
  s => HsPc.sat.go(f, Nil{}, s)

def HsPc.char(+ch: Char) -> HsPcSt -> HsPcRep<Char>:
  s => HsPc.sat.go(x => Char.is_eq(x, ch), [HsPcItem.Tokens{[ch]}], s)

def HsPc.anySingle() -> HsPcSt -> HsPcRep<Char>:
  HsPc.satisfy(_ => True{})

# string (tokens (==)): all of it or nothing consumed
def HsPc.split.take(n: Nat, xs: List<&2, Char>) -> List<&2, Char>:
  match n xs:
    case 1n+k h <> t:
      h <> HsPc.split.take(k, t)
    case _ _:
      Nil{}

def HsPc.split.drop(n: Nat, xs: List<&2, Char>) -> List<&2, Char>:
  match n xs:
    case 1n+k h <> t:
      HsPc.split.drop(k, t)
    case _ ys:
      ys

def HsPc.split.cons(h: Char, a: List<&2, Char>, b: List<&2, Char>) -> Maybe<&2, Sigma<&2, &2, List<&2, Char>, _ => List<&2, Char>>>:
  Some{(h <> a, b)}

def HsPc.split(n: Nat, xs: List<&2, Char>) -> Maybe<&2, Sigma<&2, &2, List<&2, Char>, _ => List<&2, Char>>>:
  match n xs:
    case 0n ys:
      Some{(Nil{}, ys)}
    case 1n+k Nil{}:
      None{}
    case 1n+(+k) h <> +t:
      HsPc.split.cons(h, HsPc.split.take(k, t), HsPc.split.drop(k, t))

# the state after the characters ts
def HsPc.advs(ts: List<&2, Char>, s: HsPcSt) -> HsPcSt:
  match ts s:
    case Nil{} s1:
      s1
    case +h <> t HsPcSt{i, +o, +l, +c, n}:
      HsPc.advs(t, HsPc.adv(h, Nil{}, o, l, c, n))

def HsPc.st.input(s: HsPcSt, i: List<&2, Char>) -> HsPcSt:
  match s:
    case HsPcSt{i0, o, l, c, n}:
      HsPcSt{i, o, l, c, n}

def HsPc.str.cmp(+tts: List<&2, Char>, m: Maybe<&2, Sigma<&2, &2, List<&2, Char>, _ => List<&2, Char>>>, +s: HsPcSt) -> HsPcRep<List<&2, Char>>:
  match m:
    case None{}:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPcItem.Eoi{}}, [HsPcItem.Tokens{tts}]}, s}}
    case Some{(+got, rest)}:
      HsBool.if(HsPcRep<List<&2, Char>>, HsPc.str.eq(tts, got), _ => HsPcRep{Bool.not(List.is_empty(&2, Char, tts)), HsPcRes.Ok{got, HsPc.st.input(HsPc.advs(got, s), rest), Nil{}}}, _ => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPcItem.Tokens{got}}, [HsPcItem.Tokens{tts}]}, s}})

def HsPc.st.inp(s: HsPcSt) -> List<&2, Char>:
  match s:
    case HsPcSt{i, o, l, c, n}:
      i

def HsPc.string(+tts: List<&2, Char>) -> HsPcSt -> HsPcRep<List<&2, Char>>:
  +s => HsPc.str.cmp(tts, HsPc.split(List.length(&2, Char, tts), HsPc.st.inp(s)), s)

def HsPc.eof.in(i: List<&2, Char>, +s: HsPcSt) -> HsPcRep<Unit>:
  match i:
    case Nil{}:
      HsPcRep{False{}, HsPcRes.Ok{Unit{}, s, Nil{}}}
    case h <> t:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPcItem.Tokens{[h]}}, [HsPcItem.Eoi{}]}, s}}

def HsPc.eof() -> HsPcSt -> HsPcRep<Unit>:
  +s => HsPc.eof.in(HsPc.st.inp(s), s)

# what is next, as an error's unexpected item
def HsPc.next.item(i: List<&2, Char>) -> HsPcItem:
  match i:
    case Nil{}:
      HsPcItem.Eoi{}
    case h <> t:
      HsPcItem.Tokens{[h]}

def HsPc.nfb.go(-A: Data, r: HsPcRep<A>, +s: HsPcSt) -> HsPcRep<Unit>:
  match r:
    case HsPcRep{c, HsPcRes.Ok{x, s1, hs}}:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPc.next.item(HsPc.st.inp(s))}, Nil{}}, s}}
    case HsPcRep{c, HsPcRes.Bad{e, s1}}:
      HsPcRep{False{}, HsPcRes.Ok{Unit{}, s, Nil{}}}

def HsPc.notFollowedBy(-A: Data, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<Unit>:
  +s => HsPc.nfb.go(A, p(s), s)

def HsPc.look.go(-A: Data, r: HsPcRep<A>, +s: HsPcSt) -> HsPcRep<A>:
  match r:
    case HsPcRep{c, HsPcRes.Ok{x, s1, hs}}:
      HsPcRep{False{}, HsPcRes.Ok{x, s, Nil{}}}
    case other:
      other

def HsPc.lookAhead(-A: Data, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  +s => HsPc.look.go(A, p(s), s)

def HsPc.getOffset() -> HsPcSt -> HsPcRep<HsInt>:
  +s => HsPcRep{False{}, HsPcRes.Ok{HsInt.Pos{HsPc.st.off(s)}, s, Nil{}}}

def HsPc.st.pos(s: HsPcSt) -> HsPcPos:
  match s:
    case HsPcSt{i, o, l, c, n}:
      HsPcPos{n, l, c}

def HsPc.getSourcePos() -> HsPcSt -> HsPcRep<HsPcPos>:
  +s => HsPcRep{False{}, HsPcRes.Ok{HsPc.st.pos(s), s, Nil{}}}

# takeWhileP and takeWhile1P: the longest prefix f takes
def HsPc.tw.go(~f: Char -> Bool, i: List<&2, Char>, s: HsPcSt, +acc: List<&2, Char>) -> Sigma<&2, &2, List<&2, Char>, _ => HsPcSt>:
  match i s:
    case +h <> +t HsPcSt{i0, +o, +l, +c, +n}:
      HsBool.if(Sigma<&2, &2, List<&2, Char>, _ => HsPcSt>, f(h), _ => HsPc.tw.go(~f, t, HsPc.adv(h, t, o, l, c, n), h <> acc), _ => (List.reverse(&2, Char, acc), HsPcSt{h <> t, o, l, c, n}))
    case Nil{} s1:
      (List.reverse(&2, Char, acc), s1)

def HsPc.tw.hs(ml: Maybe<&2, List<&2, Char>>) -> List<&2, HsPcItem>:
  match ml:
    case Some{h <> t}:
      [HsPcItem.Label{h <> t}]
    case _:
      Nil{}

def HsPc.tw.rep(+hs: List<&2, HsPcItem>, p: Sigma<&2, &2, List<&2, Char>, _ => HsPcSt>) -> HsPcRep<List<&2, Char>>:
  match p:
    case (+ts, s1):
      HsPcRep{Bool.not(List.is_empty(&2, Char, ts)), HsPcRes.Ok{ts, s1, hs}}

def HsPc.takeWhileP(~f: Char -> Bool, ml: Maybe<&2, List<&2, Char>>) -> HsPcSt -> HsPcRep<List<&2, Char>>:
  +s => HsPc.tw.rep(HsPc.tw.hs(ml), HsPc.tw.go(~f, HsPc.st.inp(s), s, Nil{}))

def HsPc.tw1.rep(+hs: List<&2, HsPcItem>, p: Sigma<&2, &2, List<&2, Char>, _ => HsPcSt>, +s: HsPcSt) -> HsPcRep<List<&2, Char>>:
  match p:
    case (Nil{}, s1):
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPc.next.item(HsPc.st.inp(s))}, hs}, s}}
    case (ts, s1):
      HsPcRep{True{}, HsPcRes.Ok{ts, s1, hs}}

def HsPc.takeWhile1P(~f: Char -> Bool, ml: Maybe<&2, List<&2, Char>>) -> HsPcSt -> HsPcRep<List<&2, Char>>:
  +s => HsPc.tw1.rep(HsPc.tw.hs(ml), HsPc.tw.go(~f, HsPc.st.inp(s), s, Nil{}), s)

# Running ------------------------------------------------------------------------

def HsPc.st0(name: List<&2, Char>, inp: List<&2, Char>) -> HsPcSt:
  HsPcSt{inp, 0n, 1n, 1n, name}

def HsPc.run.go(-A: Data, r: HsPcRep<A>, +name: List<&2, Char>, +inp: List<&2, Char>) -> Either<&2, &2, HsPcBundle, A>:
  match r:
    case HsPcRep{c, HsPcRes.Ok{x, s, hs}}:
      Inr{x}
    case HsPcRep{c, HsPcRes.Bad{e, s}}:
      Inl{HsPcBundle{e, inp, name}}

def HsPc.runParser(-A: Data, p: HsPcSt -> HsPcRep<A>, +name: List<&2, Char>, +inp: List<&2, Char>) -> Either<&2, &2, HsPcBundle, A>:
  HsPc.run.go(A, p(HsPc.st0(name, inp)), name, inp)
# a reply no run gives: fuel's default (rule 11), where Haskell's would not
# stop
def HsPc.rep.default(-A: Data) -> HsPcRep<A>:
  HsPcRep{False{}, HsPcRes.Bad{HsPcError.Fancy{0n, Nil{}}, HsPcSt{Nil{}, 0n, 1n, 1n, Nil{}}}}

# optional p = (Just <$> p) <|> pure Nothing (Control.Applicative)
def HsPc.optional(-A: Data, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<Maybe<&2, A>>:
  HsPc.alt(Maybe<&2, A>, HsPc.map(A, Maybe<&2, A>, x => Some{x}, p), HsPc.pure(Maybe<&2, A>, None{}))

# option x p = p <|> pure x
def HsPc.option(-A: Data, x: A, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  HsPc.alt(A, p, HsPc.pure(A, x))

# between open close p = open *> p <* close
def HsPc.between(-O: Data, -C: Data, -A: Data, o: HsPcSt -> HsPcRep<O>, c: HsPcSt -> HsPcRep<C>, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  HsPc.left(A, C, HsPc.then(O, A, o, p), c)

# Text.Megaparsec.Lexer's lexeme spc p = p <* spc and symbol spc = lexeme
# spc . string
def HsPc.lexeme(-A: Data, spc: HsPcSt -> HsPcRep<Unit>, p: HsPcSt -> HsPcRep<A>) -> HsPcSt -> HsPcRep<A>:
  HsPc.left(A, Unit, p, spc)

def HsPc.symbol(spc: HsPcSt -> HsPcRep<Unit>, +w: List<&2, Char>) -> HsPcSt -> HsPcRep<List<&2, Char>>:
  HsPc.left(List<&2, Char>, Unit, HsPc.string(w), spc)

# Char's space1 and space: takeWhile1P / takeWhileP (Just "white space")
# isSpace (HsChar's, GHC's tables)
def HsPc.space1() -> HsPcSt -> HsPcRep<Unit>:
  HsPc.void(List<&2, Char>, HsPc.takeWhile1P(~(c => HsChar.isSpace(c)), Some{String.to_list("white space")}))

def HsPc.space() -> HsPcSt -> HsPcRep<Unit>:
  HsPc.void(List<&2, Char>, HsPc.takeWhileP(~(c => HsChar.isSpace(c)), Some{String.to_list("white space")}))

def HsPc.not.nl(+c: Char) -> Bool:
  Bool.not(U32.is_eq(Char.to_u32(c), 10))

# skipLineComment prefix = string prefix *> void (takeWhileP (Just
# "character") (/= '\n'))
def HsPc.skipLineComment(+w: List<&2, Char>) -> HsPcSt -> HsPcRep<Unit>:
  HsPc.then(List<&2, Char>, Unit, HsPc.string(w), HsPc.void(List<&2, Char>, HsPc.takeWhileP(~(c => HsPc.not.nl(c)), Some{String.to_list("character")})))

# SourcePos's fields, and indentLevel = sourceColumn <$> getSourcePos
def HsPc.pos.name(p: HsPcPos) -> List<&2, Char>:
  match p:
    case HsPcPos{n, l, c}:
      n

def HsPc.pos.line(p: HsPcPos) -> Nat:
  match p:
    case HsPcPos{n, l, c}:
      l

def HsPc.pos.col(p: HsPcPos) -> Nat:
  match p:
    case HsPcPos{n, l, c}:
      c

def HsPc.indentLevel() -> HsPcSt -> HsPcRep<Nat>:
  HsPc.map(HsPcPos, Nat, p => HsPc.pos.col(p), HsPc.getSourcePos())

# incorrectIndent ord ref actual = fancyFailure {ErrorIndentation ord ref
# actual}
def HsPc.incorrectIndent(-A: Data, o: Cmp, r: Nat, a: Nat) -> HsPcSt -> HsPcRep<A>:
  +s => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Fancy{HsPc.st.off(s), [HsPcFancy.Indent{o, r, a}]}, s}}

# decimal = mkNum <$> takeWhile1P (Just "digit") isDigit <?> "integer"
def HsPc.digits(xs: List<&2, Char>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      HsPc.digits(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(Char.to_u32(h), 48))))

def HsPc.decimal() -> HsPcSt -> HsPcRep<HsInt>:
  HsPc.label(HsInt, String.to_list("integer"), HsPc.map(List<&2, Char>, HsInt, ds => HsInt.Pos{HsPc.digits(ds, 0n)}, HsPc.takeWhile1P(~(c => HsChar.isDigit(c)), Some{String.to_list("digit")})))

# unexpected item: fails where it is, the item unexpected
def HsPc.unexpected(-A: Data, +i: HsPcItem) -> HsPcSt -> HsPcRep<A>:
  +s => HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{i}, Nil{}}, s}}

# Text.Megaparsec.Char.Lexer's charLiteral: label "literal character" of
# GHC's readLitChar on the next at most 10 characters (lookAhead (count' 1
# 10 anySingle)), then that many skipped: one character, or a backslash's
# escape (\a \b \f \n \r \t \v \\ \" \', \^X, \NUL .. \DEL and \SP, a
# decimal, \o octal or \x hexadecimal code below 0x110000)
type HsPcLit is Data:
  HsPcLit{c: Char, n: Nat}

def HsPc.lit.one(+c: U32) -> Maybe<&2, HsPcLit>:
  +k = Bool.pick(U32, U32.is_eq(c, 97), 7, Bool.pick(U32, U32.is_eq(c, 98), 8, Bool.pick(U32, U32.is_eq(c, 102), 12, Bool.pick(U32, U32.is_eq(c, 110), 10, Bool.pick(U32, U32.is_eq(c, 114), 13, Bool.pick(U32, U32.is_eq(c, 116), 9, Bool.pick(U32, U32.is_eq(c, 118), 11, Bool.pick(U32, Bool.or(Bool.or(U32.is_eq(c, 92), U32.is_eq(c, 34)), U32.is_eq(c, 39)), c, 1114112))))))))
  Bool.pick(Maybe<&2, HsPcLit>, U32.is_lt(k, 1114112), Some{HsPcLit{Char.from_u32(k), 2n}}, None{})

# the value of a digit in base b, if it is one
def HsPc.lit.dig(+b: U32, +c: U32) -> U32:
  +d = Bool.pick(U32, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), U32.sub(c, 48), Bool.pick(U32, Bool.and(U32.is_ge(c, 97), U32.is_le(c, 102)), U32.sub(c, 87), Bool.pick(U32, Bool.and(U32.is_ge(c, 65), U32.is_le(c, 70)), U32.sub(c, 55), 99)))
  Bool.pick(U32, U32.is_lt(d, b), d, 99)

# the digits at the front, their value capped above the largest code
def HsPc.lit.num(+b: U32, xs: List<&2, Char>, +v: U32, +n: Nat) -> HsPcLit:
  match xs:
    case Nil{}:
      HsPcLit{Char.from_u32(v), n}
    case +h <> t:
      +d = HsPc.lit.dig(b, Char.to_u32(h))
      HsBool.if(HsPcLit, U32.is_lt(d, 99), _ => HsPc.lit.num(b, t, U32.min(U32.add(U32.mul(v, b), d), 1114112), 1n+n), _ => HsPcLit{Char.from_u32(v), n})

def HsPc.lit.code(m: HsPcLit) -> Maybe<&2, HsPcLit>:
  match m:
    case HsPcLit{+c, +n}:
      Bool.pick(Maybe<&2, HsPcLit>, Bool.and(U32.is_lt(Char.to_u32(c), 1114112), Nat.is_gt(n, 0n)), Some{HsPcLit{c, n}}, None{})

def HsPc.lit.at(m: HsPcLit, +k: Nat) -> HsPcLit:
  match m:
    case HsPcLit{c, n}:
      HsPcLit{c, Nat.add(n, k)}

def HsPc.lit.base(+b: U32, xs: List<&2, Char>, +k: Nat) -> Maybe<&2, HsPcLit>:
  Maybe.map(&2, HsPcLit, HsPcLit, m => HsPc.lit.at(m, k), HsPc.lit.code(HsPc.lit.num(b, xs, 0, 0n)))

# \^X: X from @ to _ is its code less 64
def HsPc.lit.ctl(xs: List<&2, Char>) -> Maybe<&2, HsPcLit>:
  match xs:
    case h <> t:
      +k = Char.to_u32(h)
      Bool.pick(Maybe<&2, HsPcLit>, Bool.and(U32.is_ge(k, 64), U32.is_le(k, 95)), Some{HsPcLit{Char.from_u32(U32.sub(k, 64)), 3n}}, None{})
    case Nil{}:
      None{}

# the ASCII control names, SOH before SO (Text.Read.Lex tries it first)
def HsPc.lit.names() -> List<&2, HsPcLit>:
  [HsPcLit{Char.from_u32(0), 3n}, HsPcLit{Char.from_u32(1), 3n}, HsPcLit{Char.from_u32(2), 3n}, HsPcLit{Char.from_u32(3), 3n}, HsPcLit{Char.from_u32(4), 3n}, HsPcLit{Char.from_u32(5), 3n}, HsPcLit{Char.from_u32(6), 3n}, HsPcLit{Char.from_u32(7), 3n}, HsPcLit{Char.from_u32(8), 2n}, HsPcLit{Char.from_u32(9), 2n}, HsPcLit{Char.from_u32(10), 2n}, HsPcLit{Char.from_u32(11), 2n}, HsPcLit{Char.from_u32(12), 2n}, HsPcLit{Char.from_u32(13), 2n}, HsPcLit{Char.from_u32(14), 2n}, HsPcLit{Char.from_u32(15), 2n}, HsPcLit{Char.from_u32(16), 3n}, HsPcLit{Char.from_u32(17), 3n}, HsPcLit{Char.from_u32(18), 3n}, HsPcLit{Char.from_u32(19), 3n}, HsPcLit{Char.from_u32(20), 3n}, HsPcLit{Char.from_u32(21), 3n}, HsPcLit{Char.from_u32(22), 3n}, HsPcLit{Char.from_u32(23), 3n}, HsPcLit{Char.from_u32(24), 3n}, HsPcLit{Char.from_u32(25), 2n}, HsPcLit{Char.from_u32(26), 3n}, HsPcLit{Char.from_u32(27), 3n}, HsPcLit{Char.from_u32(28), 2n}, HsPcLit{Char.from_u32(29), 2n}, HsPcLit{Char.from_u32(30), 2n}, HsPcLit{Char.from_u32(31), 2n}, HsPcLit{Char.from_u32(32), 2n}, HsPcLit{Char.from_u32(127), 3n}]

def HsPc.lit.words() -> List<&2, List<&2, Char>>:
  [String.to_list("NUL"), String.to_list("SOH"), String.to_list("STX"), String.to_list("ETX"), String.to_list("EOT"), String.to_list("ENQ"), String.to_list("ACK"), String.to_list("BEL"), String.to_list("BS"), String.to_list("HT"), String.to_list("LF"), String.to_list("VT"), String.to_list("FF"), String.to_list("CR"), String.to_list("SO"), String.to_list("SI"), String.to_list("DLE"), String.to_list("DC1"), String.to_list("DC2"), String.to_list("DC3"), String.to_list("DC4"), String.to_list("NAK"), String.to_list("SYN"), String.to_list("ETB"), String.to_list("CAN"), String.to_list("EM"), String.to_list("SUB"), String.to_list("ESC"), String.to_list("FS"), String.to_list("GS"), String.to_list("RS"), String.to_list("US"), String.to_list("SP"), String.to_list("DEL")]

def HsPc.lit.prefix(p: List<&2, Char>, xs: List<&2, Char>) -> Bool:
  match p xs:
    case Nil{} _:
      True{}
    case a <> pt b <> xt:
      Bool.and(Char.is_eq(a, b), HsPc.lit.prefix(pt, xt))
    case _ _:
      False{}

def HsPc.lit.name(ws: List<&2, List<&2, Char>>, ls: List<&2, HsPcLit>, +xs: List<&2, Char>) -> Maybe<&2, HsPcLit>:
  match ws ls:
    case w <> wt HsPcLit{c, n} <> lt:
      HsBool.if(Maybe<&2, HsPcLit>, HsPc.lit.prefix(w, xs), _ => Some{HsPcLit{c, 1n+n}}, _ => HsPc.lit.name(wt, lt, xs))
    case _ _:
      None{}

def HsPc.lit.esc(+h: Char, +t: List<&2, Char>) -> Maybe<&2, HsPcLit>:
  +k = Char.to_u32(h)
  Bool.pick(Maybe<&2, HsPcLit>, Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57)), HsPc.lit.base(10, h <> t, 1n), Bool.pick(Maybe<&2, HsPcLit>, U32.is_eq(k, 111), HsPc.lit.base(8, t, 2n), Bool.pick(Maybe<&2, HsPcLit>, U32.is_eq(k, 120), HsPc.lit.base(16, t, 2n), Bool.pick(Maybe<&2, HsPcLit>, U32.is_eq(k, 94), HsPc.lit.ctl(t), Maybe.or(&2, HsPcLit, HsPc.lit.one(k), HsPc.lit.name(HsPc.lit.words(), HsPc.lit.names(), h <> t))))))

def HsPc.lit.after(xs: List<&2, Char>) -> Maybe<&2, HsPcLit>:
  match xs:
    case +h <> +t:
      HsPc.lit.esc(h, t)
    case Nil{}:
      None{}

def HsPc.lit.read(xs: List<&2, Char>) -> Maybe<&2, HsPcLit>:
  match xs:
    case +h <> t:
      Bool.pick(Maybe<&2, HsPcLit>, U32.is_eq(Char.to_u32(h), 92), HsPc.lit.after(t), Some{HsPcLit{h, 1n}})
    case Nil{}:
      None{}

def HsPc.lit.got(m: Maybe<&2, HsPcLit>, +inp: List<&2, Char>, +s: HsPcSt) -> HsPcRep<Char>:
  match m inp:
    case Some{HsPcLit{c, +n}} _:
      HsPcRep{True{}, HsPcRes.Ok{c, HsPc.st.input(HsPc.advs(HsPc.split.take(n, inp), s), HsPc.split.drop(n, inp)), Nil{}}}
    case None{} h <> t:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPcItem.Tokens{[h]}}, [HsPcItem.Label{String.to_list("literal character")}]}, s}}
    case None{} Nil{}:
      HsPcRep{False{}, HsPcRes.Bad{HsPcError.Trivial{HsPc.st.off(s), Some{HsPcItem.Eoi{}}, [HsPcItem.Label{String.to_list("literal character")}]}, s}}

def HsPc.charLiteral() -> HsPcSt -> HsPcRep<Char>:
  +s => HsPc.lit.got(HsPc.lit.read(HsPc.split.take(10n, HsPc.st.inp(s))), HsPc.st.inp(s), s)

# Pos and Int: unPos
def HsPc.unPos(n: Nat) -> HsInt:
  HsInt.Pos{n}

# errorBundlePretty ----------------------------------------------------------

# where an offset is: its line and column, the line up to it, reversed,
# and the input from it
type HsPcAt is Data:
  HsPcAt{line: Nat, col: Nat, pre: List<&2, Char>, post: List<&2, Char>}

def HsPc.pp.walk(n: Nat, xs: List<&2, Char>, +l: Nat, +c: Nat, +acc: List<&2, Char>) -> HsPcAt:
  match n xs:
    case 1n+k +h <> t:
      +u = Char.to_u32(h)
      +nl = U32.is_eq(u, 10)
      HsPc.pp.walk(k, t, Bool.pick(Nat, nl, 1n+l, l), Bool.pick(Nat, nl, 1n, Bool.pick(Nat, U32.is_eq(u, 9), HsPc.col.tab(c), 1n+c)), Bool.pick(List<&2, Char>, nl, Nil{}, h <> acc))
    case _ ys:
      HsPcAt{l, c, acc, ys}

def HsPc.pp.line(xs: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case +h <> t:
      HsBool.if(List<&2, Char>, U32.is_eq(Char.to_u32(h), 10), _ => Nil{}, _ => h <> HsPc.pp.line(t))
    case Nil{}:
      Nil{}

# expandTab 8
def HsPc.pp.tabs(xs: List<&2, Char>, +i: Nat) -> List<&2, Char>:
  match xs:
    case +h <> t:
      +k = Nat.sub(8n, Nat.mod(i, 8n))
      +tab = U32.is_eq(Char.to_u32(h), 9)
      List.append(&2, Char, Bool.pick(List<&2, Char>, tab, List.replicate(Char, k, ' '), [h]), HsPc.pp.tabs(t, Bool.pick(Nat, tab, Nat.add(i, k), 1n+i)))
    case Nil{}:
      Nil{}

def HsPc.pp.nonempty(xs: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      String.to_list("<empty line>")
    case h <> t:
      h <> t

def HsPc.pp.str(+s: String) -> List<&2, Char>:
  String.to_list(s)

def HsPc.pp.nat(+n: Nat) -> List<&2, Char>:
  String.to_list(Nat.show(n))

# charPretty' (Text.Megaparsec.Stream)
def HsPc.pp.names() -> List<&2, String>:
  ["null", "start of heading", "start of text", "end of text", "end of transmission", "enquiry", "acknowledge", "bell", "backspace", "tab", "newline", "vertical tab", "form feed", "carriage return", "shift out", "shift in", "data link escape", "device control one", "device control two", "device control three", "device control four", "negative acknowledge", "synchronous idle", "end of transmission block", "cancel", "end of medium", "substitute", "escape", "file separator", "group separator", "record separator", "unit separator"]

def HsPc.pp.nth(xs: List<&2, String>, n: Nat) -> List<&2, Char>:
  match xs n:
    case h <> t 0n:
      String.to_list(h)
    case h <> t 1n+k:
      HsPc.pp.nth(t, k)
    case Nil{} _:
      Nil{}

def HsPc.pp.cname(+c: Char) -> Maybe<&2, List<&2, Char>>:
  +k = Char.to_u32(c)
  Bool.pick(Maybe<&2, List<&2, Char>>, U32.is_lt(k, 32), Some{HsPc.pp.nth(HsPc.pp.names(), U32.to_nat(k))}, Bool.pick(Maybe<&2, List<&2, Char>>, U32.is_eq(k, 127), Some{String.to_list("delete")}, Bool.pick(Maybe<&2, List<&2, Char>>, U32.is_eq(k, 160), Some{String.to_list("non-breaking space")}, None{})))

def HsPc.pp.char.at(m: Maybe<&2, List<&2, Char>>, +c: Char) -> List<&2, Char>:
  match m:
    case Some{n}:
      n
    case None{}:
      ['\'', c, '\'']

def HsPc.pp.char(+c: Char) -> List<&2, Char>:
  Bool.pick(List<&2, Char>, U32.is_eq(Char.to_u32(c), 32), String.to_list("space"), HsPc.pp.char.at(HsPc.pp.cname(c), c))

def HsPc.pp.inner.at(m: Maybe<&2, List<&2, Char>>, +c: Char) -> List<&2, Char>:
  match m:
    case Some{n}:
      List.append(&2, Char, '<' <> n, ['>'])
    case None{}:
      [c]

def HsPc.pp.inner(xs: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case +h <> t:
      List.append(&2, Char, HsPc.pp.inner.at(HsPc.pp.cname(h), h), HsPc.pp.inner(t))
    case Nil{}:
      Nil{}

def HsPc.pp.crlf(xs: List<&2, Char>) -> Bool:
  match xs:
    case a <> b <> Nil{}:
      Bool.and(U32.is_eq(Char.to_u32(a), 13), U32.is_eq(Char.to_u32(b), 10))
    case _:
      False{}

# stringPretty
def HsPc.pp.tokens(+xs: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case +h <> Nil{}:
      HsPc.pp.char(h)
    case ys:
      Bool.pick(List<&2, Char>, HsPc.pp.crlf(ys), String.to_list("crlf newline"), List.append(&2, Char, '"' <> HsPc.pp.inner(ys), ['"']))

def HsPc.pp.item(i: HsPcItem) -> List<&2, Char>:
  match i:
    case HsPcItem.Tokens{ts}:
      HsPc.pp.tokens(ts)
    case HsPcItem.Label{l}:
      l
    case HsPcItem.Eoi{}:
      String.to_list("end of input")

def HsPc.pp.items(xs: List<&2, HsPcItem>, acc: List<&2, List<&2, Char>>) -> List<&2, List<&2, Char>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      HsPc.pp.items(t, HsPc.sset.ins(HsPc.pp.item(h), acc))

def HsPc.pp.commas(xs: List<&2, List<&2, Char>>) -> List<&2, Char>:
  match xs:
    case x <> Nil{}:
      List.append(&2, Char, String.to_list("or "), x)
    case x <> y <> t:
      List.concat(&2, Char, [x, String.to_list(", "), HsPc.pp.commas(y <> t)])
    case Nil{}:
      Nil{}

# orList
def HsPc.pp.or(xs: List<&2, List<&2, Char>>) -> List<&2, Char>:
  match xs:
    case x <> Nil{}:
      x
    case x <> y <> Nil{}:
      List.concat(&2, Char, [x, String.to_list(" or "), y])
    case x <> y <> z <> t:
      List.concat(&2, Char, [x, String.to_list(", "), HsPc.pp.commas(y <> z <> t)])
    case Nil{}:
      Nil{}

def HsPc.pp.msg(+pre: String, xs: List<&2, List<&2, Char>>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      List.concat(&2, Char, [String.to_list(pre), HsPc.pp.or(h <> t), ['\n']])

def HsPc.pp.un(u: Maybe<&2, HsPcItem>) -> List<&2, HsPcItem>:
  match u:
    case None{}:
      Nil{}
    case Some{i}:
      [i]

def HsPc.pp.cmpword(o: Cmp) -> List<&2, Char>:
  match o:
    case LT{}:
      String.to_list("less than ")
    case EQ{}:
      String.to_list("equal to ")
    case GT{}:
      String.to_list("greater than ")

def HsPc.pp.fancy(f: HsPcFancy) -> List<&2, Char>:
  match f:
    case HsPcFancy.Fail{m}:
      m
    case HsPcFancy.Indent{o, r, a}:
      List.concat(&2, Char, [String.to_list("incorrect indentation (got "), HsPc.pp.nat(a), String.to_list(", should be "), HsPc.pp.cmpword(o), HsPc.pp.nat(r), [')']])

def HsPc.pp.unlines(xs: List<&2, HsPcFancy>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      List.concat(&2, Char, [HsPc.pp.fancy(h), ['\n'], HsPc.pp.unlines(t)])

def HsPc.pp.trivial(u: Maybe<&2, HsPcItem>, ps: List<&2, HsPcItem>) -> List<&2, Char>:
  match u ps:
    case None{} Nil{}:
      String.to_list("unknown parse error\n")
    case un es:
      List.append(&2, Char, HsPc.pp.msg("unexpected ", HsPc.pp.items(HsPc.pp.un(un), Nil{})), HsPc.pp.msg("expecting ", HsPc.pp.items(es, Nil{})))

# parseErrorTextPretty
def HsPc.pp.text(e: HsPcError) -> List<&2, Char>:
  match e:
    case HsPcError.Trivial{o, u, ps}:
      HsPc.pp.trivial(u, ps)
    case HsPcError.Fancy{o, Nil{}}:
      String.to_list("unknown fancy parse error\n")
    case HsPcError.Fancy{o, xs}:
      HsPc.pp.unlines(xs)

# the pointer's length: the unexpected item's (tokens: their number), else 1
def HsPc.pp.elen(e: HsPcError) -> Nat:
  match e:
    case HsPcError.Trivial{o, Some{HsPcItem.Tokens{ts}}, ps}:
      List.length(&2, Char, ts)
    case _:
      1n

def HsPc.pp.where(+name: List<&2, Char>, +l: Nat, +c: Nat) -> List<&2, Char>:
  +lc = List.concat(&2, Char, [HsPc.pp.nat(l), [':'], HsPc.pp.nat(c)])
  Bool.pick(List<&2, Char>, List.is_empty(&2, Char, name), lc, List.concat(&2, Char, [name, [':'], lc]))

def HsPc.pp.at(+name: List<&2, Char>, a: HsPcAt, +e: HsPcError) -> List<&2, Char>:
  match a:
    case HsPcAt{+l, +c, pre, post}:
      +sline = HsPc.pp.nonempty(HsPc.pp.tabs(List.append(&2, Char, List.reverse(&2, Char, pre), HsPc.pp.line(post)), 0n))
      +rpshift = Nat.sub(c, 1n)
      +slen = List.length(&2, Char, sline)
      +elen = HsPc.pp.elen(e)
      +plen = Bool.pick(Nat, Nat.is_gt(Nat.add(rpshift, elen), slen), Nat.sub(1n+slen, rpshift), elen)
      +lnum = HsPc.pp.nat(l)
      +pad = List.replicate(Char, 1n+List.length(&2, Char, lnum), ' ')
      +rpad = Bool.pick(List<&2, Char>, Nat.is_gt(plen, 0n), List.replicate(Char, rpshift, ' '), Nil{})
      List.concat(&2, Char, [HsPc.pp.where(name, l, c), String.to_list(":\n"), pad, String.to_list("|\n"), lnum, String.to_list(" | "), sline, ['\n'], pad, String.to_list("| "), rpad, List.replicate(Char, plen, '^'), ['\n'], HsPc.pp.text(e)])

# errorBundlePretty, for a bundle of one error (runParser's)
def HsPc.errorBundlePretty(b: HsPcBundle) -> List<&2, Char>:
  match b:
    case HsPcBundle{+e, inp, +name}:
      HsPc.pp.at(name, HsPc.pp.walk(HsPc.err.off(e), inp, 1n, 1n, Nil{}), e)

