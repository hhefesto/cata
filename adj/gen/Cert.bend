# adj/gen/Cert.bend: one step of a certificate's proof.  A certificate
# (Gen.bend's cert) states that cata's own Bend def answers, at every input,
# what the model's meaning of the Haskell program answers.  Its leaves are
# L.refl(A), A the model's side: Bend checks a leaf when both sides compute
# to the same.  Where one does not, Bend's error prints the goal, L.Le(A, B),
# computed as far as it goes; this program reads it, takes the first part
# that is stuck, and writes the proof one step on: a split of a Bool, a
# pair, a sum, a divisor, or an induction on a list for a fold.  Nothing
# here is trusted: the steps are Bend, and Bend's kernel checks them.
#   cert step N FILE LOG (NAME=FILE)...   FILE with the failing leaf of LOG
#       refined, N its helpers' number, and the files its names are from
# Run by adj/gen/cert.zsh.

import Base

def cat(xs: List<&2, String>) -> String:
  String.concat(xs)

def if.at(-A: Type, c: Bool, t: Unit -> A, e: Unit -> A) -> A:
  match c:
    case True{}:
      t(Unit{})
    case False{}:
      e(Unit{})

# terms as Bend prints them -------------------------------------------------------

# a name or a literal; an application, k its bracket ("(", "{" or "<"), its
# arguments a chain of TArg; a lambda; 1n+x; an equation
type Tm is Data:
  TId{n: String}
  TApp{k: Nat, h: Tm, as: Tm}
  TLam{x: String, b: Tm}
  TAdd{a: Tm, b: Tm}
  TEqn{a: Tm, b: Tm, t: Tm}
  TArg{x: Tm, r: Tm}
  TEnd{}

def tm.eq(a: Tm, b: Tm) -> Bool:
  match a b:
    case TId{x} TId{y}:
      String.eq(x, y)
    case TApp{k, h, x} TApp{l, i, y}:
      Bool.and(Nat.is_eq(k, l), Bool.and(tm.eq(h, i), tm.eq(x, y)))
    case TLam{x, b} TLam{y, c}:
      Bool.and(String.eq(x, y), tm.eq(b, c))
    case TAdd{x, y} TAdd{u, v}:
      Bool.and(tm.eq(x, u), tm.eq(y, v))
    case TEqn{x, y, z} TEqn{u, v, w}:
      Bool.and(tm.eq(x, u), Bool.and(tm.eq(y, v), tm.eq(z, w)))
    case TArg{x, y} TArg{u, v}:
      Bool.and(tm.eq(x, u), tm.eq(y, v))
    case TEnd{} TEnd{}:
      True{}
    case _ _:
      False{}

# tokens --------------------------------------------------------------------------

def is.id(+c: Char) -> Bool:
  +n = {Char.to_u32(c) : U32}
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c), Bool.or(U32.is_eq(n, 95), Bool.or(U32.is_eq(n, 46), Bool.or(U32.is_eq(n, 38), Bool.or(U32.is_eq(n, 47), U32.is_eq(n, 94)))))))

# the word read so far (reversed) goes before the tokens
def flush(w: List<&2, Char>, r: List<&2, String>) -> List<&2, String>:
  match w:
    case Nil{}:
      r
    case Con{c, t}:
      String.from_list(List.reverse(&2, Char, Con{c, t})) <> r

# a character and its kind: a name's, a space, a quote, another
type Cl is Data:
  CId{}
  CSp{}
  CDq{}
  CSq{}
  CPu{}

type Cc is Data:
  Cc{c: Char, k: Cl}

def cl(+c: Char) -> Cl:
  +n = {Char.to_u32(c) : U32}
  if.at(Cl, is.id(c), _ => CId{}, _ => if.at(Cl, Char.is_space(c), _ => CSp{}, _ => if.at(Cl, U32.is_eq(n, 34), _ => CDq{}, _ => if.at(Cl, U32.is_eq(n, 39), _ => CSq{}, _ => CPu{}))))

def ccs(cs: List<&2, Char>) -> List<&2, Cc>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Cc{c, cl(c)} <> ccs(t)

type Lx is Data:
  LxN{}
  LxD{}
  LxS{}

def lex(cs: List<&2, Cc>, m: Lx, w: List<&2, Char>) -> List<&2, String>:
  match cs m:
    case Nil{} _:
      flush(w, Nil{})
    case Con{Cc{c, CId{}}, t} LxN{}:
      lex(t, LxN{}, c <> w)
    case Con{Cc{c, CSp{}}, t} LxN{}:
      flush(w, lex(t, LxN{}, Nil{}))
    case Con{Cc{c, CDq{}}, t} LxN{}:
      flush(w, lex(t, LxD{}, [c]))
    case Con{Cc{c, CSq{}}, t} LxN{}:
      flush(w, lex(t, LxS{}, [c]))
    case Con{Cc{c, CPu{}}, t} LxN{}:
      flush(w, String.from_list([c]) <> lex(t, LxN{}, Nil{}))
    case Con{Cc{c, CDq{}}, t} LxD{}:
      flush(c <> w, lex(t, LxN{}, Nil{}))
    case Con{Cc{c, CSq{}}, t} LxS{}:
      flush(c <> w, lex(t, LxN{}, Nil{}))
    case Con{Cc{c, _}, t} k:
      lex(t, k, c <> w)

def toks(s: String) -> List<&2, String>:
  lex(ccs(String.to_list(s)), LxN{}, Nil{})

# the parser ----------------------------------------------------------------------

type Pr is Data:
  Pr{t: Tm, r: List<&2, String>}

def pr.t(p: Pr) -> Tm:
  match p:
    case Pr{t, r}:
      t

def pr.r(p: Pr) -> List<&2, String>:
  match p:
    case Pr{t, r}:
      r

# a term; the arguments up to a bracket; what follows a term
type Pk is Data:
  PkT{}
  PkA{close: String}
  PkP{cur: Tm}

def pr.arg2(t: Tm, b: Pr) -> Pr:
  match b:
    case Pr{u, r}:
      Pr{TArg{t, u}, r}

# an argument, and those after it
def pr.arg(a: Pr, k: List<&2, String> -> Pr) -> Pr:
  match a:
    case Pr{t, r}:
      pr.arg2(t, k(r))

# (a, b, c) is Tuple{a, Tuple{b, c}}
def tup.t(as: Tm) -> Tm:
  match as:
    case TArg{x, TEnd{}}:
      x
    case TArg{x, r}:
      TApp{1n, TId{"Tuple"}, TArg{x, TArg{tup.t(r), TEnd{}}}}
    case u:
      u

def tup(a: Pr, k: Tm -> List<&2, String> -> Pr) -> Pr:
  match a:
    case Pr{t, r}:
      k(tup.t(t), r)

# [a, b] is Con{a, Con{b, Nil{}}}
def lst.t(as: Tm) -> Tm:
  match as:
    case TArg{x, r}:
      TApp{1n, TId{"Con"}, TArg{x, TArg{lst.t(r), TEnd{}}}}
    case _:
      TApp{1n, TId{"Nil"}, TEnd{}}

def tup2(a: Pr, k: Tm -> List<&2, String> -> Pr) -> Pr:
  match a:
    case Pr{t, r}:
      k(lst.t(t), r)

def skip(n: Nat, ts: List<&2, String>) -> List<&2, String>:
  List.drop(&2, String, ts, n)

def px(+fuel: Nat, k: Pk, +ts: List<&2, String>) -> Pr:
  match fuel:
    case 0n:
      Pr{TEnd{}, ts}
    case 1n+f:
      match k:
        case PkT{}:
          match ts:
            case "{" <> +r:
              +a = px(f, PkT{}, r)
              +b = px(f, PkT{}, skip(2n, pr.r(a)))
              +t = px(f, PkT{}, skip(1n, pr.r(b)))
              Pr{TEqn{pr.t(a), pr.t(b), pr.t(t)}, skip(1n, pr.r(t))}
            case "[" <> +r:
              tup2(px(f, PkA{"]"}, r), t => ts2 => px(f, PkP{t}, ts2))
            case "(" <> +r:
              tup(px(f, PkA{")"}, r), t => ts2 => px(f, PkP{t}, ts2))
            case "+" <> +x <> "=" <> ">" <> +r:
              +b = px(f, PkT{}, r)
              Pr{TLam{x, pr.t(b)}, pr.r(b)}
            case +x <> "=" <> ">" <> +r:
              +b = px(f, PkT{}, r)
              Pr{TLam{x, pr.t(b)}, pr.r(b)}
            case +x <> +r:
              px(f, PkP{TId{x}}, r)
            case Nil{}:
              Pr{TEnd{}, Nil{}}
        case PkP{+cur}:
          match ts:
            case "(" <> +r:
              +a = px(f, PkA{")"}, r)
              px(f, PkP{TApp{0n, cur, pr.t(a)}}, pr.r(a))
            case "{" <> +r:
              +a = px(f, PkA{"}"}, r)
              px(f, PkP{TApp{1n, cur, pr.t(a)}}, pr.r(a))
            case "<" <> ">" <> +r:
              +a = px(f, PkT{}, r)
              Pr{TApp{1n, TId{"Con"}, TArg{cur, TArg{pr.t(a), TEnd{}}}}, pr.r(a)}
            case "<" <> +r:
              +a = px(f, PkA{">"}, r)
              px(f, PkP{TApp{2n, cur, pr.t(a)}}, pr.r(a))
            case "+" <> +r:
              +a = px(f, PkT{}, r)
              Pr{TAdd{cur, pr.t(a)}, pr.r(a)}
            case u:
              Pr{cur, u}
        case PkA{+close}:
          match ts:
            case "," <> +r:
              px(f, PkA{close}, r)
            case +x <> +r:
              if.at(Pr, String.eq(x, close), _ => Pr{TEnd{}, r}, _ => pr.arg(px(f, PkT{}, x <> r), ts2 => px(f, PkA{close}, ts2)))
            case Nil{}:
              Pr{TEnd{}, Nil{}}

def parse(s: String) -> Tm:
  +ts = {toks(s) : List<&2, String>}
  pr.t(px(Nat.add(8n, Nat.mul(2n, List.length(&2, String, ts))), PkT{}, ts))

# Bend prints a variable hidden by k inner ones of its name as v^(k+1): each
# lambda's variable that hides one its body names gets a name of its own
type Sc is Data:
  Sc{n: String, u: String}

def sc.look(sc: List<&2, Sc>, +n: String, k: Nat, +d: String) -> String:
  match sc k:
    case Con{Sc{+m, +u}, t} 1n:
      if.at(String, String.eq(m, n), _ => u, _ => sc.look(t, n, 1n, d))
    case Con{Sc{+m, u}, t} 2n+(+j):
      sc.look(t, n, Bool.pick(Nat, String.eq(m, n), 1n+j, 2n+j), d)
    case _ _:
      d

def sc.has(sc: List<&2, Sc>, +n: String) -> Bool:
  match sc:
    case Con{Sc{m, u}, t}:
      Bool.or(String.eq(m, n), sc.has(t, n))
    case Nil{}:
      False{}

def or.one(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      1n

def hat.k(ps: List<&2, String>) -> Nat:
  match ps:
    case Con{a, Con{k, t}}:
      or.one(Nat.read(k))
    case _:
      1n

def hat.n(ps: List<&2, String>) -> String:
  match ps:
    case Con{a, t}:
      a
    case Nil{}:
      ""

def own.name(hid: Bool, +x: String, +sc: List<&2, Sc>) -> String:
  match hid:
    case True{}:
      cat([x, "z", Nat.show(List.length(&2, Sc, sc))])
    case False{}:
      x

# whether t names a hidden x
def hat.in(t: Tm, +p: String) -> Bool:
  match t:
    case TId{n}:
      String.starts_with(n, p)
    case TApp{k, h, as}:
      Bool.or(hat.in(h, p), hat.in(as, p))
    case TLam{x, b}:
      hat.in(b, p)
    case TAdd{a, b}:
      Bool.or(hat.in(a, p), hat.in(b, p))
    case TEqn{a, b, c}:
      Bool.or(hat.in(a, p), Bool.or(hat.in(b, p), hat.in(c, p)))
    case TArg{a, r}:
      Bool.or(hat.in(a, p), hat.in(r, p))
    case TEnd{}:
      False{}

def names(t: Tm, +sc: List<&2, Sc>) -> Tm:
  match t:
    case TId{+n}:
      +ps = {String.split(n, '^') : List<&2, String>}
      TId{sc.look(sc, hat.n(ps), hat.k(ps), hat.n(ps))}
    case TApp{k, h, as}:
      TApp{k, names(h, sc), names(as, sc)}
    case TLam{+x, +b}:
      +u = {own.name(Bool.and(sc.has(sc, x), hat.in(b, cat([x, "^"]))), x, sc) : String}
      TLam{u, names(b, Sc{x, u} <> sc)}
    case TAdd{a, b}:
      TAdd{names(a, sc), names(b, sc)}
    case TEqn{a, b, c}:
      TEqn{names(a, sc), names(b, sc), names(c, sc)}
    case TArg{a, r}:
      TArg{names(a, sc), names(r, sc)}
    case TEnd{}:
      TEnd{}

# the names' signatures -------------------------------------------------------------

# a def's name (under its file's), how many of its parameters are templates,
# its parameters' names, its answer's type
type Sg is Data:
  Sg{n: String, k: Nat, ps: List<&2, String>, r: Tm}

def sg.find(ss: List<&2, Sg>, +n: String) -> Maybe<&2, Sg>:
  match ss:
    case Nil{}:
      None{}
    case Con{Sg{+m, k, ps, r}, t}:
      if.at(Maybe<&2, Sg>, String.eq(m, n), _ => Some{Sg{m, k, ps, r}}, _ => sg.find(t, n))

def sg.k(m: Maybe<&2, Sg>) -> Nat:
  match m:
    case Some{Sg{n, k, ps, r}}:
      k
    case None{}:
      0n

# the text up to a string, and after it
def upto(fuel: Nat, +s: String, +p: String, +acc: String) -> String:
  match fuel:
    case 0n:
      String.reverse(acc)
    case 1n+f:
      if.at(String, String.starts_with(s, p), _ => String.reverse(acc), _ => upto(f, String.drop(s, 1n), p, String.append(String.take(s, 1n), acc)))

def after(fuel: Nat, +s: String, +p: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      if.at(String, String.starts_with(s, p), _ => String.drop(s, String.length(p)), _ => after(f, String.drop(s, 1n), p))

def before(+s: String, +p: String) -> String:
  upto(String.length(s), s, p, "")

def past(+s: String, +p: String) -> String:
  after(String.length(s), s, p)

def past.last(fuel: Nat, +s: String, +p: String) -> String:
  match fuel:
    case 0n:
      s
    case 1n+f:
      if.at(String, String.contains(s, p), _ => past.last(f, past(s, p), p), _ => s)

def count.go(s: String, +c: Char) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{x, +t}:
      if.at(Nat, Char.is_eq(x, c), _ => 1n+count.go(t, c), _ => count.go(t, c))

# the names before a ":" at each "," of the parameters (a type's own commas
# have no ":" before the next one, or are in a bracket: the parameters'
# names alone are asked for, by position, of a template)
def ps.names(ts: List<&2, String>, +d: Nat) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case "(" <> t:
      ps.names(t, 1n+d)
    case ")" <> t:
      ps.names(t, Nat.sub(d, 1n))
    case "<" <> t:
      ps.names(t, 1n+d)
    case "=" <> ">" <> t:
      ps.names(t, d)
    case "-" <> ">" <> t:
      ps.names(t, d)
    case ">" <> t:
      ps.names(t, Nat.sub(d, 1n))
    case +x <> ":" <> +t:
      if.at(List<&2, String>, Nat.is_eq(d, 1n), _ => x <> ps.names(t, 1n), _ => ps.names(t, d))
    case _ <> t:
      ps.names(t, d)

def sg.line(+p: String, +l: String) -> Sg:
  +s = {String.drop(l, 4n) : String}
  +nm = {before(s, "(") : String}
  +res = {String.reverse(String.drop(String.reverse(past.last(40n, s, ") -> ")), 1n)) : String}
  Sg{cat([p, ".", nm]), count.go(s, '~'), ps.names(toks(String.drop(s, String.length(nm))), 0n), parse(res)}

def sg.lines(ls: List<&2, String>, +p: String, +r: List<&2, Sg>) -> List<&2, Sg>:
  match ls:
    case Nil{}:
      r
    case Con{+l, +t}:
      if.at(List<&2, Sg>, String.starts_with(l, "def "), _ => sg.line(p, l) <> sg.lines(t, p, r), _ => sg.lines(t, p, r))

# printing --------------------------------------------------------------------------

def open(k: Nat) -> String:
  match k:
    case 0n:
      "("
    case 1n:
      "{"
    case _:
      "<"

def close(k: Nat) -> String:
  match k:
    case 0n:
      ")"
    case 1n:
      "}"
    case _:
      ">"

def id.of(t: Tm) -> String:
  match t:
    case TId{n}:
      n
    case _:
      ""

type Sh is Data:
  ShT{}
  ShA{k: Nat, first: Bool}

def sep(first: Bool) -> String:
  match first:
    case True{}:
      ""
    case False{}:
      ", "

def tilde(k: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+j:
      "~"

# the times x is free in t
def occ(t: Tm, +x: String) -> Nat:
  match t:
    case TId{n}:
      if.at(Nat, String.eq(n, x), _ => 1n, _ => 0n)
    case TApp{k, h, as}:
      Nat.add(occ(h, x), occ(as, x))
    case TLam{y, +b}:
      if.at(Nat, String.eq(y, x), _ => 0n, _ => occ(b, x))
    case TAdd{a, b}:
      Nat.add(occ(a, x), occ(b, x))
    case TEqn{a, b, c}:
      Nat.add(occ(a, x), Nat.add(occ(b, x), occ(c, x)))
    case TArg{a, r}:
      Nat.add(occ(a, x), occ(r, x))
    case TEnd{}:
      0n

# a lambda's variable used more than once is marked
def lam.mark(many: Bool) -> String:
  match many:
    case True{}:
      "+"
    case False{}:
      ""

# a term's text, a template's arguments with ~
def sh(t: Tm, m: Sh, +ss: List<&2, Sg>) -> String:
  match t m:
    case TId{n} _:
      n
    case TApp{+k, +h, as} _:
      +ks = {if.at(Nat, Nat.is_eq(k, 0n), _ => sg.k(sg.find(ss, id.of(h))), _ => 0n) : Nat}
      cat([sh(h, ShT{}, ss), open(k), sh(as, ShA{ks, True{}}, ss), close(k)])
    case TLam{+x, +b} _:
      cat([lam.mark(Nat.is_gt(occ(b, x), 1n)), x, " => ", sh(b, ShT{}, ss)])
    case TAdd{a, b} _:
      cat([sh(a, ShT{}, ss), "+", sh(b, ShT{}, ss)])
    case TEqn{a, b, c} _:
      cat(["{", sh(a, ShT{}, ss), " == ", sh(b, ShT{}, ss), " : ", sh(c, ShT{}, ss), "}"])
    case TArg{x, r} ShA{+k, first}:
      cat([sep(first), tilde(k), sh(x, ShT{}, ss), sh(r, ShA{Nat.sub(k, 1n), False{}}, ss)])
    case TArg{x, r} ShT{}:
      "?"
    case TEnd{} _:
      ""

# names in terms ----------------------------------------------------------------------

# whether x is free in t
def free(t: Tm, +x: String) -> Bool:
  match t:
    case TId{n}:
      String.eq(n, x)
    case TApp{k, h, as}:
      Bool.or(free(h, x), free(as, x))
    case TLam{y, b}:
      if.at(Bool, String.eq(y, x), _ => False{}, _ => free(b, x))
    case TAdd{a, b}:
      Bool.or(free(a, x), free(b, x))
    case TEqn{a, b, c}:
      Bool.or(free(a, x), Bool.or(free(b, x), free(c, x)))
    case TArg{a, r}:
      Bool.or(free(a, x), free(r, x))
    case TEnd{}:
      False{}

def anyfree(xs: List<&2, String>, +t: Tm) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.or(free(t, x), anyfree(r, t))

# v for the name x (x's lambdas hide it)
def sub(t: Tm, +x: String, +v: Tm) -> Tm:
  match t:
    case TId{+n}:
      if.at(Tm, String.eq(n, x), _ => v, _ => TId{n})
    case TApp{k, h, as}:
      TApp{k, sub(h, x, v), sub(as, x, v)}
    case TLam{+y, +b}:
      if.at(Tm, String.eq(y, x), _ => TLam{y, b}, _ => TLam{y, sub(b, x, v)})
    case TAdd{a, b}:
      TAdd{sub(a, x, v), sub(b, x, v)}
    case TEqn{a, b, c}:
      TEqn{sub(a, x, v), sub(b, x, v), sub(c, x, v)}
    case TArg{a, r}:
      TArg{sub(a, x, v), sub(r, x, v)}
    case TEnd{}:
      TEnd{}

# v for each part of t that is p
def rep(+t: Tm, +p: Tm, +v: Tm) -> Tm:
  match t:
    case TId{+n}:
      if.at(Tm, tm.eq(TId{n}, p), _ => v, _ => TId{n})
    case TApp{+k, +h, +as}:
      if.at(Tm, tm.eq(TApp{k, h, as}, p), _ => v, _ => TApp{k, rep(h, p, v), rep(as, p, v)})
    case TLam{+y, +b}:
      TLam{y, rep(b, p, v)}
    case TAdd{+a, +b}:
      if.at(Tm, tm.eq(TAdd{a, b}, p), _ => v, _ => TAdd{rep(a, p, v), rep(b, p, v)})
    case TEqn{+a, +b, +c}:
      TEqn{rep(a, p, v), rep(b, p, v), rep(c, p, v)}
    case TArg{+a, +r}:
      TArg{rep(a, p, v), rep(r, p, v)}
    case TEnd{}:
      TEnd{}

# arguments
def arg(as: Tm, i: Nat) -> Tm:
  match as i:
    case TArg{x, r} 0n:
      x
    case TArg{x, r} 1n+j:
      arg(r, j)
    case _ _:
      TEnd{}

def args.of(xs: List<&2, Tm>) -> Tm:
  match xs:
    case Nil{}:
      TEnd{}
    case Con{x, t}:
      TArg{x, args.of(t)}

def call(n: String, xs: List<&2, Tm>) -> Tm:
  TApp{0n, TId{n}, args.of(xs)}

def con(n: String, xs: List<&2, Tm>) -> Tm:
  TApp{1n, TId{n}, args.of(xs)}

def as.of(t: Tm) -> Tm:
  match t:
    case TApp{k, h, as}:
      as
    case _:
      TEnd{}

# an application's head's name, and its bracket
def hd(t: Tm) -> String:
  match t:
    case TApp{k, h, as}:
      id.of(h)
    case _:
      ""

def is.con(+t: Tm, +n: String) -> Bool:
  Bool.and(String.eq(hd(t), n), Bool.not(String.is_empty(n)))

# types -------------------------------------------------------------------------------

def ty.sigma(a: Tm, b: Tm) -> Tm:
  TApp{2n, TId{"Sigma"}, args.of([TId{"&2"}, TId{"&2"}, a, TLam{"_", b}])}

def ty.either(a: Tm, b: Tm) -> Tm:
  TApp{2n, TId{"Either"}, args.of([TId{"&2"}, TId{"&2"}, a, b])}

def ty.list(a: Tm) -> Tm:
  TApp{2n, TId{"List"}, args.of([TId{"&2"}, a])}

def ty.maybe() -> Tm:
  parse("Maybe<&2, C.HV>")

def lam.b(t: Tm) -> Tm:
  match t:
    case TLam{x, b}:
      b
    case +u:
      u

# the model's value of a v of the type t
def rv(fuel: Nat, +t: Tm, +v: Tm) -> Tm:
  match fuel:
    case 0n:
      TEnd{}
    case 1n+g:
      +f = g
      +h = {String.append(hd(t), id.of(t)) : String}
      +a = {arg(as.of(t), 2n) : Tm}
      +b = {arg(as.of(t), 3n) : Tm}
      +x = {TId{"x"} : Tm}
      if.at(Tm, String.eq(h, "Nat"), _ => con("C.HvNat", [v]), _ => if.at(Tm, String.eq(h, "Bool"), _ => con("C.HvBool", [v]), _ => if.at(Tm, String.eq(h, "Unit"), _ => call("R.unit", [v]), _ => if.at(Tm, String.eq(h, "Sigma"), _ => call("R.pair", [a, lam.b(b), TLam{"x", rv(f, a, x)}, TLam{"x", rv(f, lam.b(b), x)}, v]), _ => if.at(Tm, String.eq(h, "Either"), _ => call("R.either", [a, b, TLam{"x", rv(f, a, x)}, TLam{"x", rv(f, b, x)}, v]), _ => call("R.list", [arg(as.of(t), 1n), TLam{"x", rv(f, arg(as.of(t), 1n), x)}, v]))))))

# whether the type is a partial def's answer (GHC's error as Inl{its message})
def ty.partial(+t: Tm) -> Bool:
  Bool.and(String.eq(hd(t), "Either"), tm.eq(arg(as.of(t), 2n), parse("List<&2, Char>")))

# a def's answer v of the type t as the model's answer
def rhs(+t: Tm, +v: Tm) -> Tm:
  +a = {arg(as.of(t), 3n) : Tm}
  if.at(Tm, ty.partial(t), _ => call("R.err", [a, TLam{"x", rv(12n, a, TId{"x"})}, v]), _ => con("Some", [rv(12n, t, v)]))

# the patterns of a type, as terms: each lower-case name a variable
def wrap1(xs: List<&2, Tm>, +n: String) -> List<&2, Tm>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      con(n, [x]) <> wrap1(t, n)

def pairs1(+x: Tm, ys: List<&2, Tm>, rest: List<&2, Tm>) -> List<&2, Tm>:
  match ys:
    case Nil{}:
      rest
    case Con{y, t}:
      con("Tuple", [x, y]) <> pairs1(x, t, rest)

def pairs(xs: List<&2, Tm>, +ys: List<&2, Tm>) -> List<&2, Tm>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      pairs1(x, ys, pairs(t, ys))

def pats(fuel: Nat, +t: Tm, +p: String) -> List<&2, Tm>:
  match fuel:
    case 0n:
      [TId{p}]
    case 1n+g:
      +f = g
      +h = {String.append(hd(t), id.of(t)) : String}
      +a = {arg(as.of(t), 2n) : Tm}
      +b = {arg(as.of(t), 3n) : Tm}
      if.at(List<&2, Tm>, String.eq(h, "Bool"), _ => [con("True", []), con("False", [])], _ => if.at(List<&2, Tm>, String.eq(h, "Unit"), _ => [con("Unit", [])], _ => if.at(List<&2, Tm>, String.eq(h, "Sigma"), _ => pairs(pats(f, a, cat([p, "a"])), pats(f, lam.b(b), cat([p, "b"]))), _ => if.at(List<&2, Tm>, String.eq(h, "Either"), _ => List.append(&2, Tm, wrap1(pats(f, a, cat([p, "l"])), "Inl"), wrap1(pats(f, b, cat([p, "r"])), "Inr")), _ => [TId{p}]))))

def starts.digit(s: String) -> Bool:
  match s:
    case SCon{c, t}:
      Char.is_digit(c)
    case SNil{}:
      False{}

def is.lit(+t: Tm) -> Bool:
  match t:
    case TId{n}:
      starts.digit(n)
    case TAdd{a, b}:
      True{}
    case _:
      False{}

def plus(lit: Bool) -> String:
  match lit:
    case True{}:
      ""
    case False{}:
      "+"

# a pattern's text
def pat.sh(t: Tm, first: Bool) -> String:
  match t:
    case TId{+n}:
      cat([plus(is.lit(TId{n})), n])
    case TApp{k, h, as}:
      cat([id.of(h), "{", pat.sh(as, True{}), "}"])
    case TArg{x, r}:
      cat([sep(first), pat.sh(x, True{}), pat.sh(r, False{})])
    case TAdd{a, b}:
      cat([id.of(a), "+", pat.sh(b, True{})])
    case _:
      ""

# HV's constructors, for an answer no def of cata's has (a dead fold's)
def hv.pats(+p: String) -> List<&2, Tm>:
  [con("C.HvNat", [TId{cat([p, "n"])}]), con("C.HvBool", [TId{cat([p, "b"])}]), con("C.HvUnit", []), con("C.HvPair", [TId{cat([p, "x"])}, TId{cat([p, "y"])}]), con("C.HvInl", [TId{cat([p, "l"])}]), con("C.HvInr", [TId{cat([p, "r"])}]), con("C.HvNil", []), con("C.HvCons", [TId{cat([p, "h"])}, TId{cat([p, "t"])}])]

# the stuck part ------------------------------------------------------------------------

# what to do about it
type Kd is Data:
  KGen{t: Tm, ty: Tm}
  KDiv{y: Tm}
  KFold{t: Tm}
  KSub{t: Tm, x: Tm, y: Tm, c: Tm}
  KNo{}

def kd.or(a: Kd, b: Unit -> Kd) -> Kd:
  match a:
    case KNo{}:
      b(Unit{})
    case u:
      u

# a part of the model's side: whether it is stuck itself
def kd.a(+t: Tm, +ls: List<&2, String>) -> Kd:
  +h = {hd(t) : String}
  +as = {as.of(t) : Tm}
  +ok = {Bool.not(anyfree(ls, t)) : Bool}
  +a0 = {arg(as, 0n) : Tm}
  if.at(Kd, Bool.not(ok), _ => KNo{}, _ =>
    if.at(Kd, String.starts_with(h, "Cmp.is_"), _ => KGen{t, TId{"Bool"}}, _ =>
    if.at(Kd, String.eq(h, "C.HvBool"), _ => if.at(Kd, Bool.or(is.con(a0, "True"), is.con(a0, "False")), _ => KNo{}, _ => KGen{a0, TId{"Bool"}}), _ =>
    if.at(Kd, String.eq(h, "C.p.at"), _ => if.at(Kd, Bool.or(is.con(a0, "C.PDiv"), is.con(a0, "C.PMod")), _ => if.at(Kd, is.lit(arg(as, 2n)), _ => KNo{}, _ => KDiv{arg(as, 2n)}), _ => KNo{}), _ =>
    if.at(Kd, String.eq(h, "R.pair"), _ => if.at(Kd, is.con(arg(as, 4n), "Tuple"), _ => KNo{}, _ => KGen{arg(as, 4n), ty.sigma(a0, arg(as, 1n))}), _ =>
    if.at(Kd, String.eq(h, "R.either"), _ => if.at(Kd, Bool.or(is.con(arg(as, 4n), "Inl"), is.con(arg(as, 4n), "Inr")), _ => KNo{}, _ => KGen{arg(as, 4n), ty.either(a0, arg(as, 1n))}), _ =>
    if.at(Kd, String.eq(h, "R.err"), _ => if.at(Kd, Bool.or(is.con(arg(as, 2n), "Inl"), is.con(arg(as, 2n), "Inr")), _ => KNo{}, _ => KGen{arg(as, 2n), ty.either(parse("List<&2, Char>"), a0)}), _ =>
    if.at(Kd, String.eq(h, "R.unit"), _ => if.at(Kd, is.con(a0, "Unit"), _ => KNo{}, _ => KGen{a0, TId{"Unit"}}), _ =>
    if.at(Kd, String.eq(h, "C.ev"), _ => if.at(Kd, is.con(a0, "C.EFold"), _ => KFold{t}, _ => KNo{}), _ => KNo{})))))))))

# a part of cata's side
def ty.inst(ps: List<&2, String>, as: Tm, +t: Tm) -> Tm:
  match ps as:
    case Con{p, r} TArg{x, u}:
      ty.inst(r, u, sub(t, p, x))
    case _ _:
      t

def sg.ty(m: Maybe<&2, Sg>, +as: Tm) -> Tm:
  match m:
    case Some{Sg{n, k, ps, r}}:
      ty.inst(ps, as, r)
    case None{}:
      TEnd{}

def splits(+t: Tm) -> Bool:
  +h = {String.append(hd(t), id.of(t)) : String}
  Bool.or(String.eq(h, "Bool"), Bool.or(String.eq(h, "Unit"), Bool.or(String.eq(h, "Sigma"), String.eq(h, "Either"))))

def is.def(+h: String) -> Bool:
  Bool.or(Bool.or(String.starts_with(h, "D."), String.starts_with(h, "B.")), Bool.or(String.starts_with(h, "H."), String.starts_with(h, "K.")))

def kd.b(+t: Tm, +ls: List<&2, String>, +ss: List<&2, Sg>) -> Kd:
  +h = {hd(t) : String}
  +as = {as.of(t) : Tm}
  if.at(Kd, anyfree(ls, t), _ => KNo{}, _ =>
    if.at(Kd, String.starts_with(h, "Cmp.is_"), _ => KGen{t, TId{"Bool"}}, _ =>
    if.at(Kd, Bool.or(String.eq(h, "H.HsNum.div"), String.eq(h, "H.HsNum.mod")), _ => KDiv{arg(as, 1n)}, _ =>
    if.at(Kd, is.def(h), _ => if.at(Kd, splits(sg.ty(sg.find(ss, h), as)), _ => KGen{t, sg.ty(sg.find(ss, h), as)}, _ => KNo{}), _ => KNo{}))))

# the model's partial (-) at a pair of numbers: cata's HsNum.sub's answer
# (S.bend), before its own test is looked at
def kd.sub(+t: Tm, +ls: List<&2, String>) -> Kd:
  +of = {arg(as.of(t), 0n) : Tm}
  +at = {arg(as.of(of), 0n) : Tm}
  +as = {as.of(at) : Tm}
  +hit = {Bool.and(String.eq(hd(t), "C.h.pv"), Bool.and(String.eq(hd(of), "C.p.of"), String.eq(hd(at), "C.p.lt.at"))) : Bool}
  if.at(Kd, Bool.and(hit, Bool.and(String.starts_with(hd(arg(as, 0n)), "Cmp.is_lt"), Bool.not(anyfree(ls, t)))), _ => KSub{t, arg(as, 1n), arg(as, 2n), arg(as, 0n)}, _ => KNo{})

# the first stuck part, the innermost first
def find(t: Tm, +a: Bool, +ls: List<&2, String>, +ss: List<&2, Sg>) -> Kd:
  match t:
    case TId{n}:
      KNo{}
    case TApp{+k, +h, +as}:
      kd.or(if.at(Kd, a, _ => kd.sub(TApp{k, h, as}, ls), _ => KNo{}), _ => kd.or(find(h, a, ls, ss), _ => kd.or(find(as, a, ls, ss), _ => if.at(Kd, a, _ => kd.a(TApp{k, h, as}, ls), _ => kd.b(TApp{k, h, as}, ls, ss)))))
    case TLam{x, b}:
      find(b, a, x <> ls, ss)
    case TAdd{x, y}:
      kd.or(find(x, a, ls, ss), _ => find(y, a, ls, ss))
    case TEqn{x, y, z}:
      KNo{}
    case TArg{x, r}:
      kd.or(find(x, a, ls, ss), _ => find(r, a, ls, ss))
    case TEnd{}:
      KNo{}

# a call of cata's that may be the model's fold of a list, and which of
# its arguments the list is
type Dc is Data:
  Dc{t: Tm, i: Nat}

def put.if(c: Bool, x: Dc, r: List<&2, Dc>) -> List<&2, Dc>:
  match c:
    case True{}:
      x <> r
    case False{}:
      r

# the arguments that are xs, the last first
def takes(as: Tm, +c: Tm, +xs: Tm, +i: Nat, +ok: Bool, r: List<&2, Dc>) -> List<&2, Dc>:
  match as:
    case TArg{+x, u}:
      takes(u, c, xs, 1n+i, ok, put.if(Bool.and(ok, tm.eq(x, xs)), Dc{c, i}, r))
    case _:
      r

# cata's closed calls that take the list xs, innermost first
def folds(t: Tm, +xs: Tm, +ls: List<&2, String>, r: List<&2, Dc>) -> List<&2, Dc>:
  match t:
    case TId{n}:
      r
    case TApp{+k, +h, +as}:
      folds(h, xs, ls, folds(as, xs, ls, takes(as, TApp{k, h, as}, xs, 0n, Bool.and(is.def(id.of(h)), Bool.not(anyfree(ls, TApp{k, h, as}))), r)))
    case TLam{x, b}:
      folds(b, xs, x <> ls, r)
    case TAdd{x, y}:
      folds(x, xs, ls, folds(y, xs, ls, r))
    case TEqn{x, y, z}:
      r
    case TArg{x, u}:
      folds(x, xs, ls, folds(u, xs, ls, r))
    case TEnd{}:
      r

# v for the argument i
def rep.arg(as: Tm, i: Nat, +v: Tm) -> Tm:
  match as i:
    case TArg{x, r} 0n:
      TArg{v, r}
    case TArg{x, r} 1n+j:
      TArg{x, rep.arg(r, j, v)}
    case u _:
      u

def rep.list(t: Tm, +i: Nat, +v: Tm) -> Tm:
  match t:
    case TApp{k, h, as}:
      TApp{k, h, rep.arg(as, i, v)}
    case u:
      u

# the goal ---------------------------------------------------------------------------------

type Vr is Data:
  Vr{n: String, ty: Tm}

# a failing leaf: its sides, its variables, its line, and what it says of its
# sides: 0 the first is below the second (L.Le), 1 they are the same, 2 the
# first answers (L.Is; it has no second)
type Gl is Data:
  Gl{a: Tm, b: Tm, vs: List<&2, Vr>, at: Nat, md: Nat}

def vs.used(vs: List<&2, Vr>, +a: Tm, +b: Tm) -> List<&2, Vr>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Vr{+n, +t}, +r}:
      if.at(List<&2, Vr>, Bool.or(free(a, n), free(b, n)), _ => Vr{n, t} <> vs.used(r, a, b), _ => vs.used(r, a, b))

def vs.drop(vs: List<&2, Vr>, +x: Tm) -> List<&2, Vr>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Vr{+n, +t}, +r}:
      if.at(List<&2, Vr>, tm.eq(TId{n}, x), _ => vs.drop(r, x), _ => Vr{n, t} <> vs.drop(r, x))

def vs.ps(vs: List<&2, Vr>, +ss: List<&2, Sg>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{Vr{n, t}, r}:
      cat(["+", n, ": ", sh(t, ShT{}, ss), ", ", vs.ps(r, ss)])

def vs.as(vs: List<&2, Vr>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{Vr{n, t}, r}:
      cat([n, ", ", vs.as(r)])

# the last ", " off
def trim2(+s: String) -> String:
  if.at(String, String.ends_with(s, ", "), _ => String.take(s, Nat.sub(String.length(s), 2n)), _ => s)

def vs.hv(vs: List<&2, Vr>, +a: Tm) -> Maybe<&2, Tm>:
  match vs:
    case Nil{}:
      None{}
    case Con{Vr{+n, +t}, +r}:
      if.at(Maybe<&2, Tm>, Bool.and(tm.eq(t, TId{"C.HV"}), free(a, n)), _ => Some{TId{n}}, _ => vs.hv(r, a))

# a step: the new defs, and what the leaf becomes
type St is Data:
  St{defs: String, leaf: String}
  StNo{why: String}

def le.sh(md: Nat, +a: Tm, +b: Tm, +ss: List<&2, Sg>) -> String:
  match md:
    case 0n:
      cat(["L.Le(", sh(a, ShT{}, ss), ", ", sh(b, ShT{}, ss), ")"])
    case 1n:
      cat(["{", sh(a, ShT{}, ss), " == ", sh(b, ShT{}, ss), " : Maybe<&2, C.HV>}"])
    case _:
      cat(["L.Is(", sh(a, ShT{}, ss), ")"])

def refl.sh(md: Nat, +a: Tm, +ss: List<&2, Sg>) -> String:
  match md:
    case 0n:
      cat(["L.refl(", sh(a, ShT{}, ss), ")"])
    case 1n:
      "{==}"
    case _:
      "Unit{}"

# where both sides are errors
def none.sh(md: Nat) -> String:
  match md:
    case 1n:
      "{==}"
    case _:
      "Unit{}"

def eq.e(md: Nat) -> String:
  match md:
    case 1n:
      "e"
    case _:
      ""

# an argument that only L.cut takes
def only.le(md: Nat, +s: String) -> String:
  match md:
    case 0n:
      s
    case _:
      ""

# the cases of a split of w, the goal's side a with w the pattern
def cases(ps: List<&2, Tm>, +md: Nat, +w: String, +a: Tm, +ss: List<&2, Sg>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, r}:
      cat(["    case ", pat.sh(p, True{}), ":\n      ", refl.sh(md, sub(a, w, p), ss), "\n", cases(r, md, w, a, ss)])

# w for the part p, then a split of w
def st.split(+g: String, +p: Tm, +ty: Tm, +ps: List<&2, Tm>, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match gl:
    case Gl{+a, +b, +vs0, at, +md}:
      +w = {cat(["w", g]) : String}
      +a2 = {rep(a, p, TId{w}) : Tm}
      +b2 = {rep(b, p, TId{w}) : Tm}
      +vs = {vs.drop(vs.used(vs0, a2, b2), p) : List<&2, Vr>}
      +body = {if.at(String, Nat.is_eq(List.length(&2, Tm, ps), 0n), _ => cat(["  ", refl.sh(md, a2, ss), "\n"]), _ => cat(["  match ", w, ":\n", cases(ps, md, w, a2, ss)])) : String}
      St{cat(["def g", g, "(", vs.ps(vs, ss), plus(Bool.not(Nat.is_eq(List.length(&2, Tm, ps), 0n))), w, ": ", sh(ty, ShT{}, ss), ") -> ", le.sh(md, a2, b2, ss), ":\n", body, "\n"]), cat(["g", g, "(", vs.as(vs), sh(p, ShT{}, ss), ")"])}

def nat.pats(+w: String) -> List<&2, Tm>:
  [TId{"0n"}, TAdd{TId{"1n"}, TId{cat([w, "p"])}}]

def lam.x(t: Tm) -> String:
  match t:
    case TLam{x, b}:
      x
    case _:
      "?"

# the model's fold over the list x
def ev.at(+fo: Tm, +env: Tm, +t: Tm, +f: Tm, +x: Tm) -> Tm:
  call("C.ev", [fo, con("C.HvPair", [env, call("R.list", [t, f, x])])])

def dc.at(+dc: Tm, +dty: Tm, +i: Nat, +x: Tm) -> Tm:
  rhs(dty, rep.list(dc, i, x))

def bind.at(+m: Tm, +k: Tm) -> Tm:
  call("Maybe.bind", [TId{"&2"}, TId{"C.HV"}, TId{"C.HV"}, m, k])

# a fold that cata's own call dc follows: gN.f, by induction on the list
# (gN.z its nil, gN.s a step), that the model's fold is below cata's; gN.c
# the goal with cata's for it, gN.n with an error
def st.fold(+g: String, +ev: Tm, +dc: Tm, +i: Nat, +dty: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match gl:
    case Gl{+a, +b, +vs0, at, +md}:
      +fo = {arg(as.of(ev), 0n) : Tm}
      +en = {arg(as.of(ev), 1n) : Tm}
      +env = {arg(as.of(en), 0n) : Tm}
      +li = {arg(as.of(en), 1n) : Tm}
      +t = {arg(as.of(li), 0n) : Tm}
      +f = {arg(as.of(li), 1n) : Tm}
      +xs = {arg(as.of(li), 2n) : Tm}
      +z = {arg(as.of(fo), 0n) : Tm}
      +s = {arg(as.of(fo), 1n) : Tm}
      +h = {TId{cat(["h", g])} : Tm}
      +tl = {TId{cat(["t", g])} : Tm}
      +q = {cat(["q", g]) : String}
      +m = {TId{cat(["m", g])} : Tm}
      +y = {TId{cat(["xs", g])} : Tm}
      +hv = {sub(lam.b(f), lam.x(f), h) : Tm}
      +k = {TLam{q, call("C.ev", [s, con("C.HvPair", [con("C.HvPair", [env, hv]), TId{q}])])} : Tm}
      +vs = {vs.used(vs0, TArg{a, TArg{ev, dc}}, b) : List<&2, Vr>}
      +ps = {vs.ps(vs, ss) : String}
      +us = {vs.as(vs) : String}
      +rn = {dc.at(dc, dty, i, con("Nil", [])) : Tm}
      +rc = {dc.at(dc, dty, i, con("Con", [h, tl])) : Tm}
      +rt = {dc.at(dc, dty, i, tl) : Tm}
      +rx = {rhs(dty, dc) : Tm}
      +et = {ev.at(fo, env, t, f, tl) : Tm}
      +bt = {bind.at(rt, k) : Tm}
      +zz = {call("C.ev", [z, env]) : Tm}
      +ht = {cat(["+", id.of(h), ": ", sh(t, ShT{}, ss), ", +", id.of(tl), ": List<&2, ", sh(t, ShT{}, ss), ">"]) : String}
      +dz = {cat(["def g", g, ".z(", trim2(ps), ") -> ", le.sh(md, zz, rn, ss), ":\n  ", refl.sh(md, zz, ss), "\n\n"]) : String}
      +ds = {cat(["def g", g, ".s(", ps, ht, ") -> ", le.sh(md, bt, rc, ss), ":\n  ", refl.sh(md, bt, ss), "\n\n"]) : String}
      +df = {cat(["def g", g, ".f(", ps, id.of(y), ": List<&2, ", sh(t, ShT{}, ss), ">) -> ", le.sh(md, ev.at(fo, env, t, f, y), dc.at(dc, dty, i, y), ss), ":\n  match ", id.of(y), ":\n    case Nil{}:\n      g", g, ".z(", trim2(us), ")\n    case Con{+", id.of(h), ", +", id.of(tl), "}:\n      L.bind", eq.e(md), "(", sh(k, ShT{}, ss), ", ", sh(et, ShT{}, ss), ", ", sh(rt, ShT{}, ss), ", ", sh(rc, ShT{}, ss), ", g", g, ".f(", us, id.of(tl), "), g", g, ".s(", us, id.of(h), ", ", id.of(tl), "))\n\n"]) : String}
      +dn = {cat(["def g", g, ".n(", trim2(ps), ") -> ", le.sh(md, rep(a, ev, con("None", [])), b, ss), ":\n  ", refl.sh(md, rep(a, ev, con("None", [])), ss), "\n\n"]) : String}
      +dc2 = {cat(["def g", g, ".c(", trim2(ps), ") -> ", le.sh(md, rep(a, ev, rx), b, ss), ":\n  ", refl.sh(md, rep(a, ev, rx), ss), "\n\n"]) : String}
      St{cat([dz, ds, df, only.le(md, dn), dc2]), cat(["L.cut", eq.e(md), "(", id.of(m), " => ", sh(rep(a, ev, m), ShT{}, ss), ", ", sh(ev, ShT{}, ss), ", ", sh(rx, ShT{}, ss), ", ", sh(b, ShT{}, ss), ", g", g, ".f(", us, sh(xs, ShT{}, ss), "), g", g, ".c(", trim2(us), ")", only.le(md, cat([", g", g, ".n(", trim2(us), ")"])), ")"])}

# a fold whose nil is an error is one, whatever the list (gN.f, by induction
# on it; gN.z its nil); gN.n the goal with the error for it
def st.err(+g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match gl:
    case Gl{+a, +b, +vs0, at, +md}:
      +fo = {arg(as.of(ev), 0n) : Tm}
      +en = {arg(as.of(ev), 1n) : Tm}
      +env = {arg(as.of(en), 0n) : Tm}
      +li = {arg(as.of(en), 1n) : Tm}
      +z = {arg(as.of(fo), 0n) : Tm}
      +s = {arg(as.of(fo), 1n) : Tm}
      +h = {TId{cat(["h", g])} : Tm}
      +tl = {TId{cat(["t", g])} : Tm}
      +q = {cat(["q", g]) : String}
      +m = {TId{cat(["m", g])} : Tm}
      +y = {TId{cat(["xs", g])} : Tm}
      +vs = {vs.used(vs0, TArg{a, ev}, b) : List<&2, Vr>}
      +ps = {vs.ps(vs, ss) : String}
      +us = {vs.as(vs) : String}
      +no = {con("None", []) : Tm}
      +k = {TLam{q, call("C.ev", [s, con("C.HvPair", [con("C.HvPair", [env, h]), TId{q}])])} : Tm}
      +et = {call("C.ev", [fo, con("C.HvPair", [env, tl])]) : Tm}
      +ey = {call("C.ev", [fo, con("C.HvPair", [env, y])]) : Tm}
      +zz = {call("C.ev", [z, env]) : Tm}
      +dz = {cat(["def g", g, ".z(", trim2(ps), ") -> ", le.sh(md, zz, no, ss), ":\n  ", refl.sh(md, zz, ss), "\n\n"]) : String}
      +df = {cat(["def g", g, ".f(", ps, id.of(y), ": C.HV) -> ", le.sh(md, ey, no, ss), ":\n  match ", id.of(y), ":\n    case C.HvNil{}:\n      g", g, ".z(", trim2(us), ")\n    case C.HvCons{+", id.of(h), ", +", id.of(tl), "}:\n      L.bind", eq.e(md), "(", sh(k, ShT{}, ss), ", ", sh(et, ShT{}, ss), ", None{}, None{}, g", g, ".f(", us, id.of(tl), "), ", none.sh(md), ")\n    case C.HvNat{n}:\n      ", none.sh(md), "\n    case C.HvBool{n}:\n      ", none.sh(md), "\n    case C.HvUnit{}:\n      ", none.sh(md), "\n    case C.HvPair{n, o}:\n      ", none.sh(md), "\n    case C.HvInl{n}:\n      ", none.sh(md), "\n    case C.HvInr{n}:\n      ", none.sh(md), "\n\n"]) : String}
      +dn = {cat(["def g", g, ".n(", trim2(ps), ") -> ", le.sh(md, rep(a, ev, no), b, ss), ":\n  ", refl.sh(md, rep(a, ev, no), ss), "\n\n"]) : String}
      St{cat([dz, df, dn]), cat(["L.cut", eq.e(md), "(", id.of(m), " => ", sh(rep(a, ev, m), ShT{}, ss), ", ", sh(ev, ShT{}, ss), ", None{}, ", sh(b, ShT{}, ss), ", g", g, ".f(", us, sh(li, ShT{}, ss), "), g", g, ".n(", trim2(us), ")", only.le(md, cat([", g", g, ".n(", trim2(us), ")"])), ")"])}

# a fold nothing uses answers (gN.f, by induction on the list: its nil does,
# gN.z, and its step at any value so far, gN.s): gN.m the goal with any
# answer for it
def st.is(+g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match gl:
    case Gl{+a, +b, +vs0, at, +md}:
      +fo = {arg(as.of(ev), 0n) : Tm}
      +en = {arg(as.of(ev), 1n) : Tm}
      +env = {arg(as.of(en), 0n) : Tm}
      +li = {arg(as.of(en), 1n) : Tm}
      +t = {arg(as.of(li), 0n) : Tm}
      +f = {arg(as.of(li), 1n) : Tm}
      +xs = {arg(as.of(li), 2n) : Tm}
      +z = {arg(as.of(fo), 0n) : Tm}
      +s = {arg(as.of(fo), 1n) : Tm}
      +h = {TId{cat(["h", g])} : Tm}
      +tl = {TId{cat(["t", g])} : Tm}
      +q = {cat(["q", g]) : String}
      +m = {TId{cat(["m", g])} : Tm}
      +y = {TId{cat(["xs", g])} : Tm}
      +u = {TId{cat(["u", g])} : Tm}
      +hv = {sub(lam.b(f), lam.x(f), h) : Tm}
      +st = {call("C.ev", [s, con("C.HvPair", [con("C.HvPair", [env, hv]), TId{q}])]) : Tm}
      +k = {TLam{q, st} : Tm}
      +vs = {vs.used(vs0, TArg{a, ev}, b) : List<&2, Vr>}
      +ps = {vs.ps(vs, ss) : String}
      +us = {vs.as(vs) : String}
      +zz = {call("C.ev", [z, env]) : Tm}
      +et = {ev.at(fo, env, t, f, tl) : Tm}
      +dz = {cat(["def g", g, ".z(", trim2(ps), ") -> ", le.sh(2n, zz, zz, ss), ":\n  Unit{}\n\n"]) : String}
      +ds = {cat(["def g", g, ".s(", ps, "+", id.of(h), ": ", sh(t, ShT{}, ss), ", +", q, ": C.HV) -> ", le.sh(2n, st, st, ss), ":\n  Unit{}\n\n"]) : String}
      +df = {cat(["def g", g, ".f(", ps, id.of(y), ": List<&2, ", sh(t, ShT{}, ss), ">) -> ", le.sh(2n, ev.at(fo, env, t, f, y), zz, ss), ":\n  match ", id.of(y), ":\n    case Nil{}:\n      g", g, ".z(", trim2(us), ")\n    case Con{+", id.of(h), ", +", id.of(tl), "}:\n      L.isbind(", sh(k, ShT{}, ss), ", ", sh(et, ShT{}, ss), ", g", g, ".f(", us, id.of(tl), "), ", q, " => g", g, ".s(", us, id.of(h), ", ", q, "))\n\n"]) : String}
      +dm = {cat(["def g", g, ".m(", ps, id.of(m), ": Maybe<&2, C.HV>, e", g, ": L.Is(", id.of(m), ")) -> ", le.sh(md, rep(a, ev, m), b, ss), ":\n  match ", id.of(m), ":\n    case None{}:\n      Empty.absurd(", le.sh(md, rep(a, ev, con("None", [])), b, ss), ", e", g, ")\n    case Some{+", id.of(u), "}:\n      ", refl.sh(md, rep(a, ev, con("Some", [u])), ss), "\n\n"]) : String}
      if.at(St, is.con(li, "R.list"), _ => St{cat([dz, ds, df, dm]), cat(["g", g, ".m(", us, sh(ev, ShT{}, ss), ", g", g, ".f(", us, sh(xs, ShT{}, ss), "))"])}, _ => StNo{"no choice"})

# a fold cata has not (nothing uses its answer)
def st.dead(+g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  st.split(g, ev, ty.maybe(), [con("None", []), con("Some", [TId{cat(["u", g])}])], gl, ss)

def gl.a(g: Gl) -> Tm:
  match g:
    case Gl{a, b, vs, at, md}:
      a

def gl.b(g: Gl) -> Tm:
  match g:
    case Gl{a, b, vs, at, md}:
      b

def gl.vs(g: Gl) -> List<&2, Vr>:
  match g:
    case Gl{a, b, vs, at, md}:
      vs

def gl.md(g: Gl) -> Nat:
  match g:
    case Gl{a, b, vs, at, md}:
      md

def gl.at(g: Gl) -> Nat:
  match g:
    case Gl{a, b, vs, at, md}:
      at

# the model's partial (-) is cata's HsNum.sub (S.bend's law): gN, rewritten
def st.sub(+g: String, +t: Tm, +x: Tm, +y: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match gl:
    case Gl{+a, +b, +vs0, at, +md}:
      +r = {call("R.err", [TId{"Nat"}, TLam{"x", con("C.HvNat", [TId{"x"}])}, call("H.HsNum.sub", [x, y])]) : Tm}
      +vs = {vs.used(vs0, a, b) : List<&2, Vr>}
      St{cat(["def g", g, "(", trim2(vs.ps(vs, ss)), ") -> ", le.sh(md, a, b, ss), ":\n  %S.sub(", sh(x, ShT{}, ss), ", ", sh(y, ShT{}, ss), ") : ", le.sh(md, rep(a, t, TId{"_"}), b, ss), "\n  ", refl.sh(md, rep(a, t, r), ss), "\n\n"]), cat(["g", g, "(", trim2(vs.as(vs)), ")"])}

def is.var(+t: Tm) -> Bool:
  match t:
    case TId{n}:
      True{}
    case _:
      False{}

# what kind of value an expression has, as far as its shape tells (a type's
# head, or ""); d how many variables are bound since the environment env
def kind.h(+h: String) -> String:
  if.at(String, String.eq(h, "C.HvNat"), _ => "Nat", _ => if.at(String, String.eq(h, "C.HvBool"), _ => "Bool", _ => if.at(String, Bool.or(String.eq(h, "C.HvUnit"), String.eq(h, "R.unit")), _ => "Unit", _ => if.at(String, Bool.or(String.eq(h, "C.HvPair"), String.eq(h, "R.pair")), _ => "Sigma", _ => if.at(String, Bool.or(String.eq(h, "C.HvInl"), Bool.or(String.eq(h, "C.HvInr"), String.eq(h, "R.either"))), _ => "Either", _ => if.at(String, Bool.or(String.eq(h, "C.HvNil"), Bool.or(String.eq(h, "C.HvCons"), String.eq(h, "R.list"))), _ => "List", _ => ""))))))

def kind.e(+h: String) -> String:
  if.at(String, String.eq(h, "C.ELit"), _ => "Nat", _ => if.at(String, String.eq(h, "C.EUnit"), _ => "Unit", _ => if.at(String, String.eq(h, "C.EPair"), _ => "Sigma", _ => if.at(String, Bool.or(String.eq(h, "C.EInl"), String.eq(h, "C.EInr")), _ => "Either", _ => if.at(String, Bool.or(String.eq(h, "C.ENil"), String.eq(h, "C.ECons")), _ => "List", _ => "")))))

def kind.v(t: Tm) -> String:
  match t:
    case TApp{k, h, as}:
      kind.h(id.of(h))
    case _:
      ""

def kind.env(env: Tm, i: Nat) -> String:
  match env i:
    case TApp{k, h, TArg{e, TArg{v, r}}} 0n:
      kind.v(v)
    case TApp{k, h, TArg{e, TArg{v, r}}} 1n+j:
      kind.env(e, j)
    case _ _:
      ""

def or.s(+a: String, b: String) -> String:
  if.at(String, String.is_empty(a), _ => b, _ => a)

def or.nat(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      0n

def lit.n(t: Tm) -> Nat:
  match t:
    case TId{n}:
      or.nat(Nat.read(String.reverse(String.drop(String.reverse(n), 1n))))
    case _:
      0n

def kind(fuel: Nat, +t: Tm, +env: Tm, +d: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+(+f):
      +h = {hd(t) : String}
      +a = {arg(as.of(t), 0n) : Tm}
      +b = {arg(as.of(t), 1n) : Tm}
      +c = {arg(as.of(t), 2n) : Tm}
      if.at(String, String.eq(h, "C.EVar"), _ => if.at(String, Nat.is_lt(lit.n(a), d), _ => "", _ => kind.env(env, Nat.sub(lit.n(a), d))), _ => if.at(String, String.eq(h, "C.EIf"), _ => or.s(kind(f, b, env, d), kind(f, c, env, d)), _ => if.at(String, String.eq(h, "C.ELet"), _ => kind(f, b, env, 1n+d), _ => if.at(String, String.eq(h, "C.ECase"), _ => or.s(kind(f, a, env, d), kind(f, b, env, d)), _ => if.at(String, String.eq(h, "C.EFold"), _ => or.s(kind(f, a, env, Nat.sub(d, 1n)), kind(f, b, env, 1n+d)), _ => if.at(String, String.eq(h, "C.EPrim"), _ => if.at(String, is.con(a, "C.PLt"), _ => "Bool", _ => "Nat"), _ => if.at(String, String.eq(h, "C.EFst"), _ => if.at(String, is.con(a, "C.EPair"), _ => kind(f, arg(as.of(a), 0n), env, d), _ => ""), _ => if.at(String, String.eq(h, "C.ESnd"), _ => if.at(String, is.con(a, "C.EPair"), _ => kind(f, arg(as.of(a), 1n), env, d), _ => ""), _ => kind.e(h)))))))))

# a def's answer's kind, under a partial def's Either
def kind.ty(+t: Tm) -> String:
  +u = {if.at(Tm, ty.partial(t), _ => arg(as.of(t), 3n), _ => t) : Tm}
  String.append(hd(u), id.of(u))

# the candidates of the fold's kind
def fits(ds: List<&2, Dc>, +k: String, +ss: List<&2, Sg>) -> List<&2, Dc>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Dc{+dc, i}, t}:
      put.if(Bool.or(String.is_empty(k), String.eq(k, kind.ty(sg.ty(sg.find(ss, hd(dc)), as.of(dc))))), Dc{dc, i}, fits(t, k, ss))

# what else there is to do about a fold
type Alt is Data:
  ADiv{y: Tm}
  AErr{}
  ADead{}
  AGen{t: Tm, ty: Tm}
  AIs{}

# (md: which of them there are where the sides are to be the same, or where
# an answer is all)
def alts(md: Nat, k: Kd) -> List<&2, Alt>:
  match md k:
    case 0n KDiv{y}:
      [ADiv{y}, AErr{}, ADead{}]
    case 0n KGen{t, ty}:
      [AErr{}, ADead{}, AGen{t, ty}]
    case 0n _:
      [AErr{}, ADead{}]
    case 1n KDiv{y}:
      [ADiv{y}, AErr{}, AIs{}]
    case 1n KGen{t, ty}:
      [AErr{}, AIs{}, AGen{t, ty}]
    case 1n _:
      [AErr{}, AIs{}]
    case _ _:
      [AIs{}]

def alt(xs: List<&2, Alt>, c: Nat, +g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match xs c:
    case Con{ADiv{+y}, t} 0n:
      st.split(g, y, TId{"Nat"}, nat.pats(cat(["v", g])), gl, ss)
    case Con{AErr{}, t} 0n:
      st.err(g, ev, gl, ss)
    case Con{ADead{}, t} 0n:
      st.dead(g, ev, gl, ss)
    case Con{AIs{}, t} 0n:
      st.is(g, ev, gl, ss)
    case Con{AGen{+x, +ty}, t} 0n:
      st.split(g, x, ty, pats(8n, ty, cat(["v", g])), gl, ss)
    case Con{a, t} 1n+d:
      alt(t, d, g, ev, gl, ss)
    case Nil{} _:
      StNo{"no choice"}

# the choice c: a call of cata's that may be this fold, or (after them) an
# error, any answer (nothing uses it), or a step of cata's side first
def act.fold2(ds: List<&2, Dc>, c: Nat, +g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match ds c:
    case Con{Dc{+dc, +i}, t} 0n:
      st.fold(g, ev, dc, i, sg.ty(sg.find(ss, hd(dc)), as.of(dc)), gl, ss)
    case Con{dc, t} 1n+d:
      act.fold2(t, d, g, ev, gl, ss)
    case Nil{} d:
      alt(alts(gl.md(gl), find(gl.b(gl), False{}, Nil{}, ss)), d, g, ev, gl, ss)

def kind.fold(+ev: Tm) -> String:
  +fo = {arg(as.of(ev), 0n) : Tm}
  +env = {arg(as.of(arg(as.of(ev), 1n)), 0n) : Tm}
  or.s(kind(24n, arg(as.of(fo), 0n), env, 0n), kind(24n, arg(as.of(fo), 1n), env, 2n))

def one.choice(c: Nat, s: Unit -> St) -> St:
  match c:
    case 0n:
      s(Unit{})
    case 1n+d:
      StNo{"no choice"}

def act.fold(+c: Nat, +g: String, +ev: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  +li = {arg(as.of(arg(as.of(ev), 1n)), 1n) : Tm}
  +xs = {arg(as.of(li), 2n) : Tm}
  if.at(St, Bool.not(is.con(li, "R.list")), _ => act.fold2(Nil{}, c, g, ev, gl, ss), _ => if.at(St, is.var(xs), _ => act.fold2(fits(folds(gl.b(gl), xs, Nil{}, Nil{}), kind.fold(ev), ss), c, g, ev, gl, ss), _ => one.choice(c, _ => st.split(g, xs, ty.list(arg(as.of(li), 0n)), Nil{}, gl, ss))))

# whether a term calls f
def has.call(t: Tm, +f: String) -> Bool:
  match t:
    case TApp{k, +h, as}:
      Bool.or(String.eq(id.of(h), f), has.call(as, f))
    case TLam{x, b}:
      has.call(b, f)
    case TAdd{x, y}:
      Bool.or(has.call(x, f), has.call(y, f))
    case TEqn{x, y, z}:
      Bool.or(has.call(x, f), has.call(y, f))
    case TArg{x, r}:
      Bool.or(has.call(x, f), has.call(r, f))
    case _:
      False{}

def act.sub1(+g: String, +b: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  st.split(g, b, TId{"Bool"}, pats(8n, TId{"Bool"}, cat(["v", g])), gl, ss)

# the model's partial (-): cata's HsNum.sub, where cata calls it, or a split of
# its test (a total Nat.sub, where a test makes the subtraction safe)
def act.sub(num: Bool, c: Nat, +g: String, +t: Tm, +x: Tm, +y: Tm, +b: Tm, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match num c:
    case True{} 0n:
      st.sub(g, t, x, y, gl, ss)
    case True{} 1n:
      act.sub1(g, b, gl, ss)
    case False{} 0n:
      act.sub1(g, b, gl, ss)
    case False{} 1n:
      st.sub(g, t, x, y, gl, ss)
    case _ _:
      StNo{"no choice"}

def act.b(k: Kd, +c: Nat, +g: String, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match k:
    case KGen{+t, +ty}:
      one.choice(c, _ => st.split(g, t, ty, pats(8n, ty, cat(["v", g])), gl, ss))
    case KDiv{+y}:
      one.choice(c, _ => st.split(g, y, TId{"Nat"}, nat.pats(cat(["v", g])), gl, ss))
    case KSub{+t, +x, +y, +b}:
      act.sub(has.call(gl.b(gl), "H.HsNum.sub"), c, g, t, x, y, b, gl, ss)
    case KFold{+ev}:
      act.fold(c, g, ev, gl, ss)
    case KNo{}:
      StNo{"no stuck part"}

def act.hv(m: Maybe<&2, Tm>, +c: Nat, +g: String, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match m:
    case Some{+u}:
      one.choice(c, _ => st.split(g, u, TId{"C.HV"}, hv.pats(cat(["v", g])), gl, ss))
    case None{}:
      act.b(find(gl.b(gl), False{}, Nil{}, ss), c, g, gl, ss)

def act.a(k: Kd, +c: Nat, +g: String, +gl: Gl, +ss: List<&2, Sg>) -> St:
  match k:
    case KNo{}:
      act.hv(if.at(Maybe<&2, Tm>, Nat.is_eq(gl.md(gl), 0n), _ => vs.hv(gl.vs(gl), gl.a(gl)), _ => None{}), c, g, gl, ss)
    case u:
      act.b(u, c, g, gl, ss)

def act(+c: Nat, +g: String, +gl: Gl, +ss: List<&2, Sg>) -> St:
  act.a(find(gl.a(gl), True{}, Nil{}, ss), c, g, gl, ss)

# the log -----------------------------------------------------------------------------------

def line.with(ls: List<&2, String>, +p: String) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, +t}:
      if.at(String, String.starts_with(l, p), _ => String.drop(l, String.length(p)), _ => line.with(t, p))

def line.has(ls: List<&2, String>, +p: String) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, +t}:
      if.at(String, String.contains(l, p), _ => l, _ => line.has(t, p))

def ctx(ls: List<&2, String>, in: Bool) -> List<&2, Vr>:
  match ls in:
    case Nil{} _:
      Nil{}
    case Con{+l, +t} True{}:
      if.at(List<&2, Vr>, String.starts_with(l, "- "), _ => Vr{String.trim(before(String.drop(l, 2n), " : ")), parse(past(l, " : "))} <> ctx(t, True{}), _ => Nil{})
    case Con{+l, t} False{}:
      ctx(t, String.starts_with(l, "Context:"))

def leaf.at(+ls: List<&2, String>) -> Nat:
  or.nat(Nat.read(String.trim(before(line.has(ls, ">|"), ">|"))))

# (at {==} Bend tells the two sides, expected and observed)
def goal.at(md: Nat, +u: Tm, +o: Tm, +ls: List<&2, String>) -> Gl:
  match md:
    case 0n:
      Gl{arg(as.of(u), 0n), arg(as.of(u), 1n), ctx(ls, False{}), leaf.at(ls), 0n}
    case 1n:
      Gl{u, o, ctx(ls, False{}), leaf.at(ls), 1n}
    case _:
      Gl{arg(as.of(u), 0n), TEnd{}, ctx(ls, False{}), leaf.at(ls), 2n}

def goal.of(+e: Tm, +o: Tm, +md: Nat, +ls: List<&2, String>) -> Gl:
  match e:
    case TEqn{a, b, t}:
      Gl{a, b, ctx(ls, False{}), leaf.at(ls), md}
    case +u:
      goal.at(md, u, o, ls)

# the file ------------------------------------------------------------------------------------

def indent(s: String) -> String:
  match s:
    case SCon{+c, t}:
      if.at(String, Char.is_eq(c, ' '), _ => SCon{' ', indent(t)}, _ => "")
    case SNil{}:
      ""

def unlines(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{l, t}:
      cat([l, "\n", unlines(t)])

# the lines reversed before the def that holds the line, and from it on
def back(rs: List<&2, String>, +acc: List<&2, String>, +defs: String) -> String:
  match rs:
    case Nil{}:
      cat([defs, unlines(acc)])
    case Con{+l, +t}:
      if.at(String, String.starts_with(l, "def "), _ => cat([unlines(List.reverse(&2, String, t)), defs, unlines(l <> acc)]), _ => back(t, l <> acc, defs))

def edit(ls: List<&2, String>, n: Nat, rs: List<&2, String>, +defs: String, +leaf: String) -> String:
  match ls n:
    case Con{+l, t} 1n:
      back(rs, cat([indent(l), leaf]) <> t, defs)
    case Con{l, t} 1n+m:
      edit(t, m, l <> rs, defs, leaf)
    case _ _:
      ""

def nth(ls: List<&2, String>, n: Nat) -> String:
  match ls n:
    case Con{l, t} 1n:
      l
    case Con{l, t} 1n+m:
      nth(t, m)
    case _ _:
      ""

# a last empty line off (a file's text ends with one)
def chop.r(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Con{"", t}:
      t
    case u:
      u

def chop(ls: List<&2, String>) -> List<&2, String>:
  List.reverse(&2, String, chop.r(List.reverse(&2, String, ls)))

type Out is Data:
  Out{ok: Bool, s: String}

def out.st(s: St, +ls: List<&2, String>, +at: Nat) -> Out:
  match s:
    case St{defs, leaf}:
      Out{True{}, edit(ls, at, Nil{}, defs, leaf)}
    case StNo{w}:
      Out{False{}, w}

def is.eqn(t: Tm) -> Bool:
  match t:
    case TEqn{a, b, c}:
      True{}
    case _:
      False{}

def is.leaf(md: Nat, +e: Tm, +l: String) -> Bool:
  match md:
    case 0n:
      Bool.and(Bool.or(is.con(e, "L.Le"), is.eqn(e)), String.contains(l, "L.refl("))
    case 1n:
      Bool.and(String.eq(String.trim(l), "{==}"), Bool.not(is.eqn(e)))
    case _:
      String.eq(String.trim(l), "Unit{}")

def step(+c: Nat, +g: String, +ls: List<&2, String>, +log: List<&2, String>, +ss: List<&2, Sg>) -> Out:
  +e = {names(parse(line.with(log, "- expected : ")), Nil{}) : Tm}
  +o = {names(parse(line.with(log, "- observed : ")), Nil{}) : Tm}
  +l = {nth(ls, leaf.at(log)) : String}
  +md = {if.at(Nat, is.con(e, "L.Is"), _ => 2n, _ => if.at(Nat, String.contains(l, "L.refl("), _ => 0n, _ => 1n)) : Nat}
  +gl = {goal.of(e, o, md, log) : Gl}
  if.at(Out, Bool.not(is.leaf(md, e, l)), _ => Out{False{}, cat(["not a leaf: ", line.with(log, "- expected : ")])}, _ => out.st(act(c, g, gl, ss), ls, gl.at(gl)))

# input and output ------------------------------------------------------------------------------

type Fr is Type:
  Fr{f: File, acc: List<&2, String>, more: Bool}

def fr.res(g: File, x: Result<&1, &1, U32 & String, String>, acc: List<&2, String>) -> IO(Fr):
  match x:
    case Fail{(c, m)}:
      do IO<Fr>:
        File.close(g)
        IO.die(Fr, 1, "cert: read failed: " ++ m)
    case Done{+s}:
      IO.pure(Fr, Fr{g, s <> acc, Bool.not(String.is_empty(s))})

def fr.got(acc: List<&2, String>, r: File & Result<&1, &1, U32 & String, String>) -> IO(Fr):
  (g, x) = r
  fr.res(g, x, acc)

def fr.step(s: Fr) -> IO(Fr):
  match s:
    case Fr{f, acc, m}:
      do IO<Fr>:
        r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 65536)
        fr.got(acc, r)

def fr.go(fuel: Nat, s: Fr) -> IO(String):
  match fuel s:
    case 1n+p Fr{f, acc, True{}}:
      IO.bind(Fr, String, fr.step(Fr{f, acc, True{}}), fr.go(p))
    case _ Fr{f, acc, _}:
      do IO<String>:
        File.close(f)
        return String.concat(List.reverse(&2, String, acc))

def fr.opened(r: Result<&1, &1, U32 & String, File>) -> IO(String):
  match r:
    case Fail{(c, m)}:
      IO.die(String, 1, "cert: cannot open a file: " ++ m)
    case Done{f}:
      fr.go(4096n, Fr{f, Nil{}, True{}})

def read(path: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    fr.opened(r)

def sgs(args: List<String>, ss: List<&2, Sg>) -> IO(List<&2, Sg>):
  match args:
    case Nil{}:
      IO.pure(List<&2, Sg>, ss)
    case +a <> t:
      do IO<List<&2, Sg>>:
        s : String <- read(past(a, "="))
        sgs(t, sg.lines(String.lines(s), before(a, "="), ss))

def finish(o: Out) -> IO(Unit):
  match o:
    case Out{True{}, s}:
      IO.write(s)
    case Out{False{}, s}:
      IO.die(Unit, 1, s)

def run(args: List<String>) -> IO(Unit):
  match args:
    case "step" <> g <> c <> f <> l <> r:
      do IO<Unit>:
        fs : String <- read(f)
        lg : String <- read(l)
        ss : List<&2, Sg> <- sgs(r, Nil{})
        finish(step(or.nat(Nat.read(c)), g, chop(String.lines(fs)), String.lines(lg), ss))
    case _:
      IO.print("usage: cert step N CHOICE FILE LOG (NAME=FILE)...")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    run(List.tail(&1, String, argv))
