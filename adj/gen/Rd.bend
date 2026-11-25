# adj/gen/Rd.bend: G's Haskell, read as the model's programs.  G (Back.bend)
# writes a def of cata's Bend as one line of Haskell, `c'f x y = E`, under
# its signature; this program reads those lines and writes def dN's body as
# an Ex of adj/Core.bend (the fragment as Haskell writes it), the defs it
# calls in place: a def that does not call itself at its arguments (lets),
# one that does, and whose body is a case of a list it calls itself at the
# tail of, all else the same, as a fold of the list with the other arguments
# around it (foldr's Haskell, EFold).  An `Either [Char]` a def answers is
# cata's failure (BendRt's HsNum, b'hs'either'bind), an error of the model;
# another Either is a sum.  What it does not read it says (OUT, why).
#
# The reading is trusted as Gen.bend's printing is (it says what Haskell
# program an Ex is); cert.zsh with EX (its rows) proves that its Ex means what cata's Bend def,
# whose G it is, answers, at every input, and tries it against GHC's G.
#   rd FILE.hs N...   a line N, a tab, and the Ex (or OUT and why) for each
#
# An argument or a let its def does not use is not in the Ex, as Haskell never
# forces it. A list's case that does not call the def at its tail is
# a fold that does not use its answer.

import Base

def cat(xs: List<&2, String>) -> String:
  String.concat(xs)

def if.at(-A: Type, c: Bool, t: Unit -> A, e: Unit -> A) -> A:
  match c:
    case True{}:
      t(Unit{})
    case False{}:
      e(Unit{})

# tokens ---------------------------------------------------------------------------

def is.id(+c: Char) -> Bool:
  +n = {Char.to_u32(c) : U32}
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c), Bool.or(U32.is_eq(n, 95), Bool.or(U32.is_eq(n, 46), U32.is_eq(n, 39)))))

type Cl is Data:
  CId{}
  CSp{}
  CDq{}
  CPu{}

type Cc is Data:
  Cc{c: Char, k: Cl}

def cl(+c: Char) -> Cl:
  +n = {Char.to_u32(c) : U32}
  if.at(Cl, is.id(c), _ => CId{}, _ => if.at(Cl, Char.is_space(c), _ => CSp{}, _ => if.at(Cl, U32.is_eq(n, 34), _ => CDq{}, _ => CPu{})))

def ccs(cs: List<&2, Char>) -> List<&2, Cc>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Cc{c, cl(c)} <> ccs(t)

def flush(w: List<&2, Char>, r: List<&2, String>) -> List<&2, String>:
  match w:
    case Nil{}:
      r
    case Con{c, t}:
      String.from_list(List.reverse(&2, Char, Con{c, t})) <> r

# dq: inside a string
def lex(cs: List<&2, Cc>, dq: Bool, w: List<&2, Char>) -> List<&2, String>:
  match cs dq:
    case Nil{} _:
      flush(w, Nil{})
    case Con{Cc{c, CId{}}, t} False{}:
      lex(t, False{}, c <> w)
    case Con{Cc{c, CSp{}}, t} False{}:
      flush(w, lex(t, False{}, Nil{}))
    case Con{Cc{c, CDq{}}, t} False{}:
      flush(w, lex(t, True{}, [c]))
    case Con{Cc{c, CPu{}}, t} False{}:
      flush(w, String.from_list([c]) <> lex(t, False{}, Nil{}))
    case Con{Cc{c, CDq{}}, t} True{}:
      flush(c <> w, lex(t, False{}, Nil{}))
    case Con{Cc{c, _}, t} True{}:
      lex(t, True{}, c <> w)

def toks(s: String) -> List<&2, String>:
  lex(ccs(String.to_list(s)), False{}, Nil{})

# expressions ------------------------------------------------------------------------

# a name (a variable, a def, a constructor: Left, [], (:), (,), ()), a number, a
# string, an application, a lambda, a case and its alternatives
type Hx is Data:
  HV{n: String}
  HN{k: String}
  HS{}
  HA{f: Hx, a: Hx}
  HL{x: String, b: Hx}
  HC{e: Hx, as: Hx}
  HAlt{p: Hx, b: Hx, r: Hx}
  HEnd{}

type Pr is Data:
  Pr{t: Hx, r: List<&2, String>}

def pr.t(p: Pr) -> Hx:
  match p:
    case Pr{t, r}:
      t

def pr.r(p: Pr) -> List<&2, String>:
  match p:
    case Pr{t, r}:
      r

def first.of(cs: List<&2, Char>) -> U32:
  match cs:
    case Con{c, t}:
      Char.to_u32(c)
    case Nil{}:
      0

def first.char(+s: String) -> U32:
  first.of(String.to_list(s))

def atom(+s: String) -> Hx:
  +c = {first.char(s) : U32}
  if.at(Hx, U32.is_eq(c, 34), _ => HS{}, _ => if.at(Hx, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), _ => HN{s}, _ => HV{s}))

def tail(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case x <> t:
      t
    case Nil{}:
      Nil{}

# an expression; what follows one (its arguments); a case's alternatives
type Pk is Data:
  PkE{}
  PkO{}
  PkA{f: Hx}
  PkS{}

def px(+fuel: Nat, k: Pk, +ts: List<&2, String>) -> Pr:
  match fuel:
    case 0n:
      Pr{HEnd{}, ts}
    case 1n+f:
      match k:
        case PkE{}:
          match ts:
            case "\\" <> +x <> "-" <> ">" <> +r:
              +b = px(f, PkE{}, r)
              Pr{HL{x, pr.t(b)}, pr.r(b)}
            case "case" <> +r:
              +e = px(f, PkE{}, r)
              +a = px(f, PkS{}, tail(tail(pr.r(e))))
              Pr{HC{pr.t(e), pr.t(a)}, pr.r(a)}
            case +u:
              +a = px(f, PkO{}, u)
              px(f, PkA{pr.t(a)}, pr.r(a))
        case PkO{}:
          match ts:
            case "(" <> ")" <> r:
              Pr{HV{"()"}, r}
            case "(" <> "," <> ")" <> r:
              Pr{HV{"(,)"}, r}
            case "(" <> ":" <> ")" <> r:
              Pr{HV{"(:)"}, r}
            case "[" <> "]" <> r:
              Pr{HV{"[]"}, r}
            case "(" <> +r:
              +e = px(f, PkE{}, r)
              Pr{pr.t(e), tail(pr.r(e))}
            case +x <> r:
              Pr{atom(x), r}
            case Nil{}:
              Pr{HEnd{}, Nil{}}
        case PkA{+fn}:
          match ts:
            case Nil{}:
              Pr{fn, Nil{}}
            case ")" <> r:
              Pr{fn, ")" <> r}
            case ";" <> r:
              Pr{fn, ";" <> r}
            case "}" <> r:
              Pr{fn, "}" <> r}
            case "of" <> r:
              Pr{fn, "of" <> r}
            case "-" <> r:
              Pr{fn, "-" <> r}
            case +u:
              +a = px(f, PkO{}, u)
              px(f, PkA{HA{fn, pr.t(a)}}, pr.r(a))
        case PkS{}:
          match ts:
            case ";" <> r:
              px(f, PkS{}, r)
            case "}" <> r:
              Pr{HEnd{}, r}
            case Nil{}:
              Pr{HEnd{}, Nil{}}
            case +u:
              +p = px(f, PkE{}, u)
              +b = px(f, PkE{}, tail(tail(pr.r(p))))
              +s = px(f, PkS{}, pr.r(b))
              Pr{HAlt{pr.t(p), pr.t(b), pr.t(s)}, pr.r(s)}

# defs ---------------------------------------------------------------------------------

type Df is Data:
  Df{n: String, ps: List<&2, String>, b: Hx}

# the tokens after a signature's last arrow outside brackets
def res.go(ts: List<&2, String>, +d: Nat, cur: List<&2, String>) -> List<&2, String>:
  match ts d:
    case Nil{} _:
      List.reverse(&2, String, cur)
    case "-" <> ">" <> t 0n:
      res.go(t, 0n, Nil{})
    case "(" <> t +k:
      res.go(t, 1n+k, "(" <> cur)
    case ")" <> t 1n+k:
      res.go(t, k, ")" <> cur)
    case x <> t +k:
      res.go(t, k, x <> cur)

# whether a signature's answer is a failure or a value
def is.part(ts: List<&2, String>) -> Bool:
  match ts:
    case "(" <> "B'Either" <> "(" <> "B'List" <> "B'Char" <> ")" <> t:
      True{}
    case _:
      False{}

type Ln is Data:
  LnSig{n: String, p: Bool}
  LnDef{d: Df}
  LnNo{}

def params(ts: List<&2, String>, +n: String, ps: List<&2, String>) -> Ln:
  match ts:
    case "=" <> t:
      LnDef{Df{n, List.reverse(&2, String, ps), pr.t(px(4000n, PkE{}, t))}}
    case x <> t:
      params(t, n, x <> ps)
    case Nil{}:
      LnNo{}

def line.ts(ts: List<&2, String>) -> Ln:
  match ts:
    case +n <> ":" <> ":" <> t:
      LnSig{n, is.part(res.go(t, 0n, Nil{}))}
    case +n <> t:
      params(t, n, Nil{})
    case Nil{}:
      LnNo{}

def line(+l: String) -> Ln:
  if.at(Ln, String.starts_with(l, "c'"), _ => line.ts(toks(l)), _ => LnNo{})

type Fs is Data:
  Fs{ds: List<&2, Df>, ps: List<&2, String>}

def fs.add(l: Ln, f: Fs) -> Fs:
  match l f:
    case LnSig{n, True{}} Fs{ds, ps}:
      Fs{ds, n <> ps}
    case LnDef{d} Fs{ds, ps}:
      Fs{d <> ds, ps}
    case _ g:
      g

def fs.of(ls: List<&2, String>, f: Fs) -> Fs:
  match ls:
    case Nil{}:
      f
    case l <> t:
      fs.of(t, fs.add(line(l), f))

def fs.part(+f: Fs, +n: String) -> Bool:
  match f:
    case Fs{ds, ps}:
      List.contains(~String, ~String.eq, ps, n)

def df.find(ds: List<&2, Df>, +n: String) -> Maybe<&2, Df>:
  match ds:
    case Nil{}:
      None{}
    case Df{+m, ps, b} <> t:
      if.at(Maybe<&2, Df>, String.eq(m, n), _ => Some{Df{m, ps, b}}, _ => df.find(t, n))

def fs.find(+f: Fs, +n: String) -> Maybe<&2, Df>:
  match f:
    case Fs{ds, ps}:
      df.find(ds, n)

# the reader -------------------------------------------------------------------------------

# what a name is: the variable at a level (counted from the outermost), an
# unevaluated lambda with its names, and in a fold's step the def whose call
# at the tail t (its parameter i), the others as they are, is the fold's
# answer, the variable at level q
type En is Data:
  ENo{}
  ELv{x: String, l: Nat, r: En}
  ECl{x: String, e: Hx, en: En, r: En}
  ERc{f: String, ps: List<&2, String>, i: Nat, t: String, q: Nat, r: En}

type Rr is Data:
  RrOk{s: String}
  RrNo{why: String}

def r1(a: Rr, +k: String) -> Rr:
  match a:
    case RrOk{s}:
      RrOk{cat([k, "{", s, "}"])}
    case RrNo{w}:
      RrNo{w}

def r2(a: Rr, b: Rr, +k: String) -> Rr:
  match a b:
    case RrOk{s} RrOk{t}:
      RrOk{cat([k, "{", s, ", ", t, "}"])}
    case RrNo{w} _:
      RrNo{w}
    case _ RrNo{w}:
      RrNo{w}

def r3(a: Rr, b: Rr, c: Rr, +k: String) -> Rr:
  match a b c:
    case RrOk{s} RrOk{t} RrOk{u}:
      RrOk{cat([k, "{", s, ", ", t, ", ", u, "}"])}
    case RrNo{w} _ _:
      RrNo{w}
    case _ RrNo{w} _:
      RrNo{w}
    case _ _ RrNo{w}:
      RrNo{w}

def prim(a: Rr, b: Rr, +p: String) -> Rr:
  r3(RrOk{cat(["C.", p, "{}"])}, a, b, "C.EPrim")

# an expression's head and arguments
def spine.h(e: Hx) -> Hx:
  match e:
    case HA{f, a}:
      spine.h(f)
    case u:
      u

def spine.as(e: Hx, acc: List<&2, Hx>) -> List<&2, Hx>:
  match e:
    case HA{f, a}:
      spine.as(f, a <> acc)
    case u:
      acc

def ev.idx(+d: Nat, l: Nat) -> Rr:
  RrOk{cat(["C.EVar{", Nat.show(Nat.sub(Nat.sub(d, 1n), l)), "n}"])}

def mem(+x: String, xs: List<&2, String>) -> Bool:
  List.contains(~String, ~String.eq, xs, x)

# whether an expression names x
def names(e: Hx, +x: String) -> Bool:
  match e:
    case HV{n}:
      String.eq(n, x)
    case HA{f, a}:
      Bool.or(names(f, x), names(a, x))
    case HL{y, b}:
      names(b, x)
    case HC{e, as}:
      Bool.or(names(e, x), names(as, x))
    case HAlt{p, b, r}:
      Bool.or(names(b, x), names(r, x))
    case _:
      False{}

def hv.is(e: Hx, +x: String) -> Bool:
  match e:
    case HV{n}:
      String.eq(n, x)
    case _:
      False{}

# whether an expression uses x, but as an argument of a call of f
def uses(e: Hx, +x: String, +f: String) -> Bool:
  match e:
    case HV{n}:
      String.eq(n, x)
    case HA{+g, +a}:
      if.at(Bool, hv.is(spine.h(g), f), _ => False{}, _ => Bool.or(uses(g, x, f), uses(a, x, f)))
    case HL{y, b}:
      uses(b, x, f)
    case HC{e2, as}:
      Bool.or(uses(e2, x, f), uses(as, x, f))
    case HAlt{p, b, r}:
      Bool.or(uses(b, x, f), uses(r, x, f))
    case _:
      False{}

# whether a recursive call's arguments are the parameters, t at i
def same.args(as: List<&2, Hx>, ps: List<&2, String>, i: Nat, +t: String) -> Bool:
  match as ps i:
    case Nil{} Nil{} _:
      True{}
    case a <> ra +p <> rp 0n:
      Bool.and(hv.is(a, t), same.args(ra, rp, 4000000000n, t))
    case a <> ra +p <> rp 1n+j:
      Bool.and(hv.is(a, p), same.args(ra, rp, j, t))
    case _ _ _:
      False{}

def index(ps: List<&2, String>, +x: String, +k: Nat) -> Maybe<&2, Nat>:
  match ps:
    case Nil{}:
      None{}
    case +p <> t:
      if.at(Maybe<&2, Nat>, String.eq(p, x), _ => Some{k}, _ => index(t, x, 1n+k))

def nth(as: List<&2, Hx>, i: Nat) -> Hx:
  match as i:
    case a <> t 0n:
      a
    case a <> t 1n+j:
      nth(t, j)
    case Nil{} _:
      HEnd{}

def drop.at(-A: Data, xs: List<&2, A>, i: Nat) -> List<&2, A>:
  match xs i:
    case x <> t 0n:
      t
    case x <> t 1n+j:
      x <> drop.at(A, t, j)
    case Nil{} _:
      Nil{}

# whether the arguments are one, () or a name nothing uses (a thunk's)
def unit.arg(as: List<&2, Hx>) -> Bool:
  match as:
    case HV{n} <> Nil{}:
      String.eq(n, "()")
    case _:
      False{}

# what ends a def's parameters' bindings: its body, or its list's fold
type Fin is Data:
  FinB{p: Bool, b: Hx}
  FinF{p: Bool, la: Hx, f: String, ps: List<&2, String>, i: Nat, z: Hx, h: String, t: String, s: Hx}

# whether a def's parameter x is used
def fin.uses(k: Fin, +x: String) -> Bool:
  match k:
    case FinB{p, b}:
      names(b, x)
    case FinF{p, la, +f, ps, i, z, h, t, s}:
      Bool.or(names(z, x), uses(s, x, f))

# a body that is a case of a list it calls itself at the tail of
type Fo is Data:
  FoF{i: Nat, z: Hx, h: String, t: String, s: Hx}
  FoB{}

def fold.at(m: Maybe<&2, Nat>, +f: String, z: Hx, h: String, t: String, +s: Hx) -> Fo:
  match m:
    case Some{i}:
      if.at(Fo, names(s, f), _ => FoF{i, z, h, t, s}, _ => FoB{})
    case None{}:
      FoB{}

def fold.of(+f: String, +ps: List<&2, String>, b: Hx) -> Fo:
  match b:
    case HC{HV{+x}, HAlt{HV{"[]"}, z, HAlt{HA{HA{HV{"(:)"}, HV{h}}, HV{t}}, +s, HEnd{}}}}:
      fold.at(index(ps, x, 0n), f, z, h, t, s)
    case _:
      FoB{}

# an expression (p: it answers a failure or a value); the rest of a def's
# parameters, bound to the call's arguments
type Rq is Data:
  QE{p: Bool, e: Hx, en: En, d: Nat}
  QB{ps: List<&2, String>, as: List<&2, Hx>, en: En, ne: En, d: Nat, k: Fin}
  QL{n: String, as: List<&2, Hx>, p: Bool, en: En, at: En, d: Nat}
  QH{h: Hx, as: List<&2, Hx>, p: Bool, en: En, d: Nat}
  QM{m: Maybe<&2, Rq>, n: String, p: Bool}
  QC{c: En, x: String, a: Hx, ps: List<&2, String>, as: List<&2, Hx>, en: En, ne: En, d: Nat, k: Fin}

# the lambda a name is, in its names; none, when it is not one
def cl.at(en: En, +n: String) -> En:
  match en:
    case ENo{}:
      ENo{}
    case ELv{+x, l, +r}:
      if.at(En, String.eq(x, n), _ => ENo{}, _ => cl.at(r, n))
    case ECl{+x, +e, +en2, +r}:
      if.at(En, String.eq(x, n), _ => ECl{x, e, en2, ENo{}}, _ => cl.at(r, n))
    case ERc{f, ps, i, t, q, +r}:
      cl.at(r, n)

def call.q(+f: String, +ps: List<&2, String>, +as: List<&2, Hx>, +p: Bool, +b: Hx, +en: En, +d: Nat, o: Fo) -> Rq:
  match o:
    case FoB{}:
      QB{ps, as, en, ENo{}, d, FinB{p, b}}
    case FoF{+i, z, h, t, s}:
      QB{drop.at(String, ps, i), drop.at(Hx, as, i), en, ENo{}, d, FinF{p, nth(as, i), f, ps, i, z, h, t, s}}

# a call of a def, its failure's reading the call's
def call(m: Maybe<&2, Df>, +as: List<&2, Hx>, +p: Bool, +fp: Bool, +en: En, +d: Nat) -> Maybe<&2, Rq>:
  match m:
    case Some{Df{+n, +ps, +b}}:
      if.at(Maybe<&2, Rq>, Bool.and(Bool.not(Bool.xor(p, fp)), Nat.is_eq(List.length(&2, String, ps), List.length(&2, Hx, as))), _ => Some{call.q(n, ps, as, p, b, en, d, fold.of(n, ps, b))}, _ => None{})
    case None{}:
      None{}

def rd(+fuel: Nat, q: Rq, +fs: Fs) -> Rr:
  match fuel:
    case 0n:
      RrNo{"fuel"}
    case 1n+f:
      match q:
        case QB{ps, as, +en, +ne, +d, +k}:
          match ps as:
            case +x <> rp HL{y, +b} <> ra:
              rd(f, QB{rp, ra, en, ECl{x, HL{y, b}, en, ne}, d, k}, fs)
            case +x <> +rp HV{+n} <> +ra:
              if.at(Rr, fin.uses(k, x), _ => rd(f, QC{cl.at(en, n), x, HV{n}, rp, ra, en, ne, d, k}, fs), _ => rd(f, QB{rp, ra, en, ne, d, k}, fs))
            case +x <> +rp +a <> +ra:
              if.at(Rr, fin.uses(k, x), _ => r2(rd(f, QE{False{}, a, en, d}, fs), rd(f, QB{rp, ra, en, ELv{x, d, ne}, 1n+d, k}, fs), "C.ELet"), _ => rd(f, QB{rp, ra, en, ne, d, k}, fs))
            case _ _:
              match k:
                case FinB{p, b}:
                  rd(f, QE{p, b, ne, d}, fs)
                case FinF{+p, la, fn, ps2, i, z, h, +t, s}:
                  r2(rd(f, QE{False{}, la, en, d}, fs), r2(rd(f, QE{p, z, ne, d}, fs), rd(f, QE{p, s, ERc{fn, ps2, i, t, 1n+d, ELv{h, d, ne}}, 1n+(1n+d)}, fs), "C.EFold"), "C.ELet")
        case QL{+n, +as, +p, +en, at, +d}:
          match at:
            case ENo{}:
              rd(f, QM{call(fs.find(fs, n), as, p, fs.part(fs, n), en, d), n, p}, fs)
            case ELv{+x, l, r}:
              if.at(Rr, String.eq(x, n), _ => if.at(Rr, Bool.or(p, Bool.not(Nat.is_eq(List.length(&2, Hx, as), 0n))), _ => RrNo{cat(["variable ", n, " called"])}, _ => ev.idx(d, l)), _ => rd(f, QL{n, as, p, en, r, d}, fs))
            case ECl{+x, HL{y, +b}, +en2, +r}:
              if.at(Rr, String.eq(x, n), _ => if.at(Rr, unit.arg(as), _ => rd(f, QE{p, b, en2, d}, fs), _ => RrNo{cat(["function ", n])}), _ => rd(f, QL{n, as, p, en, r, d}, fs))
            case ECl{+x, e, en2, +r}:
              if.at(Rr, String.eq(x, n), _ => RrNo{cat(["function ", n])}, _ => rd(f, QL{n, as, p, en, r, d}, fs))
            case ERc{+fn, +ps, +i, +t, +ql, r}:
              if.at(Rr, String.eq(fn, n), _ => if.at(Rr, same.args(as, ps, i, t), _ => ev.idx(d, ql), _ => RrNo{cat(["recursion ", n])}), _ => if.at(Rr, String.eq(t, n), _ => RrNo{cat(["tail ", n])}, _ => rd(f, QL{n, as, p, en, r, d}, fs)))
        case QC{c, +x, +a, +ps, +as, +en, +ne, +d, +k}:
          match c:
            case ECl{y, e, en2, r}:
              rd(f, QB{ps, as, en, ECl{x, e, en2, ne}, d, k}, fs)
            case _:
              r2(rd(f, QE{False{}, a, en, d}, fs), rd(f, QB{ps, as, en, ELv{x, d, ne}, 1n+d, k}, fs), "C.ELet")
        case QM{m, +n, p}:
          match m:
            case Some{q2}:
              rd(f, q2, fs)
            case None{}:
              RrNo{cat(["name ", n, if.at(String, p, _ => " (failing)", _ => "")])}
        case QE{p, +e, en, d}:
          rd(f, QH{spine.h(e), spine.as(e, Nil{}), p, en, d}, fs)
        case QH{h, as0, +p, +en, +d}:
          match h:
            case HN{k}:
              RrOk{cat(["C.ELit{", k, "n}"])}
            case HC{+s, as}:
              match as:
                case HAlt{HV{+v}, +b, HEnd{}}:
                  if.at(Rr, names(b, v), _ => r2(rd(f, QE{False{}, s, en, d}, fs), rd(f, QE{p, b, ELv{v, d, en}, 1n+d}, fs), "C.ELet"), _ => rd(f, QE{p, b, en, d}, fs))
                case HAlt{HA{HV{"Left"}, HV{+v}}, a, HAlt{HA{HV{"Right"}, HV{+w}}, b, HEnd{}}}:
                  r2(rd(f, QE{False{}, s, en, d}, fs), r2(rd(f, QE{p, a, ELv{v, d, en}, 1n+d}, fs), rd(f, QE{p, b, ELv{w, d, en}, 1n+d}, fs), "C.ECase"), "C.ELet")
                case HAlt{HV{"[]"}, a, HAlt{HA{HA{HV{"(:)"}, HV{+h}}, HV{+t}}, +b, HEnd{}}}:
                  if.at(Rr, names(b, t), _ => RrNo{"a list's tail"}, _ => r2(rd(f, QE{False{}, s, en, d}, fs), r2(rd(f, QE{p, a, en, d}, fs), rd(f, QE{p, b, ELv{h, d, en}, 1n+(1n+d)}, fs), "C.EFold"), "C.ELet"))
                case _:
                  RrNo{"a case"}
            case HV{+n}:
              match as0:
                case Nil{}:
                  if.at(Rr, String.eq(n, "[]"), _ => RrOk{"C.ENil{}"}, _ => if.at(Rr, String.eq(n, "()"), _ => RrOk{"C.EUnit{}"}, _ => rd(f, QL{n, Nil{}, p, en, en, d}, fs)))
                case +a <> Nil{}:
                  if.at(Rr, String.eq(n, "Left"), _ => if.at(Rr, p, _ => RrOk{"C.EErr{}"}, _ => r1(rd(f, QE{False{}, a, en, d}, fs), "C.EInl")), _ =>
                    if.at(Rr, String.eq(n, "Right"), _ => if.at(Rr, p, _ => rd(f, QE{False{}, a, en, d}, fs), _ => r1(rd(f, QE{False{}, a, en, d}, fs), "C.EInr")), _ =>
                      if.at(Rr, String.eq(n, "b'HsPrelude'HsList'fst"), _ => r1(rd(f, QE{False{}, a, en, d}, fs), "C.EFst"), _ =>
                        if.at(Rr, String.eq(n, "b'HsPrelude'HsList'snd"), _ => r1(rd(f, QE{False{}, a, en, d}, fs), "C.ESnd"), _ =>
                          if.at(Rr, Bool.and(p, String.eq(n, "b'HsPrelude'HsList'error")), _ => RrOk{"C.EErr{}"}, _ => rd(f, QL{n, [a], p, en, en, d}, fs))))))
                case +a <> HL{+x, +k} <> Nil{}:
                  if.at(Rr, Bool.and(p, String.eq(n, "b'hs'either'bind")), _ => r2(rd(f, QE{True{}, a, en, d}, fs), rd(f, QE{True{}, k, ELv{x, d, en}, 1n+d}, fs), "C.ELet"), _ => RrNo{cat(["name ", n])})
                case +a <> +b <> Nil{}:
                  if.at(Rr, String.eq(n, "(:)"), _ => r2(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "C.ECons"), _ =>
                    if.at(Rr, String.eq(n, "(,)"), _ => r2(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "C.EPair"), _ =>
                      if.at(Rr, String.eq(n, "b'Nat'is_lt"), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PLt"), _ =>
                        if.at(Rr, String.eq(n, "b'Nat'add"), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PAdd"), _ =>
                          if.at(Rr, String.eq(n, "b'Nat'sub"), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PSubT"), _ =>
                            if.at(Rr, String.eq(n, "b'Nat'div"), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PDivT"), _ =>
                              if.at(Rr, String.eq(n, "b'Nat'mod"), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PModT"), _ =>
                                if.at(Rr, Bool.and(p, String.eq(n, "b'HsPrelude'HsNum'sub")), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PSub"), _ =>
                                  if.at(Rr, Bool.and(p, String.eq(n, "b'HsPrelude'HsNum'div")), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PDiv"), _ =>
                                    if.at(Rr, Bool.and(p, String.eq(n, "b'HsPrelude'HsNum'mod")), _ => prim(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{False{}, b, en, d}, fs), "PMod"), _ =>
                                      rd(f, QL{n, [a, b], p, en, en, d}, fs)))))))))))
                case +a <> HL{x, +b} <> HL{y, +c} <> Nil{}:
                  if.at(Rr, String.eq(n, "b'Bool'if"), _ => r3(rd(f, QE{False{}, a, en, d}, fs), rd(f, QE{p, b, en, d}, fs), rd(f, QE{p, c, en, d}, fs), "C.EIf"), _ => RrNo{cat(["name ", n])})
                case HL{+x, HL{+y, +b}} <> +z <> +xs <> Nil{}:
                  if.at(Rr, String.eq(n, "Cata.Base.c'foldr"), _ => r2(rd(f, QE{False{}, xs, en, d}, fs), r2(rd(f, QE{p, z, en, d}, fs), rd(f, QE{p, b, ELv{y, 1n+d, ELv{x, d, en}}, 1n+(1n+d)}, fs), "C.EFold"), "C.ELet"), _ => rd(f, QL{n, [HL{x, HL{y, b}}, z, xs], p, en, en, d}, fs))
                case as:
                  rd(f, QL{n, as, p, en, en, d}, fs)
            case _:
              RrNo{"an expression"}

# def dN: \x0 -> body, its one argument the innermost variable
def def.ex(m: Maybe<&2, Df>, +fs: Fs, +p: Bool) -> Rr:
  match m:
    case Some{Df{n, ps, b}}:
      match ps:
        case +x <> Nil{}:
          rd(400n, QE{p, b, ELv{x, 0n, ENo{}}, 1n}, fs)
        case _:
          RrNo{"not of one argument"}
    case None{}:
      RrNo{"no such def"}

def row(+n: String, r: Rr) -> String:
  match r:
    case RrOk{s}:
      cat([n, "\t", s])
    case RrNo{w}:
      cat([n, "\tOUT ", w])

def rows(ns: List<String>, +fs: Fs) -> IO(Unit):
  match ns:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +n <> t:
      +d = {cat(["c'd", n]) : String}
      do IO<Unit>:
        IO.print(row(n, def.ex(fs.find(fs, d), fs, fs.part(fs, d))))
        rows(t, fs)

# input and output ------------------------------------------------------------------------------

type Fr is Type:
  Fr{f: File, acc: List<&2, String>, more: Bool}

def fr.res(g: File, x: Result<&1, &1, U32 & String, String>, acc: List<&2, String>) -> IO(Fr):
  match x:
    case Fail{(c, m)}:
      do IO<Fr>:
        File.close(g)
        IO.die(Fr, 1, "rd: read failed: " ++ m)
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
      IO.die(String, 1, "rd: cannot open a file: " ++ m)
    case Done{f}:
      fr.go(4096n, Fr{f, Nil{}, True{}})

def read(path: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    fr.opened(r)

def run(args: List<String>) -> IO(Unit):
  match args:
    case f <> ns:
      do IO<Unit>:
        s : String <- read(f)
        rows(ns, fs.of(String.lines(s), Fs{Nil{}, Nil{}}))
    case Nil{}:
      IO.print("usage: rd FILE.hs N...")

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    run(List.tail(&1, String, argv))
