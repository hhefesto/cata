# Squares between cata's XMonad.StackSet and xmonad-bend's hand port,
# proposed for the human to move into a LAWS.bend (or reword or drop);
# PROOF.bend proves them.
#
# F is cata's fold of xmonad-0.18.1's XMonad.StackSet (a law run's
# XMonad_StackSet.bend, ./l), W is ~/src/xmonad-bend's StackSet.bend (./xb),
# written by hand. phi takes each of F's types to W's, field by field (a
# Data.Map of floating windows to W's ascending list of them; GHC's Rational
# to Num.bend's Rat). Each law is a commuting square: phi after F's function
# is W's function after phi,
#
#   phi(F.h(x)) == W.b(phi(x))      for every x,
#
# so W.b implements cata's translation of h on all inputs, not only on the
# example inputs GHC answered (F.h's own laws hold h's answers there). Its
# statement is fixed by the pair (F.h, W.b) and phi alone; only the pairing
# and phi are choices (tests/square/run.zsh pairs one function wrongly, as a
# mutant, and the proof must fail).

import Base
import ./l/XMonad_StackSet.bend as F
import ./l/HsPrelude.bend as H
import ./xb/StackSet.bend as W
import ./xb/Num.bend as N

# phi: cata's XMonad.StackSet types (F) to xmonad-bend's (W), field by field

def phi.stack(-A: Data, s: F.Stack<A>) -> W.Stack<A>:
  match s:
    case F.Stack.Stack{f, u, d}:
      W.Stack{f, u, d}

def phi.mstack(-A: Data, m: Maybe<&2, F.Stack<A>>) -> Maybe<&2, W.Stack<A>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{phi.stack(A, s)}

def phi.ws(-I: Data, -L: Data, -A: Data, w: F.Workspace<I, L, A>) -> W.Workspace<I, L, A>:
  match w:
    case F.Workspace.Workspace{t, l, m}:
      W.Workspace{t, l, phi.mstack(A, m)}

def phi.wss(-I: Data, -L: Data, -A: Data, ws: List<&2, F.Workspace<I, L, A>>) -> List<&2, W.Workspace<I, L, A>>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> t:
      phi.ws(I, L, A, w) <> phi.wss(I, L, A, t)

def phi.scr(-I: Data, -L: Data, -A: Data, -S: Data, -D: Data, c: F.Screen<I, L, A, S, D>) -> W.Screen<I, L, A, S, D>:
  match c:
    case F.Screen.Screen{w, s, d}:
      W.Screen{phi.ws(I, L, A, w), s, d}

def phi.scrs(-I: Data, -L: Data, -A: Data, -S: Data, -D: Data, cs: List<&2, F.Screen<I, L, A, S, D>>) -> List<&2, W.Screen<I, L, A, S, D>>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      phi.scr(I, L, A, S, D, c) <> phi.scrs(I, L, A, S, D, t)

def phi.int(i: H.HsInt) -> N.Int:
  match i:
    case H.HsInt.Pos{n}:
      N.Int.Pos{n}
    case H.HsInt.Neg{n}:
      N.Int.Neg{n}

def phi.rat(r: H.HsRational) -> N.Rat:
  match r:
    case H.HsRational{n, d}:
      N.Rat{phi.int(n), d}

def phi.rr(r: F.RationalRect) -> W.RationalRect:
  match r:
    case F.RationalRect.RationalRect{x, y, w, h}:
      W.RationalRect{phi.rat(x), phi.rat(y), phi.rat(w), phi.rat(h)}

def phi.fl(-A: Data, m: H.HsMap<A, F.RationalRect>) -> List<&2, W.Float<A>>:
  match m:
    case H.HsMap.Tip{}:
      Nil{}
    case H.HsMap.Bin{k, v, rest}:
      W.Float{k, phi.rr(v)} <> phi.fl(A, rest)

def phi.ss(-I: Data, -L: Data, -A: Data, -S: Data, -D: Data, s: F.StackSet<I, L, A, S, D>) -> W.StackSet<I, L, A, S, D>:
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      W.StackSet{phi.scr(I, L, A, S, D, c), phi.scrs(I, L, A, S, D, v), phi.wss(I, L, A, h), phi.fl(A, f)}

# Squares
# -------

law sq.reverseStack:
  for -A: Data
  for s: F.Stack<A>
  {phi.stack(A, F.reverseStack(A, s)) == W.Stack.reverse(A, phi.stack(A, s)) : W.Stack<A>}

law sq.integrate:
  for -A: Data
  for s: F.Stack<A>
  {F.integrate(A, s) == W.Stack.integrate(A, phi.stack(A, s)) : List<&2, A>}

law sq.integrate_q:
  for -A: Data
  for m: Maybe<&2, F.Stack<A>>
  {F.integrate_q(A)(m) == W.Stack.integrate.maybe(A, phi.mstack(A, m)) : List<&2, A>}

law sq.differentiate:
  for -A: Data
  for xs: List<&2, A>
  {phi.mstack(A, F.differentiate(A, xs)) == W.Stack.differentiate(A, xs) : Maybe<&2, W.Stack<A>>}

law sq.swapUp_q:
  for -A: Data
  for s: F.Stack<A>
  {phi.stack(A, F.swapUp_q(A, s)) == W.Stack.swapUp(A, phi.stack(A, s)) : W.Stack<A>}

law sq.focus:
  for -A: Data
  for s: F.Stack<A>
  {F.focus(A, s) == W.Stack.focus(A, phi.stack(A, s)) : A}

law sq.tag:
  for -I: Data
  for -L: Data
  for -A: Data
  for w: F.Workspace<I, L, A>
  {F.tag(I, L, A, w) == W.Workspace.tag(I, L, A, phi.ws(I, L, A, w)) : I}

law sq.stack:
  for -I: Data
  for -L: Data
  for -A: Data
  for w: F.Workspace<I, L, A>
  {phi.mstack(A, F.stack(I, L, A, w)) == W.Workspace.stack(I, L, A, phi.ws(I, L, A, w)) : Maybe<&2, W.Stack<A>>}

law sq.current:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {phi.scr(I, L, A, S, D, F.current(I, L, A, S, D, s)) == W.current(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : W.Screen<I, L, A, S, D>}

law sq.floating:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {phi.fl(A, F.floating(I, L, A, S, D, s)) == W.floating(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : List<&2, W.Float<A>>}

law sq.peek:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {F.peek(I, L, A, S, D)(s) == W.peek(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : Maybe<&2, A>}

law sq.index:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {F.index(I, L, A, S, D)(s) == W.index(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : List<&2, A>}

law sq.screens:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {phi.scrs(I, L, A, S, D, F.screens(I, L, A, S, D, s)) == W.screens(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : List<&2, W.Screen<I, L, A, S, D>>}

law sq.currentTag:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {F.currentTag(I, L, A, S, D)(s) == W.currentTag(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : I}

law sq.swapUp:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {phi.ss(I, L, A, S, D, F.swapUp(I, L, A, S, D)(s)) == W.swapUp(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : W.StackSet<I, L, A, S, D>}

# workspaces: F maps workspace over the visible screens and appends the
# hidden ones; W walks the screens. The lemma by induction on the screens.
law sq.wss.lemma:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for v: List<&2, F.Screen<I, L, A, S, D>>
  for h: List<&2, F.Workspace<I, L, A>>
  {phi.wss(I, L, A, List.append(&2, F.Workspace<I, L, A>, F.hs.map(~F.Screen<I, L, A, S, D>, ~F.Workspace<I, L, A>, ~x_1 => F.workspace(I, L, A, S, D, x_1), v), h)) == W.Screen.workspaces(I, L, A, S, D, phi.scrs(I, L, A, S, D, v), phi.wss(I, L, A, h)) : List<&2, W.Workspace<I, L, A>>}

law sq.workspaces:
  for -I: Data
  for -L: Data
  for -A: Data
  for -S: Data
  for -D: Data
  for s: F.StackSet<I, L, A, S, D>
  {phi.wss(I, L, A, F.workspaces(~I, ~L, ~A, ~S, ~D, s)) == W.workspaces(I, L, A, S, D, phi.ss(I, L, A, S, D, s)) : List<&2, W.Workspace<I, L, A>>}

