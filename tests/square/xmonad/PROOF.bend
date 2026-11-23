# The proofs of PROPOSED.bend's squares: each a case split as deep as the
# two functions match, then {==} (both sides compute to one term), and a
# lemma by induction where F maps over a list W walks. Nothing here is
# trusted: `bend PROOF.bend --verdict` rechecks them with BendTT's kernel.

import Base
import ./l/XMonad_StackSet.bend as F
import ./l/HsPrelude.bend as H
import ./xb/StackSet.bend as W
import ./xb/Num.bend as N
import ./PROPOSED.bend as Proposed

def Proposed.sq.reverseStack(A, s):
  match s:
    case F.Stack.Stack{f, u, d}:
      {==}

def Proposed.sq.integrate(A, s):
  match s:
    case F.Stack.Stack{f, u, d}:
      {==}

def Proposed.sq.integrate_q(A, m):
  match m:
    case None{}:
      {==}
    case Some{s}:
      match s:
        case F.Stack.Stack{f, u, d}:
          {==}

def Proposed.sq.differentiate(A, xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def Proposed.sq.swapUp_q(A, s):
  match s:
    case F.Stack.Stack{f, u, d}:
      match u:
        case Nil{}:
          {==}
        case l <> ls:
          {==}


def Proposed.sq.focus(A, s):
  match s:
    case F.Stack.Stack{f, u, d}:
      {==}

def Proposed.sq.tag(I, L, A, w):
  match w:
    case F.Workspace.Workspace{t, l, m}:
      {==}

def Proposed.sq.stack(I, L, A, w):
  match w:
    case F.Workspace.Workspace{t, l, m}:
      {==}

def Proposed.sq.current(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      {==}

def Proposed.sq.floating(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      {==}

def Proposed.sq.peek(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          match w:
            case F.Workspace.Workspace{t, l, m}:
              match m:
                case None{}:
                  {==}
                case Some{st}:
                  match st:
                    case F.Stack.Stack{x, u, d}:
                      {==}

def Proposed.sq.index(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          match w:
            case F.Workspace.Workspace{t, l, m}:
              match m:
                case None{}:
                  {==}
                case Some{st}:
                  match st:
                    case F.Stack.Stack{x, u, d}:
                      {==}

def Proposed.sq.screens(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      {==}

def Proposed.sq.currentTag(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          match w:
            case F.Workspace.Workspace{t, l, m}:
              {==}

def Proposed.sq.swapUp(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          match w:
            case F.Workspace.Workspace{t, l, m}:
              match m:
                case None{}:
                  {==}
                case Some{st}:
                  match st:
                    case F.Stack.Stack{x, u, d}:
                      match u:
                        case Nil{}:
                          {==}
                        case y <> ys:
                          {==}

def Proposed.sq.wss.lemma(I, L, A, S, D, v, h):
  match v:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          %Proposed.sq.wss.lemma(I, L, A, S, D, t, h) : {Proposed.phi.ws(I, L, A, w) <> Proposed.phi.wss(I, L, A, List.append(&2, F.Workspace<I, L, A>, F.hs.map(~F.Screen<I, L, A, S, D>, ~F.Workspace<I, L, A>, ~x_1 => F.workspace(I, L, A, S, D, x_1), t), h)) == Proposed.phi.ws(I, L, A, w) <> _ : List<&2, W.Workspace<I, L, A>>}
          {==}

def Proposed.sq.workspaces(I, L, A, S, D, s):
  match s:
    case F.StackSet.StackSet{c, v, h, f}:
      match c:
        case F.Screen.Screen{w, sid, sd}:
          %Proposed.sq.wss.lemma(I, L, A, S, D, v, h) : {Proposed.phi.ws(I, L, A, w) <> Proposed.phi.wss(I, L, A, List.append(&2, F.Workspace<I, L, A>, F.hs.map(~F.Screen<I, L, A, S, D>, ~F.Workspace<I, L, A>, ~x_1 => F.workspace(I, L, A, S, D, x_1), v), h)) == Proposed.phi.ws(I, L, A, w) <> _ : List<&2, W.Workspace<I, L, A>>}
          {==}
