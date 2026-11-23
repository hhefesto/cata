# Squares between cata's XMonad.Config and xmonad-bend's Core.bend (its
# default config, cfg.*), proposed for the human to move into a LAWS.bend
# (or reword or drop); PROOF.bend proves them.  A second pairing for
# tests/adjoint/run.zsh, the general checker (the first: ../xmonad, the
# StackSet).
#
# F is cata's fold of xmonad-0.18.1's XMonad.Config (a law run's
# XMonad_Config.bend, ./l), W is ~/src/xmonad-bend's Core.bend (./xc, at
# 551bdaf), written by hand.  phi takes F's String (a list of characters,
# as cata writes Haskell's) to W's (Bend's String).  Each law is a square,
# phi after F's value is W's: here the five values of the default config
# law run answered for.

import Base
import ./l/XMonad_Config.bend as F
import ./xc/Core.bend as W

def phi.str(cs: List<&2, Char>) -> String:
  String.from_list(cs)

law sq.normalBorderColor:
  {phi.str(F.normalBorderColor()) == W.cfg.normalBorderColor() : String}

law sq.focusedBorderColor:
  {phi.str(F.focusedBorderColor()) == W.cfg.focusedBorderColor() : String}

law sq.terminal:
  {phi.str(F.terminal()) == W.cfg.terminal() : String}

law sq.focusFollowsMouse:
  {F.focusFollowsMouse() == W.cfg.focusFollowsMouse() : Bool}

law sq.clickJustFocuses:
  {F.clickJustFocuses() == W.cfg.clickJustFocuses() : Bool}
