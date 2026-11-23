# Squares between cata's fold of hs1003's 00038 (ChapterExercises, F: a
# law run's 00038.bend as ./l/ChapterExercises.bend) and a hand-written
# Bend of three of its functions (W: ./w/W.bend), proposed for the human
# to move into a LAWS.bend (or reword or drop); PROOF.bend proves them.
# phi is the identity here (both sides use Base's lists and Bool), so
# each square is
#
#   F.h(x) == W.b(x)      for every x.
#
# A third pairing for tests/adjoint/run.zsh, outside xmonad: the checker
# takes any pairing whose squares are written so.

import Base
import ./l/ChapterExercises.bend as F
import ./w/W.bend as W

law sq.myOr:
  for xs: List<&2, Bool>
  {F.myOr(xs) == W.orL(xs) : Bool}

law sq.squish:
  for -A: Data
  for xs: List<&2, List<&2, A>>
  {F.squish(A, xs) == W.concatL(A, xs) : List<&2, A>}

law sq.myReverse:
  for -A: Data
  for +xs: List<&2, A>
  {F.myReverse(A, xs) == W.rev(A, xs) : List<&2, A>}
