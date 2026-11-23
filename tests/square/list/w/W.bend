# A hand-written Bend of three of hs1003's 00038 (ChapterExercises) list
# functions, written apart from cata's fold of them (F: a law run's
# 00038.bend, as ./l/ChapterExercises.bend: a path's names may not start
# with a digit): a third pairing for tests/adjoint/run.zsh, outside
# xmonad.  Each is written another way than F writes it: or by a match on
# the head (F: Bool.or), squish as Base's List.concat and reverse as
# Base's List.reverse (an accumulator; F's myReverse appends each head at
# the end).

import Base

def orL(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case True{}:
          True{}
        case False{}:
          orL(t)

def concatL(-A: Data, xss: List<&2, List<&2, A>>) -> List<&2, A>:
  List.concat(&2, A, xss)

def rev(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  List.reverse(&2, A, xs)

