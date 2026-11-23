# The proofs of PROPOSED.bend's squares.  myOr and squish by induction on
# the list; myReverse (F appends each head at the end, W's List.reverse
# carries an accumulator) by two lemmas on Base's List.append, a list
# with Nil after it is itself and append is associative, and a third that
# generalises the accumulator.  Nothing here is trusted: `bend PROOF.bend
# --verdict` rechecks them with BendTT's kernel.

import Base
import ./l/ChapterExercises.bend as F
import ./w/W.bend as W
import ./PROPOSED.bend as Proposed

def Proposed.sq.myOr(xs):
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case True{}:
          {==}
        case False{}:
          Proposed.sq.myOr(t)

def Proposed.sq.squish(A, xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %Proposed.sq.squish(A, t) : {List.append(&2, A, x, F.squish(A, t)) == List.append(&2, A, x, _) : List<&2, A>}
      {==}

# r ++ [] == r
def lem.nil(-A: Data, r: List<&2, A>) -> {List.append(&2, A, r, Nil{}) == r : List<&2, A>}:
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      %lem.nil(A, t) : {h <> List.append(&2, A, t, Nil{}) == h <> _ : List<&2, A>}
      {==}

# r ++ (ys ++ zs) == (r ++ ys) ++ zs
def lem.assoc(-A: Data, r: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, r, List.append(&2, A, ys, zs)) == List.append(&2, A, List.append(&2, A, r, ys), zs) : List<&2, A>}:
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      %lem.assoc(A, t, ys, zs) : {h <> List.append(&2, A, t, List.append(&2, A, ys, zs)) == h <> _ : List<&2, A>}
      {==}

# F's reverse with acc after it is W's reverse with the accumulator acc
def lem.go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) -> {List.append(&2, A, F.myReverse(A, xs), acc) == List.reverse.go(&2, A, xs, acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %lem.assoc(A, F.myReverse(A, t), h <> Nil{}, acc) : {_ == List.reverse.go(&2, A, t, h <> acc) : List<&2, A>}
      lem.go(A, t, h <> acc)

def Proposed.sq.myReverse(A, xs):
  %lem.nil(A, F.myReverse(A, xs)) : {_ == List.reverse.go(&2, A, xs, Nil{}) : List<&2, A>}
  lem.go(A, xs, Nil{})
