# List functions at a function that uses its accumulator, or the element,
# more than once (a lambda's +): HsList's foldr and foldl, whose answer may
# be a function, and Base's List.any and List.all take it once (Fold.bend's
# fd.cp.name writes these where the lambda copies and the answer is Data)
def HsList.foldrc(~A: Data, ~B: Data, ~f: A -> B -> B, xs: List<&2, A>, z: B) -> B:
  match xs:
    case Nil{}:
      z
    case +h <> t:
      +r = HsList.foldrc(~A, ~B, ~f, t, z)
      f(h)(r)

def HsList.foldlc(~A: Data, ~B: Data, ~f: B -> A -> B, xs: List<&2, A>, +acc: B) -> B:
  match xs:
    case Nil{}:
      acc
    case +h <> t:
      HsList.foldlc(~A, ~B, ~f, t, f(acc)(h))

def HsList.anyc(~a: Quant, ~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +h <> t:
      HsBool.if(Bool, p(h), _ => True{}, _ => HsList.anyc(~a, ~A, ~p, t))

def HsList.allc(~a: Quant, ~A: Data, ~p: A -> Bool, xs: List<&2, A>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      HsBool.if(Bool, p(h), _ => HsList.allc(~a, ~A, ~p, t), _ => False{})

