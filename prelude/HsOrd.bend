# Data.Ord's comparing: an Ord's compare on a key (Fold.bend's
# fd.bftab2.ord; the survey had it as base it maps, the fold had not)
def HsList.comparing(~K: Data, ~A: Data, ~cmp: K -> K -> Cmp, ~f: A -> K, x: A, y: A) -> Cmp:
  cmp(f(x))(f(y))

# Integral's even and odd at Int (Fold.bend's BfParity)
def HsInt.even(+x: HsInt) -> Bool:
  HsInt.is_eq(HsInt.rem(x, HsInt.Pos{2n}), HsInt.Pos{0n})

def HsInt.odd(+x: HsInt) -> Bool:
  Bool.not(HsInt.even(x))
