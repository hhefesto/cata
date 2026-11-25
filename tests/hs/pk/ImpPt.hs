module ImpPt where

data P = A Int | B P P | C
  deriving (Eq, Show)

norm :: P -> P
norm p = case p of
  B a C -> norm a
  B a b -> B (norm a) (norm b)
  q -> q

total :: P -> Int
total p = case p of
  A n -> n
  B a b -> total a + total b
  C -> error "total: C"

-- point-free, partial
weight :: P -> Int
weight = (* 2) . total . norm

-- a partial def that answers a function (Size.IR's liftShowsPrec)
showP :: P -> ShowS
showP p = case p of
  A n -> showString "A " . shows n
  B a b -> showChar '(' . showP a . showString ", " . showP b . showChar ')'
  C -> error "showP: unexpected C"

render :: P -> String
render p = showP p ""
