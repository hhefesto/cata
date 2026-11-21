{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module ShowFix where

-- cata's rule for data-fix's Show at Fix f (through f's Show1): Base's
-- model's fixShowsPrec, a fold to the text a node shows unparenthesised.
-- The functors are telomare's shapes (IR.Base's BasicExprF and StuckF,
-- their hand-written Show1, which shows its text with `shows`) and one
-- whose Show1 reads the precedence.

import Data.Fix (Fix (..))
import Data.Functor.Classes (Show1 (..))

data BasicF f
  = ZeroSF
  | PairSF f f
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Show1 BasicF where
  liftShowsPrec showsPrec' _showList _prec = \case
    ZeroSF -> shows "ZeroSF"
    PairSF a b -> shows "PairSF (" . showsPrec' 0 a . shows ", " . showsPrec' 0 b . shows ")"

data StuckF f
  = DeferSF Int f
  | EnvSF
  | LeftSF f
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Show1 StuckF where
  liftShowsPrec showsPrec' _showList _prec = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . showsPrec' 0 x . shows ")"
    EnvSF -> shows "EnvSF"
    LeftSF x -> shows "LeftSF (" . showsPrec' 0 x . shows ")"

-- a Show1 that reads the precedence, as a derived one would
data TreeF f
  = Leaf Int
  | Node f f
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Show1 TreeF where
  liftShowsPrec sp _ d (Leaf n) = showParen (d > 10) (showString "Leaf " . showsPrec 11 n)
  liftShowsPrec sp _ d (Node a b) = showParen (d > 10) (showString "Node " . sp 11 a . showChar ' ' . sp 11 b)

type Basic = Fix BasicF

zero :: Basic
zero = Fix ZeroSF

pair :: Basic -> Basic -> Basic
pair a b = Fix (PairSF a b)

-- a pair per character, nested to the right
nest :: String -> Basic
nest [] = zero
nest (_ : cs) = pair zero (nest cs)

-- IR.Base's convertAbortMessage's shape: the term a message names, shown
message :: Basic -> String
message = \case
  Fix (PairSF (Fix ZeroSF) t) -> "recursion overflow for rt: " <> show t
  x -> "unexpected abort: " <> show x

ex1 :: String -> String
ex1 n = show (nest n)

ex2 :: String -> String
ex2 n = message (pair zero (nest n))

ex3 :: String -> String
ex3 n = message (pair (nest n) zero)

ex4 :: Int -> String
ex4 n = show (Fix (DeferSF n (Fix (LeftSF (Fix EnvSF)))))

tree :: [Int] -> Fix TreeF
tree [] = Fix (Leaf 0)
tree (n : ns) = Fix (Node (tree ns) (Fix (Leaf n)))

ex5 :: [Int] -> String
ex5 n = show (tree n)

ex6 :: [Int] -> String -> String
ex6 ns s = showsPrec 11 (tree ns) ("!" <> shows [nest s, zero] "")

-- show at a class's type variable, copied at Fix (convertAbortMessage is
-- over its g, Show g among its classes)
describe :: Show g => g -> String
describe x = "term: " <> show x

ex7 :: String -> String
ex7 s = describe (nest s)
