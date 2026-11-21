{-# LANGUAGE DeriveTraversable #-}

-- | base's instances at pairs, (,) w, as telomare uses them: Resolve's
-- deferLift (a fold whose answer is (DeferMap, term), sequence at a
-- derived Traversable in the pair's Applicative, g <$> a <*> b), EAL's
-- fmap at a pair, Expand's traverse at a pair.
module Pair where

newtype Log = Log [Int]
  deriving (Eq, Show)

instance Semigroup Log where
  Log a <> Log b = Log (a ++ b)

instance Monoid Log where
  mempty = Log []

data T a = Leaf Int | Node a a | Wrap Int a
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | each leaf logged, a Wrap's number added to its child's
step :: T (Log, Int) -> (Log, Int)
step (Leaf n) = (Log [n], n)
step (Node a b) = (+) <$> a <*> b
step (Wrap k a) = (+ k) <$> a

logged :: Int -> (Log, Int)
logged n = (Log [n], n)

both :: Int -> Int -> (Log, Int)
both a b = (+) <$> logged a <*> logged b

-- | sequence in the pair's Applicative (deferLift's)
seqT :: T (Log, Int) -> (Log, T Int)
seqT t = sequence t

pureL :: Int -> (Log, Int)
pureL = pure

second' :: (Int, Int) -> (Int, Int)
second' = fmap (* 2)

-- | traverse at a pair, in Maybe
half :: (Int, Int) -> Maybe (Int, Int)
half = traverse (\x -> if x > 0 then Just (x `div` 2) else Nothing)

ex1 :: (Log, Int)
ex1 = both 2 3

ex2 :: (Log, T Int)
ex2 = seqT (Node (logged 1) (logged 2))

ex3 :: (Log, Int)
ex3 = step (Wrap 5 (logged 4))

ex4 :: Maybe (Int, Int)
ex4 = half (1, 8)
