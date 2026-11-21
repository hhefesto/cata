-- | iterate f x !! n, as telomare writes it (Telomare.IR.Base's
-- i2CB/varB, Expand's accessAt, Machine's sizedRecursionChain): the
-- specialiser writes each as Cata.Base's iterateIndex f x n.
module Iter where

data B = Env | R B | L B
  deriving (Eq, Show)

-- | varB: the n-th right of the environment, then a left
varB :: Int -> B
varB n = L (iterate R Env !! n)

-- | a lambda over a parameter (accessAt's shape)
wrapAt :: Int -> Int -> [Int] -> [Int]
wrapAt k n xs = iterate (\ys -> k : ys) xs !! n

pow2 :: Int -> Int
pow2 n = iterate (* 2) 1 !! n

-- | under a ($) and a pure, the index a pattern's variable
chain :: (Int, Int) -> Maybe Int
chain (c, x) = pure $ iterate (+ x) 0 !! c

ex1 :: B
ex1 = varB 3

ex2 :: [Int]
ex2 = wrapAt 7 2 [1]

ex3 :: Int
ex3 = pow2 10

ex4 :: Maybe Int
ex4 = chain (4, 5)
