-- | Alternative at Maybe: <|> (the first Just) and empty, as telomare's
-- Machine (unsizedTestSuper, gateSuperResult) and EAL (mergeTagInfo)
-- use them.
module Alt where

import Control.Applicative (Alternative (..))

firstOf :: Maybe Int -> Maybe Int -> Maybe Int
firstOf a b = a <|> b

three :: Maybe Int -> Maybe Int -> Maybe Int -> Maybe Int
three a b c = a <|> b <|> c

none :: Maybe Bool
none = empty

-- | a lookup, else a default, else nothing
pick :: Int -> [(Int, Int)] -> Maybe Int
pick k xs = lookup k xs <|> lookup (k + 1) xs <|> empty

orZero :: Maybe Int -> Int
orZero m = case m <|> Just 0 of
  Just x -> x
  Nothing -> 1

ex1 :: Maybe Int
ex1 = firstOf Nothing (Just 3)

ex2 :: Maybe Int
ex2 = pick 2 [(3, 30), (1, 10)]
