-- tests/hs/MuTpl.hs: recursion through lifted defs that keep a function
-- argument.  wordsWhen's case on a computed value and its where-bound
-- pair are lifted defs, each taking p (a template in Bend), and they call
-- wordsWhen back: a cycle Bend takes only as one def (a template calls
-- only templates declared above it).  Fold merges it (fd.mu, the group's
-- templates kept in front of the fuel, 11-23); before, hs1003 had 23
-- defs out on it, law:- "expected a term, observed '~'".  The callers at
-- a known function (splitSpaces, splitCommas, pairsOf, firstBig) have
-- the laws; the defs with a function argument have none (no input of a
-- function type).
module MuTpl where

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s = case dropWhile p s of
  "" -> []
  s' -> w : wordsWhen p s''
    where (w, s'') = break p s'

splitSpaces :: String -> [String]
splitSpaces = wordsWhen (== ' ')

splitCommas :: String -> [String]
splitCommas s = wordsWhen (== ',') s

myUnfoldr :: (b -> Maybe (a, b)) -> b -> [a]
myUnfoldr f b = case f b of
  Nothing -> []
  Just (a, b') -> a : myUnfoldr f b'

step2 :: [Int] -> Maybe ((Int, Int), [Int])
step2 (a : b : r) = Just ((a, b), r)
step2 _ = Nothing

pairsOf :: [Int] -> [(Int, Int)]
pairsOf = myUnfoldr step2

firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust f xs = case xs of
  [] -> Nothing
  (y : ys) -> case f y of
    Just z -> Just z
    Nothing -> firstJust f ys

big :: Int -> Maybe Int
big x = if x > 3 then Just x else Nothing

firstBig :: [Int] -> Maybe Int
firstBig = firstJust big
