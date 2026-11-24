module Lazy where

-- Haskell is lazy, Bend strict.  A partial call whose answer is never
-- forced must not make F's def fail where h answers: Fold's float-in
-- (fd.fi) moves a let into the one branch that takes it, drops a let
-- nothing takes, and takes fst and snd of a pair written out, so these
-- answer where GHC's do (before it all but constHead and both failed a
-- law at an input that does not force the partial call, and were out).
-- takeOne and lengthDivs need a lazy list (map's elements unforced) and
-- stay out.

unusedHead :: [Int] -> Int -> Int
unusedHead xs n = let h = head xs in if n == 0 then 0 else h

constHead :: [Int] -> Int
constHead xs = const 1 (head xs)

fstPair :: [Int] -> Int
fstPair xs = fst (1, head xs)

unusedDiv :: Int -> Int -> Int
unusedDiv a b = let q = a `div` b in if b == 0 then 7 else q

deadLet :: [Int] -> Int
deadLet xs = let h = head xs in 5

nested :: [Int] -> Int -> Int -> Int
nested xs a b = let h = head xs in if a == 0 then 1 else if b == 0 then 2 else h

takeOne :: [Int] -> [Int]
takeOne xs = take 1 (map (\x -> 10 `div` x) xs)

lengthDivs :: [Int] -> Int
lengthDivs xs = length (map (\x -> 10 `div` x) xs)

whereHead :: [Int] -> Bool -> Int
whereHead xs b = if b then h else 0
  where h = head xs

both :: [Int] -> Bool -> Int
both xs b = let h = head xs in if b then h else h + 1
