-- a local function that takes a function, used at functions over run-time
-- locals and at two types (EAL's instantiateTemplate: shKV)
module LocHof where

import qualified Data.Map as Map

data T = V Int | P T T | D
  deriving (Eq, Show)

inst :: Int -> Map.Map Int T -> [(Int, Int)] -> (Map.Map Int T, [(Int, Int)])
inst base ts es = (Map.union (Map.fromAscList (fmap (shKV shT) (Map.toList ts))) ts, fmap (shKV sh) es)
  where
    sh i = if i >= 3 then i + base else i
    shT t = case t of
      V i -> V (sh i)
      P a b -> P (shT a) (shT b)
      D -> D
    shKV f (k, v) = (sh k, f v)

rounds :: Int -> [Int] -> Map.Map Int T -> Int
rounds _ [] m = Map.size m
rounds n (y : ys) m = case inst y m [(n, y)] of
  (m', es) -> sum (map snd es) + rounds (n + 1) ys m'

exRounds :: Int -> [Int] -> Int
exRounds n ys = rounds n ys (Map.fromList [(3, P (V 3) (V 1)), (n, D)])

exInst :: Int -> Int -> ([(Int, T)], [(Int, Int)])
exInst b n = case inst b (Map.fromList [(3, P (V 3) (V n)), (n, V n)]) [(n, 4), (5, n)] of (m, es) -> (Map.toList m, es)

-- the function it is given a partial application at a Map (shKV (fmap
-- shInfo)), local functions four deep (shEq, shB, sh, shift)
data B = B Int
  deriving (Eq, Show)

data Eqn = Eqn [B] B
  deriving (Eq, Show)

splice :: Int -> [(Int, Map.Map Int T)] -> [Eqn] -> [(Int, Int)] -> (Map.Map Int (Map.Map Int T), [Eqn], Int)
splice base ts es ks =
  let shift = base - 2
      sh i = if i >= 2 then i + shift else i
      shB (B i) = B (sh i)
      shT t = case t of
        V i -> V (sh i)
        P a b -> P (shT a) (shT b)
        D -> D
      shEq (Eqn l r) = Eqn (fmap shB l) (shB r)
      shKV f (k, v) = (sh k, f v)
  in ( Map.fromList (fmap (shKV (fmap shT)) ts)
     , fmap shEq es <> es
     , sum (map fst (fmap (shKV id) ks)) + length (zip [base ..] (fmap shEq es)) )

exSplice :: Int -> Int -> ([(Int, [(Int, T)])], [Eqn], Int)
exSplice b n = go 2 b where
  go :: Int -> Int -> ([(Int, [(Int, T)])], [Eqn], Int)
  go k c = case splice c [(1, Map.fromList [(n, V n)]), (3, Map.fromList [(1, P (V 2) D)])] [Eqn [B n, B 3] (B c)] [(n, 1), (4, n)] of
    (m, es, t) -> if k > 0 && t > 3 then go (k - 1) (c + n) else (map (\(a, x) -> (a, Map.toList x)) (Map.toList m), es, t)

-- a polymorphic local function with a class (Eval.Meter's unhandled)
check :: Int -> T -> Either String Int
check n t = case t of
  V i -> if i > n then bad "variable" i else Right (i + n)
  P a _ -> bad "pair" a
  D -> if n == 2 then bad "both" (n, t) else Right 0
  where
    bad why what = Left (why <> ": " <> show what <> " at " <> show n)

exCheck :: Int -> Int -> [Either String Int]
exCheck n i = [check n (V i), check i (P (V n) D), check n D]
