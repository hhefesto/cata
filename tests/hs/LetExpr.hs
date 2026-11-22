module LetExpr where

-- A let where only an expression may stand (fold:let-in-expression until
-- 11-22): an if's branch, a guard's body, a let's value, a lambda's body,
-- and a record update under a guard, as xmonad's StackSet.view writes it
-- (its guards' bodies are record updates, which GHC expands with a let).

-- a let in an if's branch
stepUp :: Int -> Int
stepUp x = if x > 0 then let y = x + 1 in y * y else 0

-- a let as a let's value
twice :: Int -> Int
twice x = let z = (let y = x + 1 in y + y) in z * 2

-- a let in a guard's body
clampSq :: Int -> Int
clampSq x
  | x < 0 = 0
  | x > 10 = let c = 10 in c * c
  | otherwise = let s = x * x in s + 1

-- a let in a lambda's body
addEach :: Int -> [Int] -> [Int]
addEach k = map (\x -> let y = x + k in y * 2)

-- a record update under a guard
data P = P { px :: Int, py :: Int } deriving (Show, Eq)

bump :: Int -> P -> P
bump k p
  | k > 0 = p { px = px p + k }
  | k < 0 = p { py = py p + k }
  | otherwise = p
