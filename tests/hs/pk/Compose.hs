-- functions written as compositions: a recursion through traverse
-- (Resolve's resolveModule and resolveItems)
module Compose where

import Data.Maybe (mapMaybe)

data Item = Bind String Int | Import String
  deriving (Eq, Show)

type Mods = [(String, [Item])]

resolveModule :: Mods -> [String] -> String -> Either String [(String, Int)]
resolveModule ms stack name
  | name `elem` stack = Left (concat (stack <> [name]))
  | otherwise = case lookup name ms of
      Nothing -> Left name
      Just items -> resolveItems ms (stack <> [name]) items

resolveItems :: Mods -> [String] -> [Item] -> Either String [(String, Int)]
resolveItems ms stack = fmap concat . traverse resolveItem
  where
    resolveItem it = case it of
      Bind n v -> Right [(n, v)]
      Import n -> do
        bs <- resolveModule ms stack n
        pure (map (qualify n) bs)

qualify :: String -> (String, Int) -> (String, Int)
qualify q (n, v) = (q ++ n, v)

exResolve :: String -> Int -> Either String [(String, Int)]
exResolve n v = resolveModule [("a", [Bind "x" v, Import "b"]), ("b", [Bind "y" 2, Import n])] [] "a"

evens :: Int -> [Int] -> [Int]
evens k = map (+ k) . filter keep
  where keep x = x > k

total :: Int -> [Int] -> Int
total k
  | k > 5 = sum . evens k
  | otherwise = length . mapMaybe (\x -> if x > k then Just x else Nothing)
