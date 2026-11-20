{-# LANGUAGE LambdaCase #-}
module Ap where

-- cata's <*> after <$>: telomare's b2s ((:) <$> b2i x <*> f xs at Maybe),
-- chains of three, pure f <*> .., at Maybe and Either

half :: Int -> Maybe Int
half n = if n `mod` 2 == 0 then Just (n `div` 2) else Nothing

halves :: [Int] -> Maybe [Int]
halves = \case
  [] -> Just []
  x : xs -> (:) <$> half x <*> halves xs

triple :: [Int] -> Maybe (Int, Int, Int)
triple xs = case xs of
  a : b : c : _ -> (,,) <$> half a <*> half b <*> half c
  _ -> Nothing

pureAp :: Int -> Int -> Maybe Int
pureAp a b = pure (+) <*> half a <*> half b

check :: Int -> Either String Int
check n = if n >= 0 then Right n else Left ("negative: " ++ show n)

checks :: [Int] -> Either String [Int]
checks = \case
  [] -> Right []
  x : xs -> (:) <$> check x <*> checks xs

sumPair :: Int -> Int -> Either String Int
sumPair a b = (+) <$> check a <*> check b
