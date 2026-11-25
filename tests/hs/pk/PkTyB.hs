-- functions at the types of the module PkTyA
module PkTyB where

import PkTyA

spanLen :: Span -> Int
spanLen (Span a b) = b - a

tagDepth :: Tag -> Int
tagDepth t = case t of
  NoTag -> 0
  At _ -> 1
  Made _ m -> case m of
    Nothing -> 1
    Just u -> 1 + tagDepth u

retag :: Tag -> Tag
retag t = case t of
  NoTag -> Made "retag" Nothing
  At s -> At (Span (spanLen s) 0)
  Made n m -> Made n (fmap retag m)

leaves :: Shape Int -> [Int]
leaves s = case s of
  Leaf a -> [a]
  Two l r -> leaves l ++ leaves r

mirror :: Shape a -> Shape a
mirror s = case s of
  Leaf a -> Leaf a
  Two l r -> Two (mirror r) (mirror l)

bump :: Cell -> Cell
bump c = c { cellVal = cellVal c + 1 }

cellOf :: Tag -> Int -> Cell
cellOf t n = Cell (retag t) (n * 2)

pad :: Int -> ShowS
pad n s = if n > 0 then ' ' : pad (n - 1) s else s

showsTag :: Tag -> ShowS
showsTag t s = case t of
  NoTag -> '_' : s
  At _ -> '@' : s
  Made n _ -> n ++ s

-- function arguments (telomare's cfmap, ctraverse at a constant function)
overShape :: (Int -> Int) -> Shape Int -> Shape Int
overShape f s = case s of
  Leaf a -> Leaf (f a)
  Two l r -> Two (overShape f l) (overShape f r)

foldTags :: (Tag -> Int -> Int) -> Int -> [Tag] -> Int
foldTags f z ts = case ts of
  [] -> z
  t : u -> f t (foldTags f z u)
