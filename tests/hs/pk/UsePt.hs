-- an earlier module's point-free partial def, and a partial def that answers
-- a function; () as a monoid
module UsePt where

import ImpPt

heavy :: [P] -> Int
heavy ps = sum (map weight ps)

one :: Int -> Int
one n = weight (B (A n) (if n > 3 then C else A 1)) + 1

shown :: Int -> String
shown n = "<" ++ showP (B (A n) (if n > 2 then C else A 2)) ">" ++ render (A n)

units :: Int -> ((), Int)
units n = (mconcat' [(), ()] <> (if n > 0 then () else mempty), n)
  where mconcat' xs = case xs of
          [] -> mempty
          u : us -> u <> mconcat' us
