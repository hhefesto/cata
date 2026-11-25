module PkTyF where

-- IntMap and IntSet, which Spec reads as Map Int and Set Int; types that
-- name each other (the laws' instances)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M

data T = T { tI :: IM.IntMap [Int], tS :: IS.IntSet }

data A = A1 Int | A2 B
  deriving (Eq, Show)

data B = B1 A A | B2
  deriving (Eq, Show)

ks :: IM.IntMap [Int] -> [Int]
ks = IM.keys

both :: IM.IntMap Int -> M.Map Int Int -> Int
both a b = IM.size a + M.size b

elt :: Int -> IS.IntSet -> Bool
elt = IS.member

put :: Int -> IM.IntMap Int -> IM.IntMap Int
put k = IM.insert k 7

flipB :: B -> B
flipB (B1 a b) = B1 b a
flipB B2 = B2

grow :: A -> A
grow a = A2 (B1 a a)
