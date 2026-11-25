module PkOrd where

-- parameters Fold reorders (templates first), in h's order in G; a functor
-- whose field has another of the module's, under a Fix
import Data.Fix (Fix (..))
import qualified Data.Set as S

-- a set that is a template: it is compared with at each step
within :: Int -> S.Set Int -> Int -> [Int] -> [Int]
within lo s d xs = case xs of
  [] -> []
  y : ys -> if S.member (y + lo) s then (y * d) : within lo s d ys else within lo s d ys

applyTo :: Int -> (Int -> Int) -> [Int] -> [Int]
applyTo n f xs = case xs of
  [] -> [n]
  y : ys -> f y : applyTo n f ys

data G r = Leaf Int | Two r r
  deriving (Eq, Show)

instance Functor G where
  fmap f g = case g of
    Leaf n -> Leaf n
    Two a b -> Two (f a) (f b)

data H l r = Name l | In (G r) | Pair l [G r]
  deriving (Eq, Show)

type E = Fix (H Int)

leaf :: Int -> E
leaf n = Fix (Pair n [Leaf n])

wrap :: E -> E
wrap e = Fix (In (Two e e))

names :: E -> [Int]
names (Fix h) = case h of
  Name n -> [n]
  In _ -> []
  Pair n _ -> [n]
