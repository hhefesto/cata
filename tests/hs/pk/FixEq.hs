-- == at Fix f, f's Eq1 the package's own (IR.Base's AbortableF, StuckF)
module FixEq where

import Data.Fix (Fix (..))
import Data.Functor.Classes (Eq1 (..))

data F r = Zero | Pair r r | Tag Int r
  deriving (Eq, Show)

instance Eq1 F where
  liftEq t a b = case (a, b) of
    (Zero, Zero) -> True
    (Pair x y, Pair u v) -> t x u && t y v
    (Tag n _, Tag m _) | n == m -> True
    _ -> False

type E = Fix F

data A = Abort | Aborted E
  deriving Eq

same :: E -> E -> Bool
same a b = a == b

build :: Int -> Int -> E
build n m = Fix (Pair (Fix (Tag n (Fix Zero))) (Fix (Pair (Fix Zero) (Fix (Tag m (Fix Zero))))))

exSame :: Int -> Int -> (Bool, Bool)
exSame n m = (same (build n m) (build m n), build n 1 /= build n m)

isSame :: A -> A -> Bool
isSame a b = case (a, b) of
  (Abort, Abort) -> True
  (Aborted x, Aborted y) -> x == y
  _ -> False

exIs :: Int -> Int -> Bool
exIs n m = isSame (Aborted (build n 2)) (Aborted (build m 2))
