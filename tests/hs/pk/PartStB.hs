{-# LANGUAGE LambdaCase #-}
-- PartSt's functors, the partial cata into a State in another module, at a
-- Cofree
module PartStB where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Monad.State (State, evalState)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import PartSt (EF (..), TF (..), mkQ)

convB :: (Int -> Int) -> Cofree TF Int -> Fix EF
convB ll = flip evalState 0 . cata (f failConv) where
  failConv = error "convB failed"
  f :: (TF (State Int (Fix EF)) -> State Int (Fix EF)) -> CofreeT.CofreeF TF Int (State Int (Fix EF)) -> State Int (Fix EF)
  f other (_ CofreeT.:< g) = case g of
    U i   -> pure $ iterate (Fix . S) (Fix (Env 7)) !! ll i
    D x   -> x >>= mkQ
    P a b -> (\x y -> Fix (Q x y)) <$> a <*> b
    x     -> other x

exConvB :: Int -> Fix EF
exConvB n = convB (+ n) (0 :< P (1 :< D (2 :< U 2)) (3 :< D (4 :< U (- 1))))
