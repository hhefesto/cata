-- | Control.Monad's <=< and >=>, as telomare writes them (Fast's v2s,
-- Resolve's debruijinize <=< (fmap tf . validateVariables), Expand's
-- traverse expandTerm >=> expandDef, Driver's expandDefs >=> wrapMain):
-- the specialiser writes each as Base's model's kleisliR or kleisliL.
module Kleisli where

import Control.Monad ((<=<), (>=>))

half :: Int -> Maybe Int
half n = if n > 0 && n `mod` 2 == 0 then Just (n `div` 2) else Nothing

pos :: Int -> Either String Int
pos n = if n > 0 then Right n else Left "not positive"

quarter :: Int -> Maybe Int
quarter = half <=< half

checkTwice :: Int -> Either String Int
checkTwice = pos >=> (pos . subtract 1)

-- | a composition on the right, as Resolve's
pipeline :: Int -> Maybe Int
pipeline = half <=< (fmap (+ 2) . half)

ex1 :: Maybe Int
ex1 = quarter 12

ex2 :: Either String Int
ex2 = checkTwice 1
