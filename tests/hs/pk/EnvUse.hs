-- a derived Foldable's default under a local recursion (IC's envUsage)
{-# LANGUAGE DeriveTraversable #-}
module EnvUse where

import Data.Fix (Fix (..))
import Data.Map (Map)
import qualified Data.Map as Map

data A r = AbortA | DoneA Int
  deriving (Functor, Foldable)

data B r = Env | L r | Pr r r | D Int r
  deriving (Functor, Foldable)

data C r = CB (B r) | CA (A r)
  deriving (Functor, Foldable)

usage :: Fix C -> Map [Int] Int
usage = go [] where
  go proj (Fix t) = case t of
    CB Env -> Map.singleton proj 1
    CB (L x) -> go (1 : proj) x
    CB (D _ _) -> Map.empty
    x -> foldr (Map.unionWith (+) . go []) Map.empty x

exUsage :: Int -> [([Int], Int)]
exUsage n = Map.toList (usage (Fix (CB (Pr (Fix (CB (L (Fix (CB Env))))) (if n > 2 then Fix (CA (DoneA n)) else Fix (CB (Pr (Fix (CB Env)) (Fix (CB (L (Fix (CB Env))))))))))))
