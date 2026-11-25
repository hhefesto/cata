-- functions in a list (Desugar's patternNodes)
{-# LANGUAGE DeriveFunctor, LambdaCase #-}
module FnList where

import Data.Bifunctor (first)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

data T = Zero | Var String | L T | R T | Ite T T T | Eq T T
  deriving (Eq, Show)

type Path = T -> T

data Node = PairN | IntN Int | VarN String
  deriving (Eq, Show)

data P r = PP r r | PI Int | PV String | Ign | An r Int
  deriving (Functor)

nodes :: Fix P -> [(Path, Node)]
nodes = cata alg where
  alg = \case
    PP x y -> (id, PairN) : (first (. L) <$> x) <> (first (. R) <$> y)
    PI i -> [(id, IntN i)]
    PV s -> [(id, VarN s)]
    Ign -> []
    An x _ -> x

checks :: T -> [(Path, Node)] -> [T]
checks x = concatMap check where
  check (path, node) = case node of
    PairN -> [Ite (path x) (Var "1") Zero]
    IntN i -> [Eq (path x) (Var (show i))]
    VarN _ -> []

binds :: T -> [(Path, Node)] -> T -> T
binds x ns body = foldr bind body ns where
  bind (path, node) b = case node of
    VarN s -> Ite (Var s) (path x) b
    _ -> b

lower :: T -> Fix P -> T -> T
lower x p body =
  let ns = nodes p
      bound = binds x ns body
  in case checks x ns of
       [] -> bound
       c : cs -> Ite c bound (foldr Eq Zero cs)

pat :: Int -> Fix P
pat n = Fix (PP (Fix (PV "a")) (Fix (An (Fix (PP (Fix (PI n)) (Fix Ign))) 3)))

exLower :: Int -> T
exLower n = lower (Var "s") (if n > 3 then Fix (PV "q") else pat n) (Var "body")
