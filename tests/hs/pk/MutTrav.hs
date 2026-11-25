{-# LANGUAGE DeriveTraversable #-}
module MutTrav where

import Control.Comonad.Cofree (Cofree (..))
import Data.Fix (Fix (..))

-- two mutually recursive functions, one through a traverse of a traverse
-- (telomare's expandTerm and expandPattern)
data TF p r = Lam [(Int, p)] r | App r r | Case r [(p, r)] | Var String
  deriving (Show, Eq, Functor, Foldable, Traversable)

data PF t r = PV String | PP r r | PA r t
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype A = A (Cofree (TF (Fix (PF A))) Int)
newtype B = B (Cofree (TF (Fix (PF B))) Int)

type TA = Cofree (TF (Fix (PF A))) Int
type TB = Cofree (TF (Fix (PF B))) Int

term :: TA -> Either String TB
term (k :< t) = case t of
  Lam ps b -> do
    ps' <- traverse (traverse pat) ps
    mapM_ (uncurry check) ps'
    b' <- term b
    pure (k :< Lam ps' b')
  Case s as -> do
    s' <- term s
    as' <- traverse alt as
    pure (k :< Case s' as')
  App f x -> do
    f' <- term f
    x' <- term x
    pure (k :< App f' x')
  Var n -> if n == "" then Left ("empty " ++ show k) else pure (k :< Var n)
  where
    alt (p, b) = do
      p' <- pat p
      check k p'
      (,) p' <$> term b

pat :: Fix (PF A) -> Either String (Fix (PF B))
pat (Fix p) = case p of
  PV n       -> pure (Fix (PV n))
  PP a b     -> (\x y -> Fix (PP x y)) <$> pat a <*> pat b
  PA a (A t) -> (\x y -> Fix (PA x (B y))) <$> pat a <*> term t

check :: Int -> Fix (PF B) -> Either String ()
check k (Fix p) = case p of
  PV "bad" -> Left ("bad " ++ show k)
  PP a b   -> check k a >> check k b
  _        -> Right ()

size :: TB -> Int
size (_ :< t) = case t of
  Lam ps b -> length ps + size b
  App f x -> size f + size x
  Case s as -> size s + sum [ size b | (_, b) <- as ]
  Var n -> length n

run :: [(Int, String)] -> [String] -> Either String Int
run ps ns = size <$> term (foldr (\n b -> 1 :< App (1 :< Var n) b) (0 :< Lam [ (i, Fix (PV n)) | (i, n) <- ps ] (2 :< Var "x")) ns)
