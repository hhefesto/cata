-- IR.Surface's traverseScoped and Resolve's qualifyTerm: a local and a copy at it
-- (listTraverse at goPattern) as one rec of several bindings
{-# LANGUAGE DeriveTraversable, LambdaCase, MonoLocalBinds #-}
module RecGrp where

import Data.Fix (Fix (..))
import Data.Functor.Identity (Identity (..))

data PF a r = PAnn r a | PVar Int | PCon Int [r]
  deriving (Eq, Show, Functor, Foldable, Traversable)

data TF p t = Lam Int t | Case t [(p, t)] | Lit Int
  deriving (Eq, Show, Functor, Foldable, Traversable)

newtype Ann = Ann Int deriving (Eq, Show)
type Pat = Fix (PF Ann)
newtype Term = Term (TF Pat Term)

binders :: Pat -> [Int]
binders (Fix p) = case p of
  PAnn q _ -> binders q
  PVar v -> [v]
  PCon _ ps -> concatMap binders ps

traverseScoped :: Applicative m => ([Int] -> Term -> m Term) -> Ann -> TF Pat Term -> m (TF Pat Term)
traverseScoped f ann0 = \case
  Lam v body -> Lam v <$> f [v] body
  Case s alts ->
    let goPattern (Fix p) = Fix <$> case p of
          PAnn inner (Ann a) -> PAnn <$> goPattern inner <*> (Ann <$> fmap (const a) (f [] (Term (Lit a))))
          other -> traverse goPattern other
        goAlternative (p, body) = (,) <$> goPattern p <*> f (binders p) body
    in Case <$> f [] s <*> traverse goAlternative alts
  other -> traverse (f []) other

mapScoped :: ([Int] -> Term -> Term) -> TF Pat Term -> TF Pat Term
mapScoped f = runIdentity . traverseScoped (\bs t -> Identity (f bs t)) (Ann 0)

qualify :: Int -> Term -> Term
qualify k = go [] where
  go bound (Term t) = Term $ case t of
    Lit n | n `notElem` bound -> Lit (n + k)
    other -> mapScoped (\bs -> go (bound <> bs)) other

qualifyLit :: Int -> Int -> Int
qualifyLit k n = case qualify k (Term (Case (Term (Lit n)) [(Fix (PVar n), Term (Lit (n + 1)))])) of
  Term (Case (Term (Lit a)) [(_, Term (Lit b))]) -> a * 1000 + b
  _ -> -1
