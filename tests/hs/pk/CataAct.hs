{-# LANGUAGE LambdaCase #-}
module CataAct where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Control.Monad.Reader (ReaderT, ask, lift, local, runReaderT)
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import Data.Functor.Foldable (cata, embed)

-- Catas whose answer is an action: a Reader's over Either with an algebra that
-- may err (telomare's Resolve.debruijinize), a State's with a list of children
-- (annotateUnsizedCount)
data TmF v r = Lam v r | App r r | Var v | Many [(v, r)] | Nil
  deriving (Show, Eq)

instance Functor (TmF v) where
  fmap f (Lam v x)  = Lam v (f x)
  fmap f (App a b)  = App (f a) (f b)
  fmap _ (Var v)    = Var v
  fmap f (Many xs)  = Many (fmap (fmap f) xs)
  fmap _ Nil        = Nil

instance Foldable (TmF v) where
  foldr f z (Lam _ x) = f x z
  foldr f z (App a b) = f a (f b z)
  foldr _ z (Var _)   = z
  foldr f z (Many xs) = foldr (\(_, x) acc -> f x acc) z xs
  foldr _ z Nil       = z

instance Traversable (TmF v) where
  traverse f (Lam v x) = Lam v <$> f x
  traverse f (App a b) = App <$> f a <*> f b
  traverse _ (Var v)   = pure (Var v)
  traverse f (Many xs) = Many <$> traverse (traverse f) xs
  traverse _ Nil       = pure Nil

type Named = Cofree (TmF String) Int
type Idx = Cofree (TmF Int) Int

index :: Named -> Either String Idx
index = flip (runReaderT . cata f) [] where
  f :: C.CofreeF (TmF String) Int (ReaderT [String] (Either String) Idx) -> ReaderT [String] (Either String) Idx
  f = \case
    a C.:< Lam v x -> (\y -> a :< Lam 0 y) <$> local (v :) x
    a C.:< Var v   -> ask >>= \vs -> lift (look a v vs)
    a C.:< App g x -> fmap embed . sequence $ a C.:< App g x
    a C.:< other   -> fmap (a :<) . sequence $ conv other
  look a v vs = case lookup v (zip vs [0 ..]) of
    Just i | i < length vs -> pure (iterate (\t -> a :< App t (a :< Nil)) (a :< Var i) !! (2 - a))
    _ -> Left ("free " ++ v)
  conv = \case
    Many xs -> Many (fmap (\(v, x) -> (length v, x)) xs)
    Nil     -> Nil
    _       -> error "conv: no other"

number :: Named -> Cofree (TmF String) (Int, Int)
number t = fst (State.runState (cata f t) 0) where
  f :: C.CofreeF (TmF String) Int (State Int (Cofree (TmF String) (Int, Int))) -> State Int (Cofree (TmF String) (Int, Int))
  f (a C.:< x) = case x of
    Many xs -> (\ys -> (a, length ys) :< Many ys) <$> traverse tag xs
    other   -> do
      n <- State.get
      State.put (n + 1)
      ((a, n) :<) <$> sequence other
  tag (v, x) = (\y -> (v, y)) <$> x
