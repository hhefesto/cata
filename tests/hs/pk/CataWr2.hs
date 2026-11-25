{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module CataWr2 where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Control.Monad.Trans (lift)
import qualified Control.Monad.State as State
import Control.Monad.State (evalStateT)
import Data.Functor.Foldable (cata, embed)
import qualified Data.Set as Set
import Data.Void (Void)

data G r = A r r | L String r | V String
  deriving (Show, Eq, Functor, Foldable, Traversable)

data H r = R r r r | Q r | K Int
  deriving (Show, Eq, Functor, Foldable, Traversable)

data F c p r = FG (G r) | FH (H r) | Let [(String, r)] r | Many [r] | Case c r [(p, r)] | I Int
  deriving (Show, Eq, Functor, Foldable, Traversable)

type D = F Void Void

number :: Cofree D Int -> Cofree D (Int, Int)
number = capTop . flip evalStateT (0 :: Integer) . cata f where
  f = \case
    anno C.:< x -> case x of
      ur@(FH (R _ _ _)) -> sequence ur >>= \nur -> do
        n <- State.get
        State.put (n + 1)
        lift (Set.singleton n, embed $ (anno, 0) C.:< FG (A ((anno, 0) :< nur) (embed $ (anno, 0) C.:< FG (V (':' : show n)))))
      Let bindings inner -> (\b i -> (anno, 0) :< Let b i) <$> traverse rebind bindings <*> inner
      other -> ((anno, 0) :<) <$> sequence other
  rebind (n, x) = (\(_n', x') -> (n, x')) <$> cap n (evalStateT x 0)
  cap n (vs, x@((anno, _) :< _)) = lift (Set.empty, (n, foldr (\v b -> embed $ (anno, length vs) C.:< FG (L (':' : show v) b)) x vs))
  capTop (vs, x@((anno, _) :< _)) =
    foldr (\v b -> embed $ (anno, length vs) C.:< FG (A (embed $ (anno, 0) C.:< FG (L (':' : show v) b)) (embed $ (anno, 0) C.:< FG (V (':' : show v))))) x vs
