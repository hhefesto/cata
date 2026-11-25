{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module CataWr where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Control.Monad.Trans (lift)
import qualified Control.Monad.State as State
import Control.Monad.State (evalStateT)
import Data.Functor.Foldable (cata, embed)
import qualified Data.Set as Set

-- A cata whose answer is a State's over a pair's action, run again inside its
-- algebra (telomare's Resolve.annotateUnsizedCount)
data F r = V String | A r r | L String r | R r r r | Let [(String, r)] r | Many [r]
  deriving (Show, Eq, Functor, Foldable, Traversable)

number :: Cofree F Int -> Cofree F (Int, Int)
number = capTop . flip evalStateT (0 :: Integer) . cata f where
  f = \case
    anno C.:< x -> case x of
      ur@(R _ _ _) -> sequence ur >>= \nur -> do
        n <- State.get
        State.put (n + 1)
        lift (Set.singleton n, embed $ (anno, 0) C.:< A ((anno, 0) :< nur) (embed $ (anno, 0) C.:< V (':' : show n)))
      Let bindings inner -> (\b i -> (anno, 0) :< Let b i) <$> traverse rebind bindings <*> inner
      other -> ((anno, 0) :<) <$> sequence other
  rebind (n, x) = (\(_n', x') -> (n, x')) <$> cap n (evalStateT x 0)
  cap n (vs, x@((anno, _) :< _)) = lift (Set.empty, (n, foldr (\v b -> embed $ (anno, length vs) C.:< L (':' : show v) b) x vs))
  capTop (vs, x@((anno, _) :< _)) =
    foldr (\v b -> embed $ (anno, length vs) C.:< A (embed $ (anno, 0) C.:< L (':' : show v) b) (embed $ (anno, 0) C.:< V (':' : show v))) x vs
