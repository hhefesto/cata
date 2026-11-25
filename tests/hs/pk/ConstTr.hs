module ConstTr where

import Data.Functor.Const (Const (..))
import Data.Set (Set)
import qualified Data.Set as Set

-- a traversal run at Const (telomare's Surface.foldMapScoped)
data E = V String | L String E | A E E | Ls [E] deriving (Eq, Show)

scoped :: Applicative m => ([String] -> E -> m E) -> E -> m E
scoped f e = case e of
  V v    -> pure (V v)
  L v b  -> L v <$> f [v] b
  A a b  -> A <$> f [] a <*> f [] b
  Ls xs  -> Ls <$> traverse (f []) xs

foldScoped :: Monoid r => ([String] -> E -> r) -> E -> r
foldScoped f = getConst . scoped (\bs -> Const . f bs)

free :: E -> Set String
free (V v) = Set.singleton v
free e     = foldScoped (\bs x -> free x `Set.difference` Set.fromList bs) e

names :: E -> [String]
names (V v) = [v]
names e     = foldScoped (\bs x -> bs ++ names x) e
