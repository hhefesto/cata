{-# LANGUAGE DeriveTraversable #-}
module Reader where

-- cata's ReaderT rule: ReaderT r Identity as R -> A, ReaderT r (Either e)
-- as R -> Either E A; Traversable at CofreeF as Cata.Base's model

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Control.Monad.Reader (Reader, ReaderT, ask, asks, local, runReader, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Functor.Foldable (cata, embed)

type R = Reader Int

depth :: R Int
depth = ask

deeper :: R a -> R a
deeper = local (+ 1)

twice :: R Int
twice = do
  d <- depth
  e <- deeper depth
  return (d + e)

scaled :: Int -> R Int
scaled k = asks (* k)

summed :: R Int
summed = (+) <$> depth <*> scaled 10

ex1 :: Int -> Int
ex1 r = runReader twice r

ex2 :: Int -> Int
ex2 r = runReader (fmap (* 2) summed) r

-- over Either
type E = ReaderT [String] (Either String)

lookupE :: String -> E Int
lookupE n = do
  vs <- ask
  lift (find 0 vs)
  where
    find :: Int -> [String] -> Either String Int
    find _ [] = Left ("unbound " ++ n)
    find i (v : rest) = if v == n then Right i else find (i + 1) rest

under :: String -> E a -> E a
under v = local (v :)

ex3 :: [String] -> Either String Int
ex3 env = runReaderT (under "x" (lookupE "y")) env

ex4 :: [String] -> Either String (Int, Int)
ex4 env = runReaderT ((,) <$> lookupE "a" <*> under "b" (lookupE "b")) env

-- a cata whose algebra is a Reader, the layer's children sequenced
data F x = Leaf Int | Node x x | Bind x

instance Functor F where
  fmap _ (Leaf n) = Leaf n
  fmap f (Node a b) = Node (f a) (f b)
  fmap f (Bind a) = Bind (f a)

instance Foldable F where
  foldr _ z (Leaf _) = z
  foldr f z (Node a b) = f a (f b z)
  foldr f z (Bind a) = f a z

instance Traversable F where
  traverse _ (Leaf n) = pure (Leaf n)
  traverse f (Node a b) = Node <$> f a <*> f b
  traverse f (Bind a) = Bind <$> f a

type T = Cofree F Int

levels :: T -> T
levels t = runReader (cata alg t) 0
  where
    alg (_ C.:< Bind x) = do
      d <- ask
      x' <- local (+ 1) x
      pure (embed (d C.:< Bind x'))
    alg (_ C.:< x) = do
      d <- ask
      fmap embed (sequence (d C.:< x))

sumAnn :: T -> Int
sumAnn (a :< Leaf _) = a
sumAnn (a :< Node l r) = a + sumAnn l + sumAnn r
sumAnn (a :< Bind x) = a + sumAnn x

ex5 :: Int -> Int
ex5 n = sumAnn (levels (0 :< Bind (0 :< Node (0 :< Leaf n) (0 :< Bind (0 :< Leaf 1)))))

-- the same at a derived Traversable, over Either (telomare's debruijinize)
data G x = GLeaf String | GLam String x | GApp x x
  deriving (Functor, Foldable, Traversable)

type U = Cofree G Int

scope :: U -> Either String U
scope t = runReaderT (cata alg t) []
  where
    alg :: C.CofreeF G Int (E U) -> E U
    alg (a C.:< GLam v x) = do
      x' <- local (v :) x
      pure (embed (a C.:< GLam v x'))
    alg (a C.:< GLeaf v) = do
      vs <- ask
      if v `elem` vs then pure (embed (a C.:< GLeaf v)) else lift (Left ("unbound " ++ v))
    alg y = fmap embed (sequence y)

size :: U -> Int
size (_ :< GLeaf _) = 1
size (_ :< GLam _ x) = 1 + size x
size (_ :< GApp f x) = size f + size x

ex6 :: String -> Either String Int
ex6 v = fmap size (scope (0 :< GLam "x" (0 :< GApp (0 :< GLeaf "x") (0 :< GLeaf v))))

-- telomare's closeLams: a Reader Bool, both branches of an if running the
-- same child
closeG :: U -> U
closeG = runIdentity . flip (runReaderT . cata f) True
  where
    f :: C.CofreeF G Int (ReaderT Bool Identity U) -> ReaderT Bool Identity U
    f (a C.:< x) = case x of
      GLam v ix -> ask >>= \naked -> if naked
        then (\b -> embed (a C.:< GLam ('!' : v) b)) <$> local (const False) ix
        else (\b -> embed (a C.:< GLam v b)) <$> local (const False) ix
      x' -> (\y -> embed (a C.:< y)) <$> sequence x'

names :: U -> [String]
names (_ :< GLeaf v) = [v]
names (_ :< GLam v x) = v : names x
names (_ :< GApp f x) = names f ++ names x

ex7 :: String -> [String]
ex7 v = names (closeG (0 :< GApp (0 :< GLam v (0 :< GLam "y" (0 :< GLeaf v))) (0 :< GLam "z" (0 :< GLeaf "z"))))
