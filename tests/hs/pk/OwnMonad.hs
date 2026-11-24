-- base's functions that are no methods at a package's own Functor, Monad
-- and Foldable (Size.IR's StrictAccum, EAL's unsizedIn, Expand's
-- checkPlainPattern)
{-# LANGUAGE DeriveTraversable #-}
module OwnMonad where

import Control.Applicative (Applicative (..))
import Control.Monad (liftM2, unless, void, when)

data Acc a x = Acc { getAcc :: !a, getX :: x }
  deriving (Functor)

instance Monoid a => Applicative (Acc a) where
  pure = Acc mempty
  Acc u f <*> Acc v x = Acc (u <> v) (f x)
  liftA2 f (Acc u x) (Acc v y) = Acc (u <> v) (f x y)

instance Monoid a => Monad (Acc a) where
  Acc u x >>= f = case f x of Acc v y -> Acc (u <> v) y

data Tr r = Leaf | One r | Two Int r r
  deriving (Functor, Foldable, Traversable)

tell :: [Int] -> Acc [Int] ()
tell xs = Acc xs ()

visit :: Int -> Acc [Int] Int
visit n = do
  when (n > 2) (tell [n])
  unless (n > 2) (tell [0])
  pure (n + 1)

goTr :: Monoid a => (Int -> Acc a Int) -> Tr Int -> Acc a (Tr Int)
goTr f t = case t of
  Two n a b -> liftM2 (Two n) (f a) (f b)
  One a -> One <$> f a
  Leaf -> pure Leaf

count :: Tr Int -> (Bool, Bool, Bool)
count t = (any (> 3) t, null t, 2 `elem` t)

exTr :: Int -> Int -> ([Int], Bool, Bool, Bool)
exTr a b = case goTr visit (Two 1 a b) of
  Acc xs t -> let (p, q, r) = count t in (xs, p, q, r)

exOne :: Int -> [Int]
exOne a = getAcc (void (goTr visit (One a)) >>= \_ -> visit =<< pure a)

anyOr :: Int -> Bool
anyOr n = or (fmap (> 4) (Two n n 3)) && and (fmap (> n) (One 3))

visitAll :: Tr Int -> Acc [Int] (Tr Int)
visitAll t = do
  _ <- mapM visit t
  () <$ tell [9]
  u <- traverse visit t
  return u

exAll :: Int -> ([Int], Bool)
exAll n = case visitAll (Two 0 n 1) of Acc xs t -> (xs, any (== n) t)
