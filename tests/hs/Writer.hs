{-# LANGUAGE DeriveTraversable #-}
module Writer where

-- cata's WriterT rule: WriterT w (Either e) a as Either E (A & W), its
-- newtype's m (a, w); >>= joins the two logs with w's <>, pure logs w's
-- mempty (telomare's letsToApps: WriterT (Set String) (Either ResolverError))

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.Strict (WriterT (..), writer)
import Data.Bifunctor (first)
import Data.Functor.Foldable (cata, embed)
import Data.Set (Set)
import qualified Data.Set as Set

type W = WriterT (Set String) (Either String)

ref :: String -> W Int
ref n = writer (length n, Set.singleton n)

failW :: String -> W a
failW e = lift (Left e)

both :: W Int
both = do
  a <- ref "x"
  b <- ref "yy"
  return (a + b)

logs :: W a -> Either String (a, [String])
logs m = fmap (\(a, w) -> (a, Set.toList w)) (runWriterT m)

ex1 :: Int -> Either String (Int, [String])
ex1 k = logs (fmap (+ k) both)

ex2 :: Bool -> Either String (Int, [String])
ex2 bad = logs (ref "a" >>= \a -> if bad then failW "bad" else (+ a) <$> ref "bcd")

ex3 :: String -> Either String ((Int, Int), [String])
ex3 v = logs ((,) <$> ref v <*> ref "q")

-- a WriterT built from its newtype's constructor, and an Either matched
-- on its run (letsToApps' LetUPF)
drop1 :: String -> W a -> W a
drop1 n m = case runWriterT m of
  Left e -> lift (Left e)
  Right (a, w) -> WriterT (Right (a, Set.delete n w))

ex4 :: String -> Either String (Int, [String])
ex4 n = logs (drop1 n both)

-- a cata whose algebra is a WriterT, the layer's children sequenced
data G x = GVar String | GLam String x | GApp x x
  deriving (Functor, Foldable, Traversable)

type U = Cofree G Int

free :: U -> Either String (U, Set String)
free = runWriterT . cata alg
  where
    alg :: C.CofreeF G Int (W U) -> W U
    alg (a C.:< GVar v) = writer (a :< GVar v, Set.singleton v)
    alg (a C.:< GLam v x) = case runWriterT x of
      Left e -> lift (Left e)
      Right (x', refs) -> if null refs && v == "" then failW "empty"
        else writer (a :< GLam v x', Set.delete v refs)
    alg (a C.:< y) = WriterT . fmap (first (embed . (a C.:<))) . runWriterT $ sequence y

size :: U -> Int
size (_ :< GVar _) = 1
size (_ :< GLam _ x) = 1 + size x
size (_ :< GApp f x) = size f + size x

ex5 :: String -> Either String (Int, [String])
ex5 v = fmap (\(t, w) -> (size t, Set.toList w)) (free (0 :< GApp (0 :< GLam "x" (0 :< GApp (0 :< GVar "x") (0 :< GVar v))) (0 :< GVar "z")))

ex6 :: String -> Either String (Int, [String])
ex6 v = fmap (\(t, w) -> (size t, Set.toList w)) (free (0 :< GLam v (0 :< GLam "y" (0 :< GVar "y"))))
