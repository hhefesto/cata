-- fmap (first (f . g)) with g partial (Resolve's buildRefs)
module PartFirst where

import Control.Monad.Trans.Writer (WriterT (..))
import Data.Bifunctor (first)

brt :: [Int] -> Int
brt xs = case xs of
  x : _ -> x
  _ -> error "brt: unexpected"

f1 :: Either String ([Int], Int) -> Either String (Int, Int)
f1 m = fmap (first ((+ 1) . brt)) m

f2 :: Int -> WriterT [Int] (Either String) [Int] -> WriterT [Int] (Either String) (Int, Int)
f2 k x = WriterT . fmap (first (((,) k) . h)) . runWriterT $ x where
  h ys = case ys of
    [y] -> y + k
    _ -> error "h: unexpected"

exF1 :: Int -> Either String (Int, Int)
exF1 n = f1 (if n > 2 then Left "no" else Right ([n | n > 0], n))

exF2 :: Int -> Either String ((Int, Int), [Int])
exF2 n = runWriterT (f2 n (WriterT (if n > 3 then Left "big" else Right ([n | n > 0], [n]))))
