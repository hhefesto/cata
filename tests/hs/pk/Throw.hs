-- throw of the package's own exception (Size's sizeTermM), Foldable's
-- foldMap and for_ at Maybe (Certificate's renderStaticReport)
module Throw where

import Control.Exception (Exception, throw)
import Control.Monad.State (State, execState, modify)
import Data.Foldable (for_, traverse_)

newtype UG = UG String
  deriving Show

instance Exception UG

size :: Int -> Int
size n = if n > 2 then throw (UG ("big " ++ show n)) else n * 2

exSize :: Int -> Int -> Int
exSize a b = size a + size b

header :: Maybe String -> [String]
header h = "report" : foldMap (\s -> ["hash: " <> s]) h

note :: Maybe Int -> State [Int] ()
note m = do
  for_ m $ \x -> modify (x :)
  traverse_ (\x -> modify (x + 1 :)) m

exNote :: Maybe Int -> [Int]
exNote m = execState (note m) [0]
