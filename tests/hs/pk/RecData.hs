module RecData where

import Numeric.Natural (Natural)

-- mutually recursive data types, each with its functions

data Rose = Rose Natural Forest deriving (Eq, Show)

data Forest = None | More Rose Forest deriving (Eq, Show)

roseSum, roseDepth :: Rose -> Natural
roseSum (Rose n f) = n + forestSum f
roseDepth (Rose _ f) = 1 + forestDepth f

forestSum, forestDepth :: Forest -> Natural
forestSum None = 0
forestSum (More r f) = roseSum r + forestSum f
forestDepth None = 0
forestDepth (More r f) = max (roseDepth r) (forestDepth f)

roseMap :: (Natural -> Natural) -> Rose -> Rose
roseMap g (Rose n f) = Rose (g n) (forestMap g f)

forestMap :: (Natural -> Natural) -> Forest -> Forest
forestMap _ None = None
forestMap g (More r f) = More (roseMap g r) (forestMap g f)

roseDouble :: Rose -> Rose
roseDouble = roseMap (\x -> x + x)

data Ex = Num Natural | Minus Ex Ex | Over Ex Ex | Do Block deriving (Eq, Show)

data Block = Return Ex | Seq Ex Block deriving (Eq, Show)

-- partial: (-) below 0, div by 0
evalEx :: Ex -> Natural
evalEx (Num n) = n
evalEx (Minus a b) = evalEx a - evalEx b
evalEx (Over a b) = evalEx a `div` evalEx b
evalEx (Do b) = evalBlock b

evalBlock :: Block -> Natural
evalBlock (Return e) = evalEx e
evalBlock (Seq e b) = evalEx e + evalBlock b

-- and total, an error a value
safeEx :: Ex -> Maybe Natural
safeEx (Num n) = Just n
safeEx (Minus a b) = do
  x <- safeEx a
  y <- safeEx b
  if x < y then Nothing else Just (x - y)
safeEx (Over a b) = do
  x <- safeEx a
  y <- safeEx b
  if y < 1 then Nothing else Just (x `div` y)
safeEx (Do b) = safeBlock b

safeBlock :: Block -> Maybe Natural
safeBlock (Return e) = safeEx e
safeBlock (Seq e b) = (+) <$> safeEx e <*> safeBlock b
