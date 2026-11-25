-- PrettyPrint.Indent's helpers: a module's defs that take actions and
-- functions, for another module to give partial ones
module ImpHof where

import Control.Monad.State

indent :: Int -> String -> String
indent i str = replicate i ' ' <> str

withOne :: String -> State Int String -> State Int String
withOne str sx = do
  i <- get
  let sout = str <> " "
  put $ i + length sout
  x <- sx
  pure $ sout <> x

withTwo :: String -> State Int String -> State Int String -> State Int String
withTwo str sl sr = do
  i <- get
  let sout = str <> " "
      newl = i + length sout
  put newl
  l <- sl
  put newl
  r <- sr
  pure $ sout <> l <> "\n" <> indent newl r

apply2 :: (Int -> Int) -> Int -> Int -> Int
apply2 f a b = f a + f b

pick :: (Int -> Maybe Int) -> Int -> Int
pick f n = maybe (apply2 (+ n) n n) (\k -> apply2 (k +) n 1) (f n)
