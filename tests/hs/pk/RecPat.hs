{-# LANGUAGE LambdaCase #-}
module RecPat where

-- a record pattern with no field as an as-pattern's, and lookup in a list of
-- functions
data Val = Z | P Val Val | Ab String Int deriving (Eq, Show)

left :: Val -> Either String Val
left = \case
  P a _     -> Right a
  Z         -> Right Z
  a@Ab {}   -> Right a

pick :: Val -> Val -> Val
pick x y = case (x, y) of
  (a@Ab {}, _) -> a
  (_, P {})    -> x
  _            -> y

data Fn = One (Int -> Int) | Two (Int -> Int -> Int)

fns :: [(String, Fn)]
fns = [("inc", One (+ 1)), ("add", Two (+)), ("mul", Two (*))]

fnNames :: [String]
fnNames = "id" : (fst <$> fns)

apply :: String -> [Int] -> Maybe Int
apply n xs = case lookup n fns of
  Just (One f) | [x] <- xs    -> Just (f x)
  Just (Two f) | [x, y] <- xs -> Just (f x y)
  _ -> Nothing

tagAll :: Int -> [String] -> [(Int, String)]
tagAll k xs = zipWith tag [0 ..] xs
  where tag i x = (i + k, x)
