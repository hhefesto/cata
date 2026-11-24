module NonExh where

-- clauses that leave values out: partial, as GHC's PatternMatchFail is
-- (Fold's fd.exh; the message without its place)

first :: [Int] -> Int
first (x : _) = x

third :: [Int] -> Int
third [_, _, x] = x

big :: Int -> Int
big n | n > 2 = n * 10

fromRight' :: Either String Int -> Int
fromRight' e = case e of
  Right k -> k

both :: Maybe Int -> Maybe Int -> Int
both (Just a) (Just b) = a + b
both Nothing (Just b) = b

data Color = Red | Green | Blue
  deriving (Eq, Show)

name :: Color -> String
name Red = "red"
name Blue = "blue"

digit :: Int -> String
digit 0 = "zero"
digit 1 = "one"

vowel :: Char -> Int
vowel 'a' = 0
vowel 'e' = 1

viaLocal :: [Int] -> Int
viaLocal xs = go xs
  where
    go [y] = y
    go (y : z : zs) = go (y + z : zs)

caller :: [Int] -> Int
caller xs = first xs + 1

covers :: [Bool] -> Int
covers [] = 0
covers (True : _) = 1
covers (False : True : _) = 2
covers (False : False : r) = 3 + length r
covers [False] = 4
