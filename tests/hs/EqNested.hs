module EqNested where

-- == and compare at types that hold a list, a Maybe, an Either or a pair of
-- themselves (Fold's fd.nst), and at types that hold those

data Loc = At Int | From String (Maybe Loc) | Nowhere
  deriving (Eq, Ord, Show)

data Rose = Rose Int [Rose]
  deriving (Eq, Ord, Show)

data Js = Nul | Num Int | Arr [Js] | Obj [(String, Js)] | Alt (Either Js Int)
  deriving (Eq, Ord, Show)

data Tree a = Leaf a | Fork [Tree a]
  deriving (Eq, Ord, Show)

data Blame = Blame Loc String
  deriving (Eq, Ord, Show)

locs :: Int -> [Loc]
locs n = [At n, From "a" Nothing, From "a" (Just (At n)), From "b" (Just (From "c" Nothing)), Nowhere]

sameLoc :: Int -> Int -> Bool
sameLoc a b = From "x" (Just (At a)) == From "x" (Just (At b))

orders :: Int -> [Ordering]
orders n = [compare p q | p <- locs n, q <- locs 1]

eqs :: Int -> [Bool]
eqs n = [p == q | p <- locs n, q <- locs 1]

rose :: Int -> Rose
rose n = Rose n [Rose 1 [], Rose n [Rose 2 []]]

roses :: Int -> Int -> (Bool, Ordering)
roses a b = (rose a == rose b, compare (rose a) (rose b))

js :: Int -> [Js]
js n = [Nul, Num n, Arr [Num 1, Nul], Arr [], Obj [("a", Num n)], Obj [("a", Arr [])], Alt (Left Nul), Alt (Right n)]

jsEq :: Int -> [Bool]
jsEq n = [p == q | p <- js n, q <- js 1]

jsOrd :: Int -> [Ordering]
jsOrd n = [compare p q | p <- js n, q <- js 1]

trees :: Int -> Bool
trees n = Fork [Leaf n, Fork [Leaf 1]] == Fork [Leaf 2, Fork [Leaf 1]]

blames :: Int -> [Ordering]
blames n = [compare (Blame l "s") (Blame m "s") | l <- locs n, m <- locs 2]
