module Dict where

-- == and compare at a type variable: the def takes them (Fold's fd.dc), its
-- callers pass them, a caller at a type Bend's own

member :: Eq a => a -> [a] -> Bool
member _ [] = False
member x (y : ys) = x == y || member x ys

lookupOr :: Eq a => [(a, b)] -> b -> a -> b
lookupOr [] d _ = d
lookupOr ((x, y) : xys) d k = if x == k then y else lookupOr xys d k

without :: Eq a => [a] -> [a] -> [a]
without xs ys = filter (\x -> not (member x ys)) xs

palindrome :: Eq a => [a] -> Bool
palindrome xs = xs == reverse xs

nested :: Eq a => [[a]] -> [a] -> Int
nested xss ys = length (filter (== ys) xss)

insertSorted :: Ord a => a -> [a] -> [a]
insertSorted x [] = [x]
insertSorted x (y : ys)
  | x <= y = x : y : ys
  | otherwise = y : insertSorted x ys

isort :: Ord a => [a] -> [a]
isort = foldr insertSorted []

biggest :: Ord a => a -> [a] -> a
biggest m [] = m
biggest m (y : ys) = biggest (if y > m then y else m) ys

smaller :: Ord a => a -> a -> (a, a)
smaller a b = (min a b, max a b)

order :: (Ord a, Ord b) => (a, b) -> (a, b) -> Ordering
order p q = compare p q

ordered :: Ord a => [a] -> Bool
ordered xs = snd (foldr go (Nothing, True) xs)
  where
    go _ s@(_, False) = s
    go y (Nothing, t) = (Just y, t)
    go y (Just x, _) = (Just y, x >= y)

names :: [String] -> [String]
names = isort

has :: String -> [String] -> Bool
has = member

pairs :: [(Int, Char)] -> Int -> Char
pairs xs k = lookupOr xs '?' k
