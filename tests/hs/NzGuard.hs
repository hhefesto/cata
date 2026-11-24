module NzGuard where

-- Fold's guard pass (fd.nzg): a division by a variable an enclosing if has
-- told is not 0 is the total one; by another variable, partial.  And a
-- binder that shadows the guarded variable makes it unknown again (these
-- three are out for other reasons today: a match in an expression, a
-- where's local, a partial call under a lambda).

guarded :: Int -> Int -> Int
guarded x y = if x == 0 then 0 else y `div` x

guardedPos :: Int -> Int -> Int
guardedPos x y = if x > 0 then y `mod` x else 7

wrongVar :: Int -> Int -> Int
wrongVar x y = if x == 0 then 0 else x `div` y

shadowCase :: Int -> Maybe Int -> Int
shadowCase x m = if x == 0 then 0 else case m of
  Just x -> 10 `div` x
  Nothing -> 1

shadowLet :: Int -> Int -> Int
shadowLet x y = if x == 0 then 0 else let x = y * 0 in 10 `div` x

shadowWhere :: Int -> Int -> Int
shadowWhere x y = if x /= 0 then go y else 0
  where go x = 10 `div` x
