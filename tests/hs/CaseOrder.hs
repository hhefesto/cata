module CaseOrder where

-- Cases in an order Bend's match does not take: Bend matches a binder
-- after none of the ones behind it, so a case on an earlier parameter
-- inside one on a later, on a local from around a lifted case, or after a
-- later column split, is a def of its own (Fold's fd.env.al).

back :: Maybe Int -> [Int] -> Int
back m xs = case xs of
  [] -> case m of
    Just n -> n
    Nothing -> 0
  (x : _) -> case m of
    Just n -> n + x
    Nothing -> x

inner :: Either Int Bool -> Maybe Int -> Int
inner e m = case fmap (+ 1) m of
  Just k -> case e of
    Left n -> n + k
    Right b -> if b then k else 0
  Nothing -> case e of
    Left n -> n
    Right _ -> 9

third :: Maybe Int -> [Int] -> Maybe Bool -> Int
third a xs (Just b) = case a of
  Just n -> if b then n else 0
  Nothing -> length xs
third a xs Nothing = case xs of
  [] -> 1
  (x : t) -> case a of
    Just n -> x + n
    Nothing -> length t

inIf :: Bool -> Maybe Int -> Int
inIf b m = if b then case m of { Just n -> n; Nothing -> 1 } else 2

step :: [Int] -> Maybe Int -> Int
step xs m = go xs 0
  where
    go [] acc = case m of
      Just n -> n + acc
      Nothing -> acc
    go (y : ys) acc = case m of
      Just n -> go ys (acc + n + y)
      Nothing -> go ys (acc + y)
