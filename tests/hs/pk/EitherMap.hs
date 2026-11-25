{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module EitherMap where

-- mapM in Either at a partial function, and through a function that is given
-- one (telomare's traverseUPTPatterns expandPattern)
data T p f = Case f [(p, f)] | Leaf Int | Many [f]
  deriving (Show, Eq)

pats :: Applicative m => (p -> m q) -> T p f -> m (T q f)
pats f = \case
  Case s as -> Case s <$> traverse (\(p, b) -> (, b) <$> f p) as
  Leaf n    -> pure (Leaf n)
  Many xs   -> pure (Many xs)

half :: Int -> Either String Int
half n
  | n < 0 = Left ("negative " ++ show n)
  | otherwise = Right (100 `div` n)

halves :: T Int Bool -> Either String (T Int Bool)
halves = pats half

third :: Int -> Either String Int
third n = if n > 3 then Left "big" else Right (head (replicate n 3))

thirds :: [Int] -> Either String [Int]
thirds = traverse third

strictly :: Int -> Either String ()
strictly n = if n == 0 then error "zero" else if n > 3 then Left "big" else Right ()

check :: [Int] -> Either String ()
check = mapM_ strictly
