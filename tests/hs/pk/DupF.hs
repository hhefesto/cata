module DupF where

-- two local functions of one name (telomare's letsToApps)
both :: Int -> [Int] -> Either String [Int]
both k xs = case xs of
  y : ys -> f (rest ys) where
    f (Right zs) = if null zs then Right [k] else Right (y : zs)
    f (Left s)   = Left s
  [] -> Right (end 3)
  where
    rest ys = if length ys > k then Left "long" else Right ys
    end = g where
      g = f . (+ k)
      f n = replicate n k
