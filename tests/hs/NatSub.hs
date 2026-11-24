module NatSub where

-- Natural's (-): an error below 0 (ArithException Underflow), so F's is a
-- failure value (prelude/HsPartial.bend's HsNum.sub, "arithmetic
-- underflow"), a partial def, as division by 0 is.

import Numeric.Natural (Natural)

minus :: Natural -> Natural -> Natural
minus a b = a - b

less :: Natural -> Natural
less n = n - 1

gap :: Natural -> Natural -> Natural
gap a b = if a < b then b - a else a - b

countdown :: Natural -> [Natural]
countdown 0 = [0]
countdown n = n : countdown (n - 1)

total :: [Natural] -> Natural
total [] = 10
total (x : xs) = total xs - x

pick :: Maybe Natural -> Natural -> Natural
pick m n = case m of
  Nothing -> n
  Just k -> n - k
