module RecMut where

import Numeric.Natural (Natural)

-- adj section 14's programs (adj/RecGhc.hs) as Haskell: recursion

evenN, oddN :: Natural -> Bool
evenN n = if n < 1 then True else oddN (n - 1)
oddN n = if n < 1 then False else evenN (n - 1)

hofF, hofM :: Natural -> Natural
hofF n = if n < 1 then 1 else n - hofM (hofF (n - 1))
hofM n = if n < 1 then 0 else n - hofF (hofM (n - 1))

ack :: Natural -> Natural -> Natural
ack m n
  | m < 1 = n + 1
  | n < 1 = ack (m - 1) 1
  | otherwise = ack (m - 1) (ack m (n - 1))

collatz :: Natural -> Natural
collatz n
  | n < 2 = 0
  | n `mod` 2 < 1 = 1 + collatz (n `div` 2)
  | otherwise = 1 + collatz (3 * n + 1)
