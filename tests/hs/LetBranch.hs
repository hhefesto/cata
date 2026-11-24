module LetBranch where

-- A let with partial calls in an if's branch (Fold's fd.pt.elet): its
-- value's calls bound before it, its body an answer; a let and an if in two
-- arguments of one call.

import Numeric.Natural (Natural)

inThen :: Natural -> Natural -> Natural
inThen v1 v2 = if 3 < v1 then (let v3 = v1 + 1 in v3 * (v1 `mod` v2)) else 5

twice :: Natural -> Natural -> Natural
twice v1 v2 = if 3 < v1 then (let v3 = v1 + 1 in v3 * (v1 `mod` v2) + v3) else 5

value :: Natural -> Natural -> Natural
value v1 v2 = if 1 < v1 then (let v3 = v1 `mod` v2 in v3 + v3) else 5

inElse :: Natural -> Natural -> Natural
inElse v1 v2 = if 3 < v1 then (let v3 = v1 * v1 in v3 + v3) else 5 + (v1 `mod` v2)

argLet :: Natural -> Natural -> Natural
argLet v1 v2 = (let v3 = v1 + 1 in v3 * (v1 `mod` v2)) + (if 3 < v1 then 4 else 5)

argIf :: Natural -> Natural -> Natural
argIf v1 v2 = (if 3 < v1 then 4 else 5) + (let v3 = v1 + 1 in v3 * (v1 `mod` v2))

nested :: Natural -> Natural -> Natural
nested v1 v2 =
  if 1 < v1
    then (let v3 = v1 `div` v2 in if v3 > 1 then v3 else (let v4 = v3 + 1 in v4 `mod` v2))
    else 7
