{-# LANGUAGE BangPatterns #-}
module Bang where

-- A strict let, `let !h = e` (BangPatterns), must be evaluated where it
-- stands, not moved by Fold's float-in (fd.fi) into the branch that uses
-- it: at [] and True GHC errs (the bang forces head []).  GHC keeps it a
-- FunBind with the strictness in its match; hs-export now writes it as
-- the pattern binding it means, (patbind (pbang (pvar h)) ..), which Fold
-- does not take yet (fold:form): out, where before it was a plain let by
-- luck.  seq and $! are not taken (base:GHC.Prim.seq).

bangLet :: [Int] -> Bool -> Int
bangLet xs b = let !h = head xs in if b then 0 else h

bangWhere :: [Int] -> Bool -> Int
bangWhere xs b = if b then 0 else h
  where !h = head xs

seqd :: [Int] -> Bool -> Int
seqd xs b = let h = head xs in h `seq` (if b then 0 else h)

strictApp :: [Int] -> Bool -> Int
strictApp xs b = (\h -> if b then 0 else h) $! head xs
