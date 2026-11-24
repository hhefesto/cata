{-# LANGUAGE BangPatterns #-}
-- tests/hs/BangPat.hs: local pattern bindings, lazy and strict, in a
-- module alone.  bangPar and bangVar force head xs as GHC does (ok-law);
-- tupLet and bangTup do not force it in GHC (the pair is already a
-- constructor), and Bend matches the pair's parts strictly, so their laws
-- fail at [] and they are out (adj/, section 9: F less defined there).
-- lazySplit and whereGuard use their binding in one branch only: Fold
-- floats it in (fd.pb.at), and both are ok-law.
module BangPat where

tupLet :: [Int] -> Bool -> Int
tupLet xs b = let (h, k) = (head xs, 1 :: Int) in if b then k else h

bangTup :: [Int] -> Bool -> Int
bangTup xs b = let !(h, k) = (head xs, 1 :: Int) in if b then k else h

bangPar :: [Int] -> Bool -> Int
bangPar xs b = let !(h) = head xs in if b then 0 else h

bangVar :: [Int] -> Bool -> Int
bangVar xs b = let !h = head xs in if b then 0 else h

-- a lazy pattern binding the one branch that uses it takes (Fold's
-- fd.pb.at floats it in, as GHC does): GHC answers 0 at ([], True), and so
-- does Bend
lazySplit :: [Int] -> Bool -> Int
lazySplit xs b = let (h, t) = (head xs, tail xs) in if b then 0 else h + length t

-- the same in a where under guards (hs1003's 00533 numDigits' ilog)
whereGuard :: [Int] -> Int
whereGuard xs
  | null xs = 0
  | otherwise = h + length t
  where
    (h, t) = (head xs, tail xs)
