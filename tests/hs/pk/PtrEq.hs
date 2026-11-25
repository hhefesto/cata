{-# LANGUAGE MagicHash #-}
module PtrEq where

import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)

data Tr = L | N Int Tr Tr deriving (Eq, Show)

same :: Tr -> Tr -> Bool
same a b = isTrue# (reallyUnsafePtrEquality# a b) || case (a, b) of
  (L, L)                 -> True
  (N i l r, N j m s)     -> i == j && same l m && same r s
  _                      -> False

pick :: Tr -> Tr -> Tr
pick a b = if isTrue# (reallyUnsafePtrEquality# a b) then a else case (a, b) of
  (N i l r, N j m s) | i == j -> N i (pick l m) (pick r s)
  _ | same a b -> a
    | otherwise -> N 0 a b
