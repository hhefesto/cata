{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Newtypes where

import qualified Data.Sequence as Seq
import Data.Sequence (Seq)

newtype Ix = Ix { unIx :: Int } deriving (Eq, Ord, Enum, Show)

newtype Tok = Tok Int deriving (Eq, Ord, Enum)

next :: Ix -> Ix
next = succ

ixOf :: Int -> Ix
ixOf = toEnum

back :: Ix -> Int
back = fromEnum

firstTok :: Tok
firstTok = toEnum 0

bump :: Tok -> Tok
bump = succ

queue :: [Int] -> [Int]
queue xs = drain (foldl (Seq.|>) Seq.empty xs)

drain :: Seq Int -> [Int]
drain s = case Seq.viewl s of
  Seq.EmptyL -> []
  x Seq.:< _ -> [x]
