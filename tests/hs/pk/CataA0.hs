module CataA0 where

data O = OVar Int | OApp O O | OClo Int O | OPair O O | ONil | OIte O O O | OL O
  deriving (Show, Eq)

mkPair :: O -> O -> O
mkPair a b = OPair a b
