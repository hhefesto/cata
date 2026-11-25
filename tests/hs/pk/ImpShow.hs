module ImpShow where

data Loc = Loc Int | Gen String (Maybe Loc)
  deriving (Eq, Show)

newtype Name = Name (Loc, String)
  deriving (Eq, Show)
