-- data types a later module of the package takes and answers (telomare's
-- LocTag, StuckF: a type of IR.Loc, IR.Base used in EAL)
module PkTyA where

data Span = Span Int Int
  deriving (Eq, Show)

data Tag = NoTag | At Span | Made String (Maybe Tag)
  deriving (Eq, Show)

data Shape a = Leaf a | Two (Shape a) (Shape a)
  deriving (Eq, Show)

data Cell = Cell { cellTag :: Tag, cellVal :: Int }
  deriving (Eq, Show)

-- a functor for Fix and Cofree (telomare's BasicExprF)
data ExprF r = Lit Int | Add r r | Neg r
  deriving (Eq, Show)
