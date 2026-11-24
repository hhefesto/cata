-- Show at Cofree, through a type whose annotations hold the term again
-- (IR.Surface's AnnotatedEST: a pattern's annotation is an expanded term)
{-# LANGUAGE DeriveFunctor, LambdaCase #-}
module ShowCof where

import Control.Comonad.Cofree (Cofree (..))
import Data.Fix (Fix (..))
import Data.Functor.Classes (Show1 (..))

data Loc = Here Int | Gen String (Maybe Loc)
  deriving (Eq, Show)

-- no recursion through the annotation
data G r = Leaf Int | Node r r | Many [r]
  deriving (Eq, Show, Functor)

instance Show1 G where
  liftShowsPrec sp sl d = \case
    Leaf n -> showParen (d >= 11) (showString "Leaf " . showsPrec 11 n)
    Node a b -> showParen (d >= 11) (showString "Node " . sp 11 a . showChar ' ' . sp 11 b)
    Many xs -> showParen (d >= 11) (showString "Many " . sl xs)

type T = Cofree G Loc

showT :: T -> String
showT t = show t

exT :: Int -> Int -> String
exT a b = showT (Here a :< Node (Gen "x" (Just (Here b)) :< Leaf a) (Here (a - 1) :< Many [Here b :< Leaf b, Here 2 :< Many []]))

exTs :: Int -> String
exTs a = show [Here a :< Leaf (0 - a), Gen "y" Nothing :< Leaf 3]

-- the annotation holds the term again
data PatF a r = PAnn r a | PVar Int | PPair r r
  deriving (Eq, Show, Functor)

instance Show a => Show1 (PatF a) where
  liftShowsPrec sp _ d = \case
    PAnn r a -> showParen (d >= 11) (showString "PAnn " . sp 11 r . showChar ' ' . showsPrec 11 a)
    PVar n -> showParen (d >= 11) (showString "PVar " . showsPrec 11 n)
    PPair a b -> showParen (d >= 11) (showString "PPair " . sp 11 a . showChar ' ' . sp 11 b)

newtype Ann = Ann E
  deriving Show

type Pat = Fix (PatF Ann)

data EF p r = Lit Int | Lam Int r | Case r [(p, r)]
  deriving (Eq, Show, Functor)

instance Show p => Show1 (EF p) where
  liftShowsPrec sp _ d = \case
    Lit n -> showParen (d >= 11) (showString "Lit " . showsPrec 11 n)
    Lam v b -> showParen (d >= 11) (showString "Lam " . showsPrec 11 v . showChar ' ' . sp 11 b)
    Case s as -> showParen (d >= 11) (showString "Case " . sp 11 s . showString (show (map fst as)) . foldr (\(_, b) r -> sp 0 b . r) id as)

type E = Cofree (EF Pat) Int

showLayer :: EF Pat () -> String
showLayer e = show e

exLayer :: Int -> Int -> String
exLayer a b = showLayer (Case () [(Fix (PAnn (Fix (PVar a)) (Ann (b :< Lam 1 (a :< Case (2 :< Lit a) [(Fix (PVar 3), 4 :< Lit b)])))), ())])
