-- a list of shows put together with a separator (Surface's Show1), shows of
-- a list of pairs with a Fix in it
{-# LANGUAGE DeriveFunctor #-}
module ShowSep where

import Data.Fix (Fix (..))
import Data.Functor.Classes (Show1 (..))
import Data.List (intersperse)

data P r = V String | Q r r
  deriving (Eq, Show, Functor)

instance Show1 P where
  liftShowsPrec sp _ d p = case p of
    V s -> showString "V " . shows s
    Q a b -> showString "Q " . sp 11 a . showChar ' ' . sp 11 b

data E r = Let [(String, r)] r | Lst [r] | Lam [(Int, Fix P)] r | N Int
  deriving (Show, Functor)

instance Show1 E where
  liftShowsPrec sp _ d e = case e of
    Let bs b ->
      let showB (s, x) = showChar '(' . shows s . showString ", " . sp 11 x . showChar ')'
          showBs ys = showChar '[' . foldr (.) id (intersperse (showString ", ") (fmap showB ys)) . showChar ']'
      in showString "Let " . showBs bs . showChar ' ' . sp 11 b
    Lst xs -> showString "Lst [" . foldr (.) id (intersperse (showString ", ") (fmap (sp 11) xs)) . showChar ']'
    Lam ps b -> showString "Lam " . shows ps . showChar ' ' . sp 11 b
    N n -> showString "N " . shows n

term :: Int -> Fix E
term n = Fix (Let [("x", Fix (N n)), ("y", Fix (Lst [Fix (N 1), Fix (N (n + 1))]))] (Fix (Lam [(n, Fix (Q (Fix (V "a")) (Fix (V "b")))), (2, Fix (V "c"))] (Fix (Lst [])))))

exShow :: Int -> String
exShow n = show (term n)
