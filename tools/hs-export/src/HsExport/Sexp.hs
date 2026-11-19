-- | The output syntax (FORMAT.md, "Lexical syntax"), the same as agda2bend's
--   agda-export so that one Bend reader (ToBend/Sexp.bend) reads both:
--   parenthesized lists, bare atoms over [A-Za-z0-9_.-], non-negative
--   decimal integers, and double-quoted strings whose only escapes are \"
--   and \\ (every other character, newline included, is written as itself
--   in UTF-8).
module HsExport.Sexp
  ( Sexp (..)
  , atom, str, int, list, tagged
  , render
  ) where

import Data.ByteString.Builder (Builder, char7, charUtf8, integerDec, stringUtf8)

data Sexp
  = A String     -- ^ an atom (the caller keeps it in [A-Za-z0-9_.-])
  | S String     -- ^ a string
  | I Integer    -- ^ an integer; a negative one is written (neg N)
  | L [Sexp]     -- ^ a list

atom :: String -> Sexp
atom = A

str :: String -> Sexp
str = S

int :: Integral a => a -> Sexp
int = I . toInteger

list :: [Sexp] -> Sexp
list = L

-- | (tag x y ...)
tagged :: String -> [Sexp] -> Sexp
tagged t xs = L (A t : xs)

-- | One line, single spaces.
render :: Sexp -> Builder
render s = case s of
  A t -> stringUtf8 t
  S t -> char7 '"' <> foldr (\c b -> esc c <> b) mempty t <> char7 '"'
  I n
    | n < 0 -> char7 '(' <> stringUtf8 "neg " <> integerDec (negate n) <> char7 ')'
    | otherwise -> integerDec n
  L [] -> char7 '(' <> char7 ')'
  L (x : xs) -> char7 '(' <> render x <> foldr (\y b -> char7 ' ' <> render y <> b) mempty xs <> char7 ')'
  where
    esc '"' = char7 '\\' <> char7 '"'
    esc '\\' = char7 '\\' <> char7 '\\'
    esc c = charUtf8 c
