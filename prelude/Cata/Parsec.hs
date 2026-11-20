-- | cata's model of the combinators of megaparsec 9.7.0 and
-- parser-combinators 1.3.1 that run a parser they are given more than
-- once, or hand one to a function, at @Parsec Void String@: their
-- definitions in those packages, the class methods at ParsecT. The
-- specialiser (bend/Spec.bend) writes a call of one of them in a package
-- as a call of this module's def, so that each runs as the package's own
-- code: a copy at its known parser arguments (rule 15), one def with the
-- parsers that call it back (rule 11's @.mu@). What runs a parser once,
-- and the parser's state and errors, are HsPrelude's (HsPc, in Bend).
--
-- tests/hs/Pc.hs checks these against megaparsec's own.
module Cata.Parsec where

import Control.Applicative (empty, optional, (<|>))
import Control.Monad (void)
import Data.Void (Void)
import Text.Megaparsec (Parsec, Pos, anySingle, hidden)
import Text.Megaparsec.Char (string)
import qualified Text.Megaparsec.Char.Lexer as L

type P = Parsec Void String

-- Control.Monad.Combinators -------------------------------------------------

-- | many p = go id where go f = optional p >>= .. go (f . (x :)): the
-- difference list as the reversed list
many :: P a -> P [a]
many p = go []
  where
    go acc = do
      r <- optional p
      case r of
        Nothing -> return (reverse acc)
        Just x -> go (x : acc)

-- | some p = liftM2 (:) p (many p)
some :: P a -> P [a]
some p = do
  x <- p
  xs <- many p
  return (x : xs)

sepBy :: P a -> P sep -> P [a]
sepBy p sep = do
  r <- optional p
  case r of
    Nothing -> return []
    Just x -> (x :) <$> many (sep >> p)

sepBy1 :: P a -> P sep -> P [a]
sepBy1 p sep = do
  x <- p
  (x :) <$> many (sep >> p)

-- | manyTill p end = fst <$> manyTill_ p end
manyTill :: P a -> P end -> P [a]
manyTill p end = go []
  where
    go acc = do
      done <- optional end
      case done of
        Just _ -> return (reverse acc)
        Nothing -> do
          x <- p
          go (x : acc)

-- | skipMany p = go where go = option False (True <$ p) >>= \more -> when more go
skipMany :: P a -> P ()
skipMany p = go
  where
    go = do
      more <- (True <$ p) <|> pure False
      if more then go else return ()

skipSome :: P a -> P ()
skipSome p = p >> skipMany p

-- Text.Megaparsec.Lexer and Text.Megaparsec.Char.Lexer ----------------------

-- | space sp line block = skipMany (choice [hidden sp, hidden line, hidden block])
space :: P () -> P () -> P () -> P ()
space sp line block = skipMany (hidden sp <|> (hidden line <|> (hidden block <|> empty)))

-- | skipBlockCommentNested start end = p >> void (manyTill e n) where e =
-- skipBlockCommentNested start end <|> void anySingle; p = string start;
-- n = string end (the locals in place: a known argument is no local)
skipBlockCommentNested :: String -> String -> P ()
skipBlockCommentNested start end =
  string start >> void (manyTill (skipBlockCommentNested start end <|> void anySingle) (string end))

indentGuard :: P () -> Ordering -> Pos -> P Pos
indentGuard sc ord ref = do
  sc
  actual <- L.indentLevel
  if compare actual ref == ord
    then return actual
    else L.incorrectIndent ord ref actual

-- | lineFold sc action = sc >> indentLevel >>= action . void . indentGuard sc GT
lineFold :: P () -> (P () -> P a) -> P a
lineFold sc action = do
  sc
  lvl <- L.indentLevel
  action (void (indentGuard sc GT lvl))
