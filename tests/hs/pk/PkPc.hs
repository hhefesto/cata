module PkPc where

-- parsers with laws (HsPc.answer): a lexer, alternatives, a fold of
-- operators, a parser that takes arguments, one that fails
import Data.Char (isAlpha, isAlphaNum)
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type P = Parsec Void String

data E = V String | N Int | App E E | Pr E E
  deriving (Eq, Show)

ws :: P ()
ws = L.space space1 (L.skipLineComment "#") empty

tok :: P a -> P a
tok = L.lexeme ws

sym :: String -> P String
sym = L.symbol ws

name :: P String
name = tok ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)) <?> "name"

number :: P Int
number = tok L.decimal

pr :: P E
pr = do
  _ <- sym "("
  a <- expr
  _ <- sym ","
  b <- expr
  _ <- sym ")"
  pure (Pr a b)

atom :: P E
atom = choice [try pr, V <$> name, N <$> number, between (sym "(") (sym ")") expr]

expr :: P E
expr = foldl App <$> atom <*> many atom

upTo :: Int -> P [Int]
upTo n = do
  x <- number
  if x > n then fail "too large" else pure [x]

two :: Char -> Char -> P (Char, Char)
two a b = (,) <$> char a <*> (char b <|> char ' ')

-- a parser as an argument
twice :: P a -> P (a, a)
twice p = (,) <$> p <*> p

orElse :: P Int -> Int -> P Int
orElse p n = p <|> pure n
