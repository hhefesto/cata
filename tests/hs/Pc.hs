-- Rule 16's test: megaparsec at Parsec Void String, the way telomare's
-- parser (src/Telomare/Parse.hs) uses it: a lexer from
-- Text.Megaparsec.Char.Lexer, try, <?>, choice over try, sepBy and many,
-- a lineFold, manyTill at a local indentation, and parsers that call each
-- other (expr through brackets, parens and let).
module Pc where

import Control.Monad (void)
import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isLetter)
import Data.Void (Void)
import Text.Megaparsec (Parsec, Pos, between, choice, eof, errorBundlePretty,
                        getOffset, many, manyTill, notFollowedBy, optional,
                        runParser, satisfy, sepBy, sepBy1, some, try, unPos,
                        (<?>), (<|>))
import Text.Megaparsec.Char (char, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L

type P = Parsec Void String

data E = Num Integer
       | Str String
       | Var String
       | Lst [E]
       | App E [E]
       | Let [(String, E)] E
       | At Int E
  deriving (Eq, Show)

lineComment :: P ()
lineComment = L.skipLineComment "--"

blockComment :: P ()
blockComment = L.skipBlockCommentNested "{-" "-}"

sc :: P ()
sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment blockComment

scn :: P ()
scn = L.space space1 lineComment blockComment

lexeme :: P a -> P a
lexeme = L.lexeme sc

symbol :: String -> P String
symbol = L.symbol sc

reserved :: String -> P ()
reserved w = (lexeme . try) (string w *> notFollowedBy (satisfy isAlphaNum))

keywords :: [String]
keywords = ["let", "in"]

identRaw :: P String
identRaw = try $ p >>= check
  where
    p = (:) <$> (satisfy isLetter <?> "letter") <*> many (satisfy isAlphaNum <?> "variable")
    check x = if x `elem` keywords
              then fail ("keyword " <> show x <> " cannot be an identifier")
              else pure x

ident :: P String
ident = lexeme identRaw

brackets :: P a -> P a
brackets = between (symbol "[") (symbol "]")

parens :: P a -> P a
parens = between (symbol "(") (symbol ")")

commaSep :: P a -> P [a]
commaSep p = p `sepBy` symbol ","

number :: P E
number = Num <$> lexeme L.decimal

stringLit :: P E
stringLit = Str <$> (char '"' >> manyTill L.charLiteral (char '"')) <* sc

located :: P E
located = do
  o <- getOffset
  e <- parens (scn *> expr <* scn)
  pure (At o e)

atom :: P E
atom = choice $ try <$> [ number
                        , stringLit
                        , Var <$> ident
                        , Lst <$> brackets (commaSep (scn *> expr <* scn))
                        , located
                        ]

app :: P E
app = do
  xs <- L.lineFold scn $ \sc' -> atom `sepBy1` try sc'
  case xs of
    f:args -> pure (mkApp f args)
    []     -> fail "expected expression"

mkApp :: E -> [E] -> E
mkApp f [] = f
mkApp f args = App f args

sameLvl :: Pos -> P a -> P a
sameLvl pos p = do
  lvl <- L.indentLevel
  if pos == lvl then p else fail "Expected same indentation."

binding :: P (String, E)
binding = do
  v <- ident <* scn
  _ <- symbol "=" <?> "assignment ="
  e <- scn *> expr <* scn
  pure (v, e)

letE :: P E
letE = do
  reserved "let" <* scn
  lvl <- L.indentLevel
  ds <- manyTill (sameLvl lvl binding) (reserved "in") <* scn
  Let ds <$> expr

expr :: P E
expr = choice [letE, app]

parseE :: String -> Either String E
parseE = first errorBundlePretty . runParser (scn *> expr <* scn <* eof) "t"

parseOk :: String -> Bool
parseOk s = case runParser (scn *> expr <* eof) "" s of
  Right _ -> True
  Left _  -> False

column :: String -> Int
column s = case runParser (many (char 'a') *> L.indentLevel :: P Pos) "" s of
  Right p -> unPos p
  Left _  -> 0

ex1 :: Either String E
ex1 = parseE "f [1, x] (g \"s\\n\")"

ex2 :: Either String E
ex2 = parseE "let a = 1\n    b = [a, 2]\nin f a b -- done"

ex3 :: Either String E
ex3 = parseE "{- a {- nested -} comment -} [1,\n 2]"

ex4 :: Either String E
ex4 = parseE "let in = 1 in in"

ex5 :: Either String E
ex5 = parseE "[1, 2"

ex6 :: Either String E
ex6 = parseE "f\n  x\ny"

ex7 :: Maybe [String]
ex7 = either (const Nothing) Just (runParser (optional (symbol "a") *> some ident <* eof :: P [String]) "" "a b  c")
