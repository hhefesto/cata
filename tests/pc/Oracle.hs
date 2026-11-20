import Data.Void (Void)
import Data.Char (isDigit)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type P = Parsec Void String

r :: Show a => P a -> String -> String
r p s = either errorBundlePretty show (runParser p "f.tel" s)

main :: IO ()
main = print $ concatMap (++ "\n=====\n")
  [ r (string "let" <* eof) "lex"
  , r (char 'a' <|> char 'b') "c"
  , r (label "thing" (char 'x')) "y"
  , r (try (string "ab") <|> string "ac") "ad"
  , r (takeWhile1P (Just "digit") isDigit) "x"
  , r (notFollowedBy (char 'a')) "a"
  , r eof "z"
  , r (L.decimal <* eof :: P Integer) "12x"
  , r (L.charLiteral <* eof) "\\n"
  , r (L.charLiteral <* eof) "\\q"
  , r L.charLiteral ""
  , r (L.charLiteral <* eof) "\\SOH"
  , r (L.charLiteral <* char 'x') "\\65x"
  , r (char '\t' >> char '\t' >> char 'a') "\t\tz"
  , r (char 'x' >> char '\n' >> string "ac") "x\nab"
  , r (char '\n' >> eof) "\n\n"
  , r (L.indentGuard space GT (mkPos 3) :: P Pos) "  a"
  , r (fail "boom" :: P ()) "q"
  , r (space1 >> string "if" >> eof) "  \t if then"
  , r (string "abc") "ab"
  , r (char 'a' >> L.charLiteral) "a\\^Ab"
  , r (string "\r\n") "x"
  , r (char ' ') "\NUL"
  , r ((,) <$> getSourcePos <*> (string "ab\n\tc" *> getSourcePos)) "ab\n\tcd"
  , r (optional (char 'a') >> char 'b') "c"
  , r (lookAhead (string "ab") >> string "ax") "ab"
  , r (hidden (char 'a') <|> char 'b') "c"
  , r (L.skipLineComment "--" >> eof) "-- hi\nx"
  ]
