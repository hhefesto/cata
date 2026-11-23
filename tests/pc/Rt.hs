-- Unit.bend.part's 28 parsers on BendRt's HsPc (prelude/Back/BendPc.hs),
-- each written as the Bend one is, its answer shown as Oracle.hs shows
-- megaparsec's: tests/pc/rt.sh compares the two texts.
import BendPc

type P a = B'HsPrelude'HsPc'P a

pos :: B'HsPrelude'HsPcPos -> String
pos (B'HsPrelude'HsPcPos n l c) =
  concat ["SourcePos {sourceName = ", show n, ", sourceLine = Pos ", show l, ", sourceColumn = Pos ", show c, "}"]

r :: (a -> String) -> P a -> String -> String
r sh p inp = case b'HsPrelude'HsPc'runParser p "f.tel" inp of
  Left b -> b'HsPrelude'HsPc'errorBundlePretty b
  Right x -> sh x

u :: () -> String
u _ = "()"

str :: String -> P String
str = b'HsPrelude'HsPc'string

ch :: Char -> P Char
ch = b'HsPrelude'HsPc'char

lit :: P Char
lit = b'HsPrelude'HsPc'charLiteral

main :: IO ()
main = print $ concatMap (++ "\n=====\n")
  [ r show (b'HsPrelude'HsPc'left (str "let") b'HsPrelude'HsPc'eof) "lex"
  , r show (b'HsPrelude'HsPc'alt (ch 'a') (ch 'b')) "c"
  , r show (b'HsPrelude'HsPc'label "thing" (ch 'x')) "y"
  , r show (b'HsPrelude'HsPc'alt (b'HsPrelude'HsPc'try (str "ab")) (str "ac")) "ad"
  , r show (b'HsPrelude'HsPc'takeWhile1P (\c -> c >= '0' && c <= '9') (Just "digit")) "x"
  , r u (b'HsPrelude'HsPc'notFollowedBy (ch 'a')) "a"
  , r u b'HsPrelude'HsPc'eof "z"
  , r show (b'HsPrelude'HsPc'left b'HsPrelude'HsPc'decimal b'HsPrelude'HsPc'eof) "12x"
  , r show (b'HsPrelude'HsPc'left lit b'HsPrelude'HsPc'eof) "\\n"
  , r show (b'HsPrelude'HsPc'left lit b'HsPrelude'HsPc'eof) "\\q"
  , r show lit ""
  , r show (b'HsPrelude'HsPc'left lit b'HsPrelude'HsPc'eof) "\\SOH"
  , r show (b'HsPrelude'HsPc'left lit (ch 'x')) "\\65x"
  , r show (b'HsPrelude'HsPc'then (ch '\t') (b'HsPrelude'HsPc'then (ch '\t') (ch 'a'))) "\t\tz"
  , r show (b'HsPrelude'HsPc'then (ch 'x') (b'HsPrelude'HsPc'then (ch '\n') (str "ac"))) "x\nab"
  , r u (b'HsPrelude'HsPc'then (ch '\n') b'HsPrelude'HsPc'eof) "\n\n"
  , r show (b'HsPrelude'HsPc'then b'HsPrelude'HsPc'space (b'HsPrelude'HsPc'bind b'HsPrelude'HsPc'indentLevel (\a -> b'HsPrelude'HsPc'incorrectIndent GT 3 a :: P Int))) "  a"
  , r u (b'HsPrelude'HsPc'fail "boom") "q"
  , r u (b'HsPrelude'HsPc'then b'HsPrelude'HsPc'space1 (b'HsPrelude'HsPc'then (str "if") b'HsPrelude'HsPc'eof)) "  \t if then"
  , r show (str "abc") "ab"
  , r show (b'HsPrelude'HsPc'then (ch 'a') lit) "a\\^Ab"
  , r show (str "\r\n") "x"
  , r show (ch ' ') "\NUL"
  , r (\(a, b) -> concat ["(", pos a, ",", pos b, ")"])
      (b'HsPrelude'HsPc'bind b'HsPrelude'HsPc'getSourcePos (\p1 -> b'HsPrelude'HsPc'then (str "ab\n\tc") (b'HsPrelude'HsPc'map (\p2 -> (p1, p2)) b'HsPrelude'HsPc'getSourcePos))) "ab\n\tcd"
  , r u (b'HsPrelude'HsPc'then (b'HsPrelude'HsPc'optional (ch 'a')) (b'HsPrelude'HsPc'void (ch 'b'))) "c"
  , r show (b'HsPrelude'HsPc'then (b'HsPrelude'HsPc'lookAhead (str "ab")) (str "ax")) "ab"
  , r show (b'HsPrelude'HsPc'alt (b'HsPrelude'HsPc'hidden (ch 'a')) (ch 'b')) "c"
  , r u (b'HsPrelude'HsPc'then (b'HsPrelude'HsPc'skipLineComment "--") b'HsPrelude'HsPc'eof) "-- hi\nx"
  ]
