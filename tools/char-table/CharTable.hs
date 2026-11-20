-- Writes prelude/HsChar.bend: Data.Char's predicates as GHC 9.10.3's base
-- answers them (its Unicode tables), as sorted ranges of code points, so
-- the fold's isAlpha, isAlphaNum, ... agree with GHC on every Char.
--   runghc tools/char-table/CharTable.hs > prelude/HsChar.bend
-- (in pieces of 100 ranges: Bend expands no much longer literal)
import Data.Char
import Data.List (intercalate)

ranges :: (Char -> Bool) -> [(Int, Int)]
ranges p = go [c | c <- [0 .. 0x10FFFF], p (chr c)]
  where
    go [] = []
    go (c : cs) = let (hi, rest) = run c cs in (c, hi) : go rest
    run h (d : ds) | d == h + 1 = run d ds
    run h ds = (h, ds)

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = let (a, b) = splitAt n xs in a : chunks n b

table :: String -> (Char -> Bool) -> String
table name p =
  concat
    [ "def HsChar." ++ name ++ ".r" ++ show i ++ "() -> List<&2, HsChar.R>:\n  ["
        ++ intercalate ", " ["HsChar.R{" ++ show a ++ ", " ++ show b ++ "}" | (a, b) <- c]
        ++ "]\n\n"
    | (i, c) <- zip [0 :: Int ..] cs ]
    ++ "def HsChar." ++ name ++ ".r() -> List<&2, HsChar.R>:\n  List.concat(&2, HsChar.R, ["
    ++ intercalate ", " ["HsChar." ++ name ++ ".r" ++ show i ++ "()" | i <- [0 .. length cs - 1]]
    ++ "])\n\ndef HsChar." ++ name ++ "(+c: Char) -> Bool:\n  HsChar.in(HsChar." ++ name ++ ".r(), Char.to_u32(c))\n"
  where
    cs = chunks 100 (ranges p)

main :: IO ()
main = do
  putStr (unlines
    [ "# Written by tools/char-table/CharTable.hs (GHC 9.10.3's base): Data.Char's"
    , "# predicates as sorted ranges of code points, each answered as GHC does."
    , "type HsChar.R is Data:"
    , "  HsChar.R{lo: U32, hi: U32}"
    , ""
    , "def HsChar.in(rs: List<&2, HsChar.R>, +k: U32) -> Bool:"
    , "  match rs:"
    , "    case Nil{}:"
    , "      False{}"
    , "    case HsChar.R{+lo, +hi} <> t:"
    , "      HsBool.if(Bool, U32.is_lt(k, lo), _ => False{}, _ => HsBool.if(Bool, U32.is_le(k, hi), _ => True{}, _ => HsChar.in(t, k)))"
    , "" ])
  mapM_ (putStrLn . uncurry table)
    [ ("isAlpha", isAlpha), ("isAlphaNum", isAlphaNum), ("isUpper", isUpper)
    , ("isLower", isLower), ("isSpace", isSpace), ("isDigit", isDigit) ]
