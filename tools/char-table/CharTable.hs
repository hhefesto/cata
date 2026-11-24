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

-- a case map (toUpper, toLower) as its changed code points' runs: from lo to
-- hi by st (1 or 2), k is k + d (up) or k - d
maps :: (Char -> Char) -> [(Int, Int, Int, Bool, Int)]
maps f = go [(c, ord (f (chr c)) - c) | c <- [0 .. 0x10FFFF], f (chr c) /= chr c]
  where
    go [] = []
    go ((c, d) : xs) =
      let (h1, r1) = run 1 c d xs
          (h2, r2) = run 2 c d xs
          (st, h, r) = if h2 > h1 then (2, h2, r2) else (1, h1, r1)
       in (c, h, st, d >= 0, abs d) : go r
    run s h d ((c, e) : xs) | c == h + s, e == d = run s c d xs
    run _ h _ xs = (h, xs)

mtable :: String -> (Char -> Char) -> String
mtable name f =
  concat
    [ "def HsChar." ++ name ++ ".m" ++ show i ++ "() -> List<&2, HsChar.M>:\n  ["
        ++ intercalate ", " ["HsChar.M{" ++ intercalate ", " [show a, show b, show s, if u then "True{}" else "False{}", show d] ++ "}" | (a, b, s, u, d) <- c]
        ++ "]\n\n"
    | (i, c) <- zip [0 :: Int ..] cs ]
    ++ "def HsChar." ++ name ++ ".m() -> List<&2, HsChar.M>:\n  List.concat(&2, HsChar.M, ["
    ++ intercalate ", " ["HsChar." ++ name ++ ".m" ++ show i ++ "()" | i <- [0 .. length cs - 1]]
    ++ "])\n\ndef HsChar." ++ name ++ "(c: Char) -> Char:\n  Char.from_u32(HsChar.to(HsChar." ++ name ++ ".m(), Char.to_u32(c)))\n"
  where
    cs = chunks 60 (maps f)

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
    , ""
    , "# a run of a case map: from lo to hi by st, k is k + d (up) or k - d"
    , "type HsChar.M is Data:"
    , "  HsChar.M{lo: U32, hi: U32, st: U32, up: Bool, d: U32}"
    , ""
    , "def HsChar.to(ms: List<&2, HsChar.M>, +k: U32) -> U32:"
    , "  match ms:"
    , "    case Nil{}:"
    , "      k"
    , "    case HsChar.M{+lo, +hi, +st, +up, +d} <> t:"
    , "      +in = Bool.and(U32.is_le(k, hi), Bool.or(U32.is_eq(st, 1), U32.is_eq(U32.and(U32.sub(k, lo), 1), 0)))"
    , "      HsBool.if(U32, U32.is_lt(k, lo), _ => k, _ => HsBool.if(U32, in, _ => Bool.pick(U32, up, U32.add(k, d), U32.sub(k, d)), _ => HsChar.to(t, k)))"
    , "" ])
  mapM_ (putStrLn . uncurry table)
    [ ("isAlpha", isAlpha), ("isAlphaNum", isAlphaNum), ("isUpper", isUpper)
    , ("isLower", isLower), ("isSpace", isSpace), ("isDigit", isDigit) ]
  mapM_ (putStrLn . uncurry mtable) [("toUpper", toUpper), ("toLower", toLower)]
