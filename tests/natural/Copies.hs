-- Copies.hs DIR...: cata's specialised copies (a def f__SUFFIX, with its
-- helpers f__SUFFIX'go, ...) in G's modules (DIR/*.hs, bend2hs's output,
-- where every type is erased), grouped by the def they copy (f).  A copy's
-- text is normalised by writing its own name as f__S; copies of f whose
-- normalised texts are equal are the same erased program at different
-- types: components of one natural transformation, so one polymorphic def
-- and one law would serve them all.  Prints, by f: copies, distinct texts,
-- and how many copies fix a function argument (a suffix _fNNN); then the
-- totals.
module Main (main) where

import Data.List (isPrefixOf, isInfixOf, sortOn, group, sort, nub)
import qualified Data.Map.Strict as M
import System.Directory (listDirectory)
import System.Environment (getArgs)
import System.FilePath ((</>), takeExtension)

-- a top-level def of G's: its name (c'...) and its whole line
defs :: String -> [(String, String)]
defs src = [ (takeWhile (/= ' ') l, l) | l <- lines src, "c'" `isPrefixOf` l ]

-- the def f a copy name copies, and the copy's suffix (up to its helper's ')
split2 :: String -> Maybe (String, String)
split2 n = go "" (drop 2 n)
  where
    go acc ('_' : '_' : r) = Just (reverse acc, takeWhile (/= '\'') r)
    go acc (c : r) = go (c : acc) r
    go _ [] = Nothing

replace :: String -> String -> String -> String
replace old new = go
  where
    go s | old `isPrefixOf` s = new ++ go (drop (length old) s)
    go (c : r) = c : go r
    go [] = []

-- every copy's name in a text (a c'NAME token with __) as its def's f__S
every :: String -> String
every ('c' : '\'' : r) =
  let (tok, rest) = span idc r
  in case split2 ("c'" ++ tok) of
       Just (f, sfx) -> "c'" ++ f ++ "__S" ++ drop (length f + 2 + length sfx) tok ++ every rest
       Nothing -> "c'" ++ tok ++ every rest
  where idc c = c `elem` (['A' .. 'Z'] ++ ['a' .. 'z'] ++ ['0' .. '9'] ++ "_'")
every (c : r) = c : every r
every [] = []

-- a suffix that names a known function argument (Rule 15's copies): _fDIGITS
fixesFn :: String -> Bool
fixesFn s = any isF (tails' s)
  where
    isF ('_' : 'f' : d : _) = d `elem` ['0' .. '9']
    isF _ = False
    tails' [] = [[]]
    tails' x@(_ : r) = x : tails' r

main :: IO ()
main = do
  dirs <- getArgs
  files <- concat <$> mapM (\d -> map (d </>) . filter ((== ".hs") . takeExtension) <$> listDirectory d) dirs
  srcs <- mapM readFile files
  let units = M.fromListWith (flip (++))
        [ ((f, file, sfx), [l])
        | (file, src) <- zip files srcs, (n, l) <- defs src, Just (f, sfx) <- [split2 n] ]
      -- every copy's name in a text as its def's f__S (all: the copies it
      -- calls too, which at the corresponding types are the corresponding
      -- components)
      own (f, sfx) = replace ("c'" ++ f ++ "__" ++ sfx) ("c'" ++ f ++ "__S")
      norm ((f, _, sfx), ls) = (f, (sfx, unlines (map (own (f, sfx)) ls), unlines (map every ls)))
      byF = M.fromListWith (++) [ (f, [x]) | u <- M.toList units, let (f, x) = norm u ]
      rows = [ (f, length xs, length (nub [ t | (_, t, _) <- xs ]), length (nub [ t | (_, _, t) <- xs ]), length (filter (\(s, _, _) -> fixesFn s) xs)) | (f, xs) <- M.toList byF ]
  mapM_ (\(f, n, d, e, k) -> putStrLn (f ++ "\tcopies " ++ show n ++ "\tdistinct " ++ show d ++ "\tdistinct-up-to-copies " ++ show e ++ "\tfix-a-function " ++ show k)) (sortOn (\(_, n, _, _, _) -> negate n) rows)
  let tot = sum [ n | (_, n, _, _, _) <- rows ]
      dist = sum [ d | (_, _, d, _, _) <- rows ]
      dist2 = sum [ e | (_, _, _, e, _) <- rows ]
      fx = sum [ k | (_, _, _, _, k) <- rows ]
      shared = sum [ n | (_, n, d, _, _) <- rows, d == 1, n > 1 ]
      shared2 = sum [ n | (_, n, _, e, _) <- rows, e == 1, n > 1 ]
  putStrLn ("defs copied " ++ show (length rows) ++ ", copies " ++ show tot ++ " in all modules, " ++ show (length (nub [ (f, s) | (f, _, s) <- M.keys units ])) ++ " by name (fixing a function argument " ++ show fx ++ "), distinct erased texts " ++ show dist ++ " (" ++ show dist2 ++ " up to the copies they call); copies of a def all of whose copies are one erased text: " ++ show shared ++ " (" ++ show shared2 ++ ")")
