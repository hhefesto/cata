-- | The skeleton of telomare's parse of a file, as GHC runs telomare's
-- parser: per module item its kind, names and the spans of the names and
-- of the body's root, or the parse error's text. skel.bend.part writes the
-- same from cata's Bend of Telomare.Parse; run.sh compares the two.
--   Skel NAME FILE   (NAME: the source name the parser records)
--   Skel --bend NAME FILE: the Bend call Sk.file("NAME", "TEXT") that
--   writes the same in skel.bend.part
module Main (main) where

import Control.Comonad.Cofree (Cofree (..))
import System.Environment (getArgs)
import Telomare.IR.Loc (LocTag (..), LocatedName (..))
import Telomare.IR.Surface (DefinitionF (..), ImportDecl (..), ModuleItem (..),
                            ParsedSurfaceTerm)
import Telomare.Parse (runParseModule)

loc :: LocTag -> String
loc (SourceLoc s) = showsPrec 0 s ""
loc _ = "gen"

name :: LocatedName -> String
name (LocatedName (l, s)) = s ++ " " ++ loc l

root :: ParsedSurfaceTerm -> String
root (l :< _) = loc l

ann :: Maybe a -> String
ann Nothing = ""
ann (Just _) = " ann"

item :: ModuleItem ParsedSurfaceTerm -> String
item (ModuleImportItem (ImportDecl l m q)) =
  "import " ++ name m ++ " at " ++ loc l ++ maybe "" (\x -> " as " ++ name x) q ++ "\n"
item (ModuleDefinitionItem (SingleDefF n a t)) =
  "def " ++ name n ++ ann a ++ " body " ++ root t ++ "\n"
item (ModuleDefinitionItem (ListDefF l ns t)) =
  "defs " ++ loc l ++ concatMap (\x -> " " ++ name x) ns ++ " body " ++ root t ++ "\n"

skel :: Either String [ModuleItem ParsedSurfaceTerm] -> String
skel (Left e) = "error\n" ++ e ++ "\n"
skel (Right xs) = concatMap item xs

-- a Bend string literal's text
lit :: String -> String
lit s = "\"" ++ concatMap esc s ++ "\""
  where
    esc '\\' = "\\\\"
    esc '"' = "\\\""
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--bend", n, f] -> do
      src <- readFile f
      putStr ("Sk.file(" ++ lit n ++ ", " ++ lit src ++ ")")
    [n, f] -> do
      src <- readFile f
      putStr ("== " ++ n ++ "\n" ++ skel (runParseModule n src))
    _ -> error "usage: Skel [--bend] NAME FILE"
