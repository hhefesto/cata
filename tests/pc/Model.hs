import qualified Pc
import qualified PcM

toks :: [String]
toks = ["a", "b1", "1", "23", "[", "]", ",", "(", ")", " ", "  ", "\n", "\n  ", "\t", "let", "in", "=", "--c\n", "{-", "-}", "\"", "\\n", "\\q", "x", "f"]

lcg :: Int -> Int
lcg s = (s * 1103515245 + 12345) `mod` 2147483648

gen :: Int -> Int -> [String]
gen 0 _ = []
gen n s = let s1 = lcg s; s2 = lcg s1; k = 1 + (s1 `div` 7) `mod` 12 in concat (take k (pick s2)) : gen (n - 1) s2
  where pick t = let t' = lcg t in toks !! ((t' `div` 13) `mod` length toks) : pick t'

main :: IO ()
main = do
  let ins = gen 4000 42 ++ ["let a = 1\n    b = [a, 2]\nin f a b", "f\n  x\n y", "{- a {- b -} c -} x", "[1, 2"]
      bad = [ (i, a, b) | i <- ins, let a = fmap show (Pc.parseE i), let b = fmap show (PcM.parseE i), a /= b ]
      oks = length [ () | i <- ins, Right _ <- [Pc.parseE i] ]
  putStrLn (show (length ins) ++ " inputs, " ++ show oks ++ " parse, " ++ show (length bad) ++ " differ")
  mapM_ print (take 5 bad)
