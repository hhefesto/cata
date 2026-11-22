-- | cata's model of Data.Graph (prelude/Cata/Graph.hs) against containers'
-- own, on graphs drawn from a fixed seed: every answer the same, its order
-- included.
--   stronglyConnComp at Int keys (telomare's EAL cycleStep: each node its
--     own key; keys sparse, out-lists with keys of no node, self-loops,
--     repeats) and at String nodes with Int keys given in any order;
--   graphFromEdges and components at telomare's bipartite (Int, Int) keys
--     (EAL's components): each vertex's node, each key's vertex, and each
--     component's flatten;
--   all of them at keys two nodes share.
module Main (main) where

import qualified Cata.Graph as M
import qualified Data.Graph as G
import qualified Data.Tree as T
import System.Exit (exitFailure)

-- | a linear congruential generator (Knuth's MMIX constants), its high bits
next :: Integer -> Integer
next s = (6364136223846793005 * s + 1442695040888963407) `mod` (2 ^ (64 :: Int))

draws :: Integer -> [Int]
draws s = let s' = next s in fromInteger (s' `div` (2 ^ (33 :: Int))) : draws s'

-- | n nodes' keys (from a range of 3n: sparse) and out-lists of up to 4
-- keys from the same range (some no node's)
intGraph :: [Int] -> ([(Int, Int, [Int])], [Int])
intGraph (a : rest) =
  let n = a `mod` 12
      (keys, r1) = distinct n (3 * n + 1) rest []
      (outs, r2) = outLists keys (3 * n + 1) r1
  in ([(k, k, o) | (k, o) <- zip keys outs], r2)
intGraph [] = ([], [])

-- | keys with repeats (containers' graphFromEdges keeps both nodes, and its
-- binary search finds one of them)
dupGraph :: [Int] -> ([(String, Int, [Int])], [Int])
dupGraph (a : rest) =
  let n = a `mod` 10
      m = n `div` 2 + 1
      (ks, r1) = splitAt n rest
      keys = map (`mod` m) ks
      (outs, r2) = outLists keys (m + 1) r1
  in ([("d" ++ show i, k, o) | (i, k, o) <- zip3 [0 :: Int ..] keys outs], r2)
dupGraph [] = ([], [])

distinct :: Int -> Int -> [Int] -> [Int] -> ([Int], [Int])
distinct 0 _ r acc = (reverse acc, r)
distinct n m (x : r) acc
  | (x `mod` m) `elem` acc = distinct n m r acc
  | otherwise = distinct (n - 1) m r ((x `mod` m) : acc)
distinct _ _ [] acc = (reverse acc, [])

outLists :: [Int] -> Int -> [Int] -> ([[Int]], [Int])
outLists [] _ r = ([], r)
outLists (_ : ks) m (c : r) =
  let len = c `mod` 5
      (o, r1) = splitAt len r
      (os, r2) = outLists ks m r1
  in (map (`mod` m) o : os, r2)
outLists _ _ [] = ([], [])

-- | telomare's components: rows (0, i) naming variables (1, v), and the
-- variables, nodes ()
bipartite :: [Int] -> ([((), (Int, Int), [(Int, Int)])], [Int])
bipartite (a : b : rest) =
  let rows = a `mod` 7
      vars = b `mod` 9
      (rs, r1) = rowLists rows (max 1 vars) rest
  in ([((), (0, i), [(1, v) | v <- vs]) | (i, vs) <- zip [0 ..] rs] ++ [((), (1, v), []) | v <- [0 .. vars - 1]], r1)
bipartite _ = ([], [])

rowLists :: Int -> Int -> [Int] -> ([[Int]], [Int])
rowLists 0 _ r = ([], r)
rowLists n m (c : r) =
  let (o, r1) = splitAt (c `mod` 4) r
      (os, r2) = rowLists (n - 1) m r1
  in (map (`mod` m) o : os, r2)
rowLists _ _ [] = ([], [])

sccG :: G.SCC a -> Either a [a]
sccG (G.AcyclicSCC v) = Left v
sccG (G.CyclicSCC vs) = Right vs

sccM :: M.SCC a -> Either a [a]
sccM (M.AcyclicSCC v) = Left v
sccM (M.CyclicSCC vs) = Right vs

checkInt :: [(Int, Int, [Int])] -> Bool
checkInt es = map sccG (G.stronglyConnComp es) == map sccM (M.stronglyConnComp es)

-- | String nodes, the list in the order drawn (not by key)
checkNamed :: [(Int, Int, [Int])] -> Bool
checkNamed es =
  let named = [("n" ++ show k, k, o) | (_, k, o) <- reverse es]
  in map sccG (G.stronglyConnComp named) == map sccM (M.stronglyConnComp named)

checkDup :: [(String, Int, [Int])] -> Bool
checkDup es =
  let (g, nodeG, vertG) = G.graphFromEdges es
      (m, nodeM, vertM) = M.graphFromEdges es
      vs = [0 .. length es - 1]
  in map sccG (G.stronglyConnComp es) == map sccM (M.stronglyConnComp es)
       && map nodeG vs == map nodeM vs
       && map vertG [-1 .. 6] == map vertM [-1 .. 6]
       && map (map (\v -> nodeG v) . T.flatten) (G.components g) == map (map (\v -> nodeM v) . M.flatten) (M.components m)

checkBip :: [((), (Int, Int), [(Int, Int)])] -> Bool
checkBip ns =
  let (g, nodeG, vertG) = G.graphFromEdges ns
      (m, nodeM, vertM) = M.graphFromEdges ns
      vs = [0 .. length ns - 1]
      keyG v = let (_, k, _) = nodeG v in k
      keyM v = let (_, k, _) = nodeM v in k
      keys = [k | (_, k, _) <- ns] ++ [(2, 0), (0, 99), (1, -1)]
  in map nodeG vs == map nodeM vs
       && map vertG keys == map vertM keys
       && map (map keyG . T.flatten) (G.components g) == map (map keyM . M.flatten) (M.components m)

main :: IO ()
main = do
  let go :: Int -> [Int] -> (Int, Int, Int, Int, [String]) -> (Int, Int, Int, Int, [String])
      go 0 _ acc = acc
      go i r (a, b, c, d, bad) =
        let (es, r1) = intGraph r
            (ns, r2) = bipartite r1
            (ds, r3) = dupGraph r2
            okI = checkInt es
            okN = checkNamed es
            okB = checkBip ns
            okD = checkDup ds
            bad' = [show es | not okI] ++ [show es | not okN] ++ [show ns | not okB] ++ [show ds | not okD] ++ bad
        in go (i - 1) r3 (a + fromEnum okI, b + fromEnum okN, c + fromEnum okB, d + fromEnum okD, bad')
      runs = 20000
      (a, b, c, d, bad) = go runs (draws 20261122) (0, 0, 0, 0, [])
      of_ x = show x ++ "/" ++ show runs
  putStrLn ("stronglyConnComp Int " ++ of_ a ++ ", named " ++ of_ b ++ "; graphFromEdges+components " ++ of_ c ++ "; repeated keys " ++ of_ d)
  if null bad then putStrLn "Data.Graph model: the same as containers" else mapM_ putStrLn (take 5 bad) >> exitFailure
