-- | containers' Data.Graph and Data.Tree as telomare's EAL uses them, which
-- cata writes with its model (prelude/Cata/Graph.hs):
--   cycles: cycleStep's graph of Int nodes, each its own key, and the
--     members of its cycles (the pattern synonym CyclicSCC);
--   groups: components', rows and the variables they name as a bipartite
--     graph of (Int, Int) keys, its connected components' rows
--     (graphFromEdges' node of a vertex, Graph.components, Tree.flatten).
module Graph where

import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Graph as Graph
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Tree as Tree

-- | each pair a total and its summands; an edge from each summand to its
-- total
cycles :: [(Int, [Int])] -> [[Int]]
cycles eqs =
  let edges = IntMap.fromListWith (<>) [(l, [r]) | (r, ls) <- eqs, l <- ls]
      nodes = IntSet.toAscList (IntSet.fromList (concatMap (\(r, ls) -> r : ls) eqs))
  in [ms | CyclicSCC ms <- stronglyConnComp [(n, n, IntMap.findWithDefault [] n edges) | n <- nodes]]

-- | the vertices on no cycle
acyclic :: [(Int, [Int])] -> [Int]
acyclic eqs = [n | AcyclicSCC n <- stronglyConnComp [(r, r, ls) | (r, ls) <- eqs]]

-- | rows, each its variables' coefficients: the rows of each connected
-- component (rows sharing a variable)
groups :: IntMap (IntMap Int) -> [[Int]]
groups rows =
  let vars = IntSet.toList (IntSet.unions (fmap IntMap.keysSet (IntMap.elems rows)))
      rowNodes = [((), (0 :: Int, i), [(1, v) | v <- IntMap.keys r]) | (i, r) <- IntMap.toList rows, not (IntMap.null r)]
      varNodes = [((), (1, v), []) | v <- vars]
      (g, nodeFromVertex, _) = Graph.graphFromEdges (rowNodes <> varNodes)
      keyOf v = let (_, k, _) = nodeFromVertex v in k
      rowsOf t = [i | (0, i) <- fmap keyOf (Tree.flatten t)]
  in filter (not . null) (fmap rowsOf (Graph.components g))
