{-# LANGUAGE ExplicitForAll #-}

-- | cata's model of containers 0.7's Data.Graph (the part telomare's EAL
-- uses: 'stronglyConnComp', 'graphFromEdges', 'components') and Data.Tree's
-- 'Tree' and 'flatten': containers' own algorithms (King and Launchbury's
-- depth-first search, as Data.Graph bundles it), so that every answer, its
-- order included, is containers'. The specialiser (bend/Spec.bend, sp.p5)
-- reads a package's Data.Graph and Data.Tree names as this module's: a
-- 'Vertex' is an Int, a 'Graph' (containers' @Array Vertex [Vertex]@,
-- indexed from 0) is an IntMap from each vertex to its successors, and the
-- pattern synonym @CyclicSCC vs@ (containers' NECyclicSCC's list) is the
-- constructor of the same name here.
--
-- The visited set is an IntSet threaded through the search, as containers'
-- portable SetM; the arrays are IntMaps; graphFromEdges' sort is a stable
-- one, as Data.List's (so the same order, equal keys too), and its binary
-- search over the sorted keys is containers'.
--
-- The functions the specialiser maps containers' to quantify their type
-- variables in containers' order, which is GHC's implicit one (first
-- appearance, the context's first): @forall key node.@ for
-- 'graphFromEdges', 'stronglyConnComp' and 'stronglyConnCompR', whose
-- @Ord key =>@ comes first; a call's type arguments are applied in that
-- order.
--
-- tests/graph/run.sh checks these against containers' own.
module Cata.Graph where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | Data.Tree's rose tree
data Tree a = Node a [Tree a]

-- | containers' strongly connected component: a vertex on no cycle, or a
-- cycle's vertices (never none)
data SCC v = AcyclicSCC v | CyclicSCC [v]

-- Data.Tree -----------------------------------------------------------------

-- | the labels in pre-order, as containers' (flatten t = squish t [] where
-- squish (Node x ts) xs = x : foldr squish xs ts), read off a stack of the
-- trees still to read: a node's label, then its children, then the trees
-- after it (one function, not two that call each other: the fold merges
-- no group of polymorphic defs)
flatten :: forall a. Tree a -> [a]
flatten t = squish [t]

squish :: forall a. [Tree a] -> [a]
squish [] = []
squish (Node x ts : rest) = x : squish (ts ++ rest)

-- Graphs --------------------------------------------------------------------

-- | the vertices, 0 to n - 1 (Data.Graph's indices)
vertices :: IntMap [Int] -> [Int]
vertices g = IntMap.keys g

-- | the edges, (v, w) for each successor w of each vertex v in order
edges :: IntMap [Int] -> [(Int, Int)]
edges g = edgesFrom (IntMap.toList g)

edgesFrom :: [(Int, [Int])] -> [(Int, Int)]
edgesFrom [] = []
edgesFrom ((v, ws) : rest) = edgesOf v ws (edgesFrom rest)

edgesOf :: Int -> [Int] -> [(Int, Int)] -> [(Int, Int)]
edgesOf v [] acc = acc
edgesOf v (w : ws) acc = (v, w) : edgesOf v ws acc

reverseE :: [(Int, Int)] -> [(Int, Int)]
reverseE [] = []
reverseE ((v, w) : es) = (w, v) : reverseE es

-- | buildG (0, n - 1) es: accumArray (flip (:)) [], each edge's target put
-- in front of the ones before it
buildG :: Int -> [(Int, Int)] -> IntMap [Int]
buildG n es = buildAcc es (emptyG 0 n)

emptyG :: Int -> Int -> IntMap [Int]
emptyG i n = emptyFrom (upTo i n) IntMap.empty

emptyFrom :: [Int] -> IntMap [Int] -> IntMap [Int]
emptyFrom [] m = m
emptyFrom (v : vs) m = emptyFrom vs (IntMap.insert v [] m)

-- | [i .. n - 1]
upTo :: Int -> Int -> [Int]
upTo i n
  | i >= n = []
  | otherwise = i : upTo (i + 1) n

buildAcc :: [(Int, Int)] -> IntMap [Int] -> IntMap [Int]
buildAcc [] m = m
buildAcc ((v, w) : es) m = buildAcc es (IntMap.insert v (w : IntMap.findWithDefault [] v m) m)

transposeG :: IntMap [Int] -> IntMap [Int]
transposeG g = buildG (IntMap.size g) (reverseE (edges g))

-- | the graph with every edge in both directions
undirected :: IntMap [Int] -> IntMap [Int]
undirected g = buildG (IntMap.size g) (edges g ++ reverseE (edges g))

-- | graphFromEdges: the nodes sorted by key, vertex i the i-th; the graph,
-- each vertex's node, and the vertex of a key (Nothing: no node's)
graphFromEdges :: forall key node. Ord key => [(node, key, [key])] -> (IntMap [Int], Int -> (node, key, [key]), key -> Maybe Int)
graphFromEdges edges0 = graphFromNumbered (number (sortNodes edges0) 0)

-- | graphFromEdges' parts, its tuple's functions as functions (Spec writes a
-- let of its tuple as lets of these): the numbered nodes, the graph, each
-- vertex's node, a key's vertex
numberedNodes :: forall key node. Ord key => [(node, key, [key])] -> [(Int, (node, key, [key]))]
numberedNodes edges0 = number (sortNodes edges0) 0

graphOfNumbered :: forall key node. Ord key => [(Int, (node, key, [key]))] -> IntMap [Int]
graphOfNumbered ns = graphOf (keysOf ns) ns

nodesOfNumbered :: forall key node. [(Int, (node, key, [key]))] -> IntMap (node, key, [key])
nodesOfNumbered ns = IntMap.fromList ns

keysOfNumbered :: forall key node. [(Int, (node, key, [key]))] -> IntMap key
keysOfNumbered ns = keysOf ns

graphFromNumbered :: forall node key. Ord key => [(Int, (node, key, [key]))] -> (IntMap [Int], Int -> (node, key, [key]), key -> Maybe Int)
graphFromNumbered ns = (graphOf (keysOf ns) ns, nodeAt (IntMap.fromList ns), vertexOf (keysOf ns))

-- | each vertex's key
keysOf :: forall node key. [(Int, (node, key, [key]))] -> IntMap key
keysOf [] = IntMap.empty
keysOf ((v, (_, k, _)) : rest) = IntMap.insert v k (keysOf rest)

nodeAt :: forall node key. IntMap (node, key, [key]) -> Int -> (node, key, [key])
nodeAt m v = m IntMap.! v

-- | the graph of numbered nodes: each vertex's successors, the keys its
-- node names that are some node's
graphOf :: forall node key. Ord key => IntMap key -> [(Int, (node, key, [key]))] -> IntMap [Int]
graphOf keys [] = IntMap.empty
graphOf keys ((v, (_, _, ks)) : rest) = IntMap.insert v (keyVertices keys ks) (graphOf keys rest)

keyVertices :: forall key. Ord key => IntMap key -> [key] -> [Int]
keyVertices keys [] = []
keyVertices keys (k : ks) = case vertexOf keys k of
  Just v -> v : keyVertices keys ks
  Nothing -> keyVertices keys ks

-- | containers' key_vertex: a binary search over the vertices' keys,
-- sorted (so that, at a key two nodes have, it finds containers' one)
vertexOf :: forall key. Ord key => IntMap key -> key -> Maybe Int
vertexOf keys k = findVertex keys k 0 (IntMap.size keys - 1)

findVertex :: forall key. Ord key => IntMap key -> key -> Int -> Int -> Maybe Int
findVertex keys k a b = if a > b then Nothing else findAt keys k a b (a + (b - a) `div` 2)

-- | (mid is always a vertex, a to b being some: the lookup's Nothing is not
-- reached, and keeps the search total)
findAt :: forall key. Ord key => IntMap key -> key -> Int -> Int -> Int -> Maybe Int
findAt keys k a b mid = case IntMap.lookup mid keys of
  Nothing -> Nothing
  Just km -> case compare k km of
    LT -> findVertex keys k a (mid - 1)
    EQ -> Just mid
    GT -> findVertex keys k (mid + 1) b

-- | each element with its index from i, in order (the list first: Bend
-- reads a self-call's arguments left to right, and the list is the one that
-- shrinks)
number :: forall a. [a] -> Int -> [(Int, a)]
number [] i = []
number (x : xs) i = (i, x) : number xs (i + 1)

-- | Data.List.sortBy on the key: an insertion sort, stable (an equal key
-- goes after the ones there)
sortNodes :: forall node key. Ord key => [(node, key, [key])] -> [(node, key, [key])]
sortNodes [] = []
sortNodes (x : xs) = insertNode x (sortNodes xs)

-- | x before the first node of a greater key: x came first in the list, so
-- it stays before an equal one
insertNode :: forall node key. Ord key => (node, key, [key]) -> [(node, key, [key])] -> [(node, key, [key])]
insertNode x [] = [x]
insertNode (n, k, ks) ((n2, k2, ks2) : ys) = case compare k k2 of
  GT -> (n2, k2, ks2) : insertNode (n, k, ks) ys
  _ -> (n, k, ks) : (n2, k2, ks2) : ys

-- Depth-first search --------------------------------------------------------

-- | dfs g vs: a spanning forest of what the vertices reach, searched from
-- each in order, a vertex in the first tree that reaches it
dfs :: IntMap [Int] -> [Int] -> [Tree Int]
dfs g vs = fst (dfsGo g vs IntSet.empty)

dfsGo :: IntMap [Int] -> [Int] -> IntSet -> ([Tree Int], IntSet)
dfsGo g [] seen = ([], seen)
dfsGo g (v : vs) seen
  | IntSet.member v seen = dfsGo g vs seen
  | otherwise = case dfsGo g (IntMap.findWithDefault [] v g) (IntSet.insert v seen) of
      (as, seen1) -> case dfsGo g vs seen1 of
        (bs, seen2) -> (Node v as : bs, seen2)

dff :: IntMap [Int] -> [Tree Int]
dff g = dfs g (vertices g)

-- | postorder (Node a ts) = postorderF ts . (a :)
postorder :: Tree Int -> [Int] -> [Int]
postorder (Node a ts) xs = postorderF ts (a : xs)

-- | postorderF ts = foldr (.) id (map postorder ts)
postorderF :: [Tree Int] -> [Int] -> [Int]
postorderF [] xs = xs
postorderF (t : ts) xs = postorder t (postorderF ts xs)

postOrd :: IntMap [Int] -> [Int]
postOrd g = postorderF (dff g) []

-- | the connected components, the edges read in both directions
components :: IntMap [Int] -> [Tree Int]
components g = dff (undirected g)

-- | the strongly connected components, in reverse topological order
scc :: IntMap [Int] -> [Tree Int]
scc g = dfs g (reverse (postOrd (transposeG g)))

-- Strongly connected components ---------------------------------------------

-- | the strongly connected components of the nodes, reverse topologically
-- sorted (Data.Graph's stronglyConnComp: stronglyConnCompR's, each node's
-- own part)
stronglyConnComp :: forall key node. Ord key => [(node, key, [key])] -> [SCC node]
stronglyConnComp edges0 = sccNodes (stronglyConnCompR edges0)

sccNodes :: forall node key. [SCC (node, key, [key])] -> [SCC node]
sccNodes [] = []
sccNodes (c : cs) = sccNode c : sccNodes cs

sccNode :: forall node key. SCC (node, key, [key]) -> SCC node
sccNode (AcyclicSCC (n, _, _)) = AcyclicSCC n
sccNode (CyclicSCC ts) = CyclicSCC (firsts ts)

firsts :: forall node key. [(node, key, [key])] -> [node]
firsts [] = []
firsts ((n, _, _) : ts) = n : firsts ts

stronglyConnCompR :: forall key node. Ord key => [(node, key, [key])] -> [SCC (node, key, [key])]
stronglyConnCompR [] = []
stronglyConnCompR edges0 = sccOfNumbered (number (sortNodes edges0) 0)

sccOfNumbered :: forall node key. Ord key => [(Int, (node, key, [key]))] -> [SCC (node, key, [key])]
sccOfNumbered ns = decodeAll (graphOf (keysOf ns) ns) (IntMap.fromList ns) (scc (graphOf (keysOf ns) ns))

decodeAll :: forall n. IntMap [Int] -> IntMap n -> [Tree Int] -> [SCC n]
decodeAll g m [] = []
decodeAll g m (t : ts) = decode g m t : decodeAll g m ts

-- | a tree of the search: a vertex alone (on a cycle only if it is its own
-- successor) or a cycle, its vertices in the tree's pre-order
decode :: forall n. IntMap [Int] -> IntMap n -> Tree Int -> SCC n
decode g m (Node v []) =
  if elemInt v (IntMap.findWithDefault [] v g) then CyclicSCC [m IntMap.! v] else AcyclicSCC (m IntMap.! v)
decode g m (Node v ts) = CyclicSCC ((m IntMap.! v) : decF m ts [])

-- | foldr dec vs ts, dec (Node v ts) vs = vertex v : foldr dec vs ts
decF :: forall n. IntMap n -> [Tree Int] -> [n] -> [n]
decF m [] vs = vs
decF m (Node v ts : rest) vs = (m IntMap.! v) : decF m ts (decF m rest vs)

elemInt :: Int -> [Int] -> Bool
elemInt x [] = False
elemInt x (y : ys) = x == y || elemInt x ys
