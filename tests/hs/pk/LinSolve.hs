module LinSolve where

import Control.Monad (foldM, unless, void)
import Data.Bifunctor (first)
import qualified Data.Graph as Graph
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (minimumBy, partition, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import qualified Data.Tree as Tree

-- telomare's exact linear solving (EAL.hs): simplex over Rational, its
-- lookups partial (!), a division by zero GHC's
data EqR = EqR { eqLhs :: [Int], eqRhs :: Int, eqNote :: String } deriving (Eq, Show)

data Row = Row
  { rowCoefs :: IntMap Rational
  , rowConst :: Rational
  , rowIsEq  :: Bool
  , rowFrom  :: [EqR]
  }

-- | A variable eliminated from the system: @y_v = max 0 ((const - sum
-- coefs*y) / k)@, where the max only matters for a variable whose row
-- was already an inequality.
data Elim = Elim
  { elVar   :: Int
  , elCoefs :: IntMap Rational
  , elConst :: Rational
  , elK     :: Rational
  }

-- | Solve the live equations over naturals with the given lower bounds.
-- Returns the value of every variable mentioned, or the equations of an
-- inconsistent subsystem.
solveLinear :: (Int -> Int) -> (Int -> Integer) -> [EqR] -> Either [EqR] (Map Int Int)
solveLinear lb weight eqs = do
  let rows0 = IntMap.fromList (zip [0 ..] (fmap toRow eqs))
      (rows1, elims) = eliminate (const True) rows0
      (trivial, residual0) = IntMap.partition (IntMap.null . rowCoefs) rows1
      -- an inequality every nonnegative assignment satisfies (nonpositive
      -- coefficients, nonnegative constant) says nothing
      residual = IntMap.filter (not . vacuous) residual0
      violated = concat [ rowFrom r | r <- IntMap.elems trivial, not (trivialOk r) ]
  unless (null violated) $ Left violated
  -- the residual splits into connected components; one that the all-zero
  -- assignment satisfies needs no simplex (zero is also optimal, every
  -- weight being positive), and the rest are solved separately
  ys <- IntMap.unions <$> mapM (simplexSolve weight)
    [ comp | comp <- components residual, not (all zeroSatisfies (IntMap.elems comp)) ]
  -- elims holds the last elimination first; it depends only on
  -- variables still in the residual, so substitute in that order
  let ysAll = foldl (flip backSubstitute) ys elims
      vars = Set.toList . Set.fromList $ concatMap (\e -> eqRhs e : eqLhs e) eqs
      xs = [ (v, fromIntegral (lb v) + IntMap.findWithDefault 0 v ysAll) | v <- vars ]
      scale = foldr (lcm . denominator . snd) 1 xs :: Integer
  pure $ Map.fromList
    [ (v, fromInteger (numerator (x * fromInteger scale))) | (v, x) <- xs ]
  where
    toRow e@(EqR lhs rhs _) = Row
      { rowCoefs = IntMap.filter (/= 0) $ IntMap.fromListWith (+)
          ([ (l, 1) | l <- lhs ] <> [ (rhs, -1) ])
      , rowConst = fromIntegral (lb rhs) - sum (fmap (fromIntegral . lb) lhs)
      , rowIsEq = True
      , rowFrom = [e]
      }
    trivialOk r
      | rowIsEq r = rowConst r == 0
      | otherwise = rowConst r >= 0
    zeroSatisfies = trivialOk
    vacuous r = not (rowIsEq r) && rowConst r >= 0 && all (<= 0) (IntMap.elems (rowCoefs r))
    backSubstitute (Elim v coefs c k) ys =
      let s = sum [ a * IntMap.findWithDefault 0 u ys | (u, a) <- IntMap.toList coefs ]
      in IntMap.insert v (max 0 ((c - s) / k)) ys

-- | Sparse Gaussian elimination that keeps nonnegativity: every variable
-- occurring in some equality is solved for from one of them (the
-- shortest), substituted into every other row it occurs in, and the
-- solving row becomes the inequality @y_v >= 0@ over the rest. Variables
-- with the fewest occurrences go first to limit fill-in. Afterwards no
-- equality has a variable left, so the residual is a system of
-- inequalities over the free variables only. Each step removes one
-- variable from the system, so this terminates.
eliminate :: (Int -> Bool) -> IntMap Row -> (IntMap Row, [Elim])
eliminate eligible rows0 = passes rows0 (occurrences rows0) [] where
  occurrences rows = IntMap.fromListWith IntSet.union
    [ (v, IntSet.singleton i) | (i, r) <- IntMap.toList rows
    , v <- IntMap.keys (rowCoefs r) ]
  passes rows occ elims =
    let candidates = sortOn snd
          [ (v, IntSet.size is) | (v, is) <- IntMap.toList occ, eligible v
          , any (\i -> maybe False rowIsEq (IntMap.lookup i rows)) (IntSet.toList is) ]
    in if null candidates
      then (rows, elims)
      else let (rows', occ', elims') = foldl step (rows, occ, elims) (fmap fst candidates)
           in passes rows' occ' elims'
  step (rows, occ, elims) v =
    let is = IntSet.toList (IntMap.findWithDefault IntSet.empty v occ)
        eqRows = [ (i, r) | i <- is, Just r <- [IntMap.lookup i rows], rowIsEq r
                 , IntMap.member v (rowCoefs r) ]
    in case sortOn (IntMap.size . rowCoefs . snd) eqRows of
      [] -> (rows, occ, elims)
      ((i, r) : _) ->
        let k = rowCoefs r IntMap.! v
            rest = IntMap.delete v (rowCoefs r)
            c = rowConst r
            pivotRow = if k > 0
              then r { rowCoefs = rest, rowIsEq = False }
              else r { rowCoefs = IntMap.map negate rest, rowConst = negate c
                     , rowIsEq = False }
            substitute (rs, oc) j = case IntMap.lookup j rs of
              Just rj | Just a <- IntMap.lookup v (rowCoefs rj) ->
                let f = a / k
                    coefs' = IntMap.filter (/= 0) $ IntMap.unionWith (+)
                      (IntMap.delete v (rowCoefs rj)) (IntMap.map (negate . (f *)) rest)
                    rj' = rj { rowCoefs = coefs', rowConst = rowConst rj - f * c
                             , rowFrom = rowFrom rj <> rowFrom r }
                    gone = IntMap.keys (IntMap.difference (rowCoefs rj) coefs')
                    new = IntMap.keys (IntMap.difference coefs' (rowCoefs rj))
                    oc' = foldr (IntMap.insertWith IntSet.union `flip` IntSet.singleton j)
                            (foldr (IntMap.adjust (IntSet.delete j)) oc gone) new
                in (IntMap.insert j rj' rs, oc')
              _unchanged -> (rs, oc)
            (rows1, occ1) = foldl substitute (rows, occ) (filter (/= i) is)
            rows2 = IntMap.insert i pivotRow rows1
            occ2 = IntMap.delete v occ1
        in (rows2, occ2, Elim v rest c k : elims)

-- | Values of the residual system's variables from a two-phase exact
-- simplex: phase one finds a feasible vertex or names the rows that
-- cannot hold together, phase two minimizes the weighted sum of the
-- variables.
simplexSolve :: (Int -> Integer) -> IntMap Row -> Either [EqR] (IntMap Rational)
simplexSolve weight rows
  | IntMap.null rows = Right IntMap.empty
  | not (any rowIsEq (IntMap.elems rows)) = dualSolve weight rows
  | otherwise =
      let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
          nVars = length vars
          colOf = IntMap.fromList (zip vars [0 ..])
          varOf = IntMap.fromList (zip [0 ..] vars)
          rowList = zip [0 ..] (IntMap.elems rows)
          rowByIndex = IntMap.fromList rowList
          nRows = length rowList
          slackBase = nVars
          artBase = nVars + nRows
          -- row i: coefs over var columns (+ slack column for an
          -- inequality), rhs made nonnegative. An inequality with a
          -- nonnegative constant starts from its slack; only the other
          -- rows get an artificial column artBase+i, so phase one is as
          -- small as the lower bounds make it
          build (i, r) =
            let base = IntMap.fromList [ (colOf IntMap.! v, a) | (v, a) <- IntMap.toList (rowCoefs r) ]
                withSlack = if rowIsEq r then base else IntMap.insert (slackBase + i) 1 base
                (coefs, b) = if rowConst r >= 0
                  then (withSlack, rowConst r)
                  else (IntMap.map negate withSlack, negate (rowConst r))
                slackStarts = not (rowIsEq r) && rowConst r >= 0
            in if slackStarts
              then (i, ((coefs, b), slackBase + i))
              else (i, ((IntMap.insert (artBase + i) 1 coefs, b), artBase + i))
          built = fmap build rowList
          tRows = IntMap.fromList [ (i, rb) | (i, (rb, _)) <- built ]
          basis0 = IntMap.fromList [ (i, c) | (i, (_, c)) <- built ]
          artRowsInit = [ i | (i, (_, c)) <- built, c >= artBase ]
          obj1 = IntMap.filter (/= 0) . IntMap.unionsWith (+) $
            [ IntMap.map negate (IntMap.filterWithKey (\c _ -> c < artBase) coefs)
            | i <- artRowsInit, let (coefs, _) = tRows IntMap.! i ]
          phase1 = if null artRowsInit
            then mkTab tRows basis0 IntMap.empty
            else runSimplex (mkTab tRows basis0 obj1)
          blamed = concat
            [ rowFrom (rowByIndex IntMap.! i)
            | (i, (_, b)) <- IntMap.toList (tbRows phase1)
            , tbBasis phase1 IntMap.! i >= artBase, b > 0 ]
      in if not (null blamed)
        then Left blamed
        else
          let cleaned = dropArtificials artBase phase1
              cost c = if c < slackBase then fromInteger (weight (varOf IntMap.! c)) else 0 :: Rational
              obj2 = IntMap.filter (/= 0) . IntMap.unionsWith (+) $
                IntMap.fromList [ (c, cost c) | c <- [0 .. artBase - 1] ]
                  : [ IntMap.map (negate . (cost (tbBasis cleaned IntMap.! i) *)) coefs
                    | (i, (coefs, _)) <- IntMap.toList (tbRows cleaned)
                    , cost (tbBasis cleaned IntMap.! i) /= 0 ]
              obj2' = foldr IntMap.delete obj2 (IntMap.elems (tbBasis cleaned))
              phase2 = runSimplex cleaned { tbObj = obj2' }
              values = IntMap.fromList
                [ (varOf IntMap.! c, b)
                | (i, (_, b)) <- IntMap.toList (tbRows phase2)
                , let c = tbBasis phase2 IntMap.! i, c < slackBase ]
          in Right values

data Tab = Tab
  { tbRows  :: IntMap (IntMap Rational, Rational) -- ^ row: coefficients by column, rhs
  , tbBasis :: IntMap Int                         -- ^ row: its basic column
  , tbObj   :: IntMap Rational                    -- ^ reduced costs of nonbasic columns
  , tbCols  :: IntMap IntSet                      -- ^ column: the rows with a nonzero
                                                  --   entry in it (the sparse column
                                                  --   index a pivot walks)
  , tbNeg   :: IntSet                             -- ^ rows whose rhs is negative
  }

-- | A tableau with its indices built from the rows.
mkTab :: IntMap (IntMap Rational, Rational) -> IntMap Int -> IntMap Rational -> Tab
mkTab rows basis obj = Tab rows basis obj cols neg where
  cols = IntMap.fromListWith IntSet.union
    [ (c, IntSet.singleton i) | (i, (row, _)) <- IntMap.toList rows, c <- IntMap.keys row ]
  neg = IntMap.keysSet (IntMap.filter ((< 0) . snd) rows)

-- | Remove a row, keeping the indices consistent.
deleteRow :: Int -> Tab -> Tab
deleteRow i tab = case IntMap.lookup i (tbRows tab) of
  Nothing -> tab
  Just (row, _) -> tab
    { tbRows = IntMap.delete i (tbRows tab)
    , tbBasis = IntMap.delete i (tbBasis tab)
    , tbCols = foldr (IntMap.adjust (IntSet.delete i)) (tbCols tab) (IntMap.keys row)
    , tbNeg = IntSet.delete i (tbNeg tab)
    }

-- | Pivot row @r@ on column @c@. Only the rows with a nonzero entry in
-- column @c@ change, and the column index says which those are, so a
-- pivot costs the column's density times the pivot row's length rather
-- than a pass over the whole tableau.
pivot :: Int -> Int -> Tab -> Tab
pivot r c (Tab rows basis obj cols neg) =
  let (prow, pb) = rows IntMap.! r
      p = prow IntMap.! c
      prow' = IntMap.map (/ p) prow
      pb' = pb / p
      -- row - a*prow', dropping what cancels; rows hold no zeros, so
      -- only the overlap can cancel
      combine a row = IntMap.mergeWithKey
        (\_ x y -> let z = subMul x a y in if z == 0 then Nothing else Just z)
        id (IntMap.map (negate . (a *))) row prow'
      -- the column index is a superset: an entry that cancelled to zero,
      -- or a row since deleted, stays listed and is skipped here, which is
      -- cheaper than keeping the index exact
      affected = IntSet.filter
        (\j -> j /= r && maybe False (IntMap.member c . fst) (IntMap.lookup j rows))
        (IntMap.findWithDefault IntSet.empty c cols)
      step (rs, ng) j =
        let (row, b) = rs IntMap.! j
            a = row IntMap.! c
            row' = combine a row
            b' = subMul b a pb'
            ng' = if b' < 0 then IntSet.insert j ng else IntSet.delete j ng
        in (IntMap.insert j (row', b') rs, ng')
      (rows1, neg1) = IntSet.foldl' step (rows, neg) affected
      -- every affected row now has an entry in each column of the pivot
      -- row (but where it cancelled), so those columns take the affected
      -- rows as a set; column c is nonzero in row r alone
      cols' = IntMap.insert c (IntSet.singleton r) $ IntMap.unionWith IntSet.union cols
        (IntMap.fromSet (const affected) (IntSet.delete c (IntMap.keysSet prow')))
      rows' = IntMap.insert r (prow', pb') rows1
      neg' = if pb' < 0 then IntSet.insert r neg1 else IntSet.delete r neg1
      obj' = maybe obj (`combine` obj) (IntMap.lookup c obj)
  in Tab rows' (IntMap.insert r c basis) obj' cols' neg'

-- | @x - a*y@, on the integers when all three are (nearly always: the
-- coefficients stay small integers), which skips 'Rational''s gcds.
subMul :: Rational -> Rational -> Rational -> Rational
subMul x a y
  | denominator x == 1 && denominator a == 1 && denominator y == 1 =
      fromInteger (numerator x - numerator a * numerator y)
  | otherwise = x - a * y

-- | Minimize. Pricing is Dantzig.s (the most negative reduced cost
-- enters) while pivots are non-degenerate, and Bland.s (the
-- lowest-numbered improving column enters, the minimum-ratio row with the
-- lowest-numbered basic column leaves) after a degenerate pivot. Every
-- non-degenerate pivot lowers an objective bounded below over finitely
-- many vertices, and a run of degenerate pivots under Bland.s rule cannot
-- cycle, so this terminates.
runSimplex :: Tab -> Tab
runSimplex = go False where
  go bland tab = case entering of
    Nothing -> tab
    Just c -> case leaving c of
      Nothing              -> tab -- unbounded: impossible for a nonnegative objective
      Just (r, degenerate) -> go degenerate (pivot r c tab)
    where
      improving = filter ((< 0) . snd) (IntMap.toAscList (tbObj tab))
      entering = case improving of
        []                  -> Nothing
        (first : _) | bland -> Just (fst first)
        _                   -> Just (fst (minimumBy (comparing snd) improving))
      leaving c =
        let candidates = [ (b / a, tbBasis tab IntMap.! i, i)
                         | i <- IntSet.toList (IntMap.findWithDefault IntSet.empty c (tbCols tab))
                         , Just (row, b) <- [IntMap.lookup i (tbRows tab)]
                         , Just a <- [IntMap.lookup c row], a > 0 ]
        in case candidates of
          [] -> Nothing
          _  -> let (ratio, _, i) = minimum candidates in Just (i, ratio == 0)

-- | After phase one, pivot every artificial column out of the basis (its
-- value is zero, so any nonzero entry of a real column will do) or drop
-- the row if it has none (it was redundant), then forget the artificial
-- columns.
dropArtificials :: Int -> Tab -> Tab
dropArtificials artBase tab0 =
  let tab1 = foldr step tab0 (IntMap.toList (tbBasis tab0))
      step (i, c) tab
        | c < artBase = tab
        | otherwise = case IntMap.lookup i (tbRows tab) of
            Nothing -> tab
            Just (row, _) ->
              case [ j | (j, a) <- IntMap.toAscList row, j < artBase, a /= 0 ] of
                (j : _) -> pivot i j tab
                []      -> deleteRow i tab
      strip = IntMap.filterWithKey (\c _ -> c < artBase)
  in mkTab (IntMap.map (first strip) (tbRows tab1)) (tbBasis tab1)
       (strip (tbObj tab1))

components :: IntMap Row -> [IntMap Row]
components rows =
  let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
      -- a bipartite graph of rows and variables; 'Graph.components'
      -- reads it undirected, so one direction of edge is enough
      rowNodes = [ ((), (0 :: Int, i), [ (1, v) | v <- IntMap.keys (rowCoefs r) ])
                 | (i, r) <- IntMap.toList rows, not (IntMap.null (rowCoefs r)) ]
      varNodes = [ ((), (1, v), []) | v <- vars ]
      (g, nodeFromVertex, _) = Graph.graphFromEdges (rowNodes <> varNodes)
      keyOf v = let (_, k, _) = nodeFromVertex v in k
      rowsOf t = IntMap.fromList
        [ (i, rows IntMap.! i) | (0, i) <- fmap keyOf (Tree.flatten t) ]
  in filter (not . IntMap.null) (fmap rowsOf (Graph.components g))

dualSolve :: (Int -> Integer) -> IntMap Row -> Either [EqR] (IntMap Rational)
dualSolve weight rows =
  let vars = IntSet.toList . IntSet.unions $ fmap (IntMap.keysSet . rowCoefs) (IntMap.elems rows)
      colOf = IntMap.fromList (zip vars [0 ..])
      varOf = IntMap.fromList (zip [0 ..] vars)
      rowList = zip [0 ..] (IntMap.elems rows)
      rowByIndex = IntMap.fromList rowList
      slackBase = length vars
      coefsOf r = IntMap.fromList
        [ (colOf IntMap.! v, a) | (v, a) <- IntMap.toList (rowCoefs r) ]
      build (i, r) = (i, (IntMap.insert (slackBase + i) 1 (coefsOf r), rowConst r))
      (active0, waiting0) = partition (\(_, r) -> rowConst r < 0) rowList
      tRows = IntMap.fromList (fmap build active0)
      basis0 = IntMap.fromList [ (i, slackBase + i) | (i, _) <- active0 ]
      obj0 = IntMap.fromList [ (colOf IntMap.! v, fromInteger (weight v)) | v <- vars ]
      -- the argument counts the degenerate pivots in a row
      go :: Int -> Tab -> Either [EqR] Tab
      go degenerate tab
        | IntSet.null (tbNeg tab) = Right tab
        | otherwise =
            let infeasible = IntMap.restrictKeys (tbBasis tab) (tbNeg tab)
                r | degenerate >= blandAfter = snd $ IntMap.foldlWithKey'
                      (\acc i c -> if c < fst acc then (c, i) else acc)
                      (maxBound, -1) infeasible
                  | otherwise = (\(_, _, i) -> i) $ IntMap.foldlWithKey'
                      (\acc i c -> min acc (IntMap.size (fst (tbRows tab IntMap.! i)), c, i))
                      (maxBound, maxBound, -1) infeasible
                (row, _) = tbRows tab IntMap.! r
                candidates =
                  [ (IntMap.findWithDefault 0 j (tbObj tab) / negate a, j)
                  | (j, a) <- IntMap.toList row, a < 0 ]
            in case candidates of
                 [] -> Left (rowFrom (rowByIndex IntMap.! r))
                 _  -> let (ratio, c) = minimum candidates
                       in go (if ratio == 0 then degenerate + 1 else 0) (pivot r c tab)
      -- the current point: basic structural columns carry their row's
      -- rhs, every other column is zero
      pointOf tab = IntMap.fromList
        [ (c, b) | (i, (_, b)) <- IntMap.toList (tbRows tab)
        , let c = tbBasis tab IntMap.! i, c < slackBase ]
      -- a waiting row over the current nonbasic columns: substitute every
      -- basic structural column by its tableau row
      -- the structural basic columns' rows: built once per batch, since an
      -- added row's basic column is its own slack
      rowsOfBasics tab = IntMap.fromList
        [ (c, ri) | (ri, c) <- IntMap.toList (tbBasis tab), c < slackBase ]
      addRow rowOfCol tab (i, r) =
        let coefs0 = coefsOf r
            substitute (cs, b) (j, a) = case IntMap.lookup j rowOfCol of
              Nothing -> (cs, b)
              Just ri ->
                let (prow, pb) = tbRows tab IntMap.! ri
                in ( IntMap.filter (/= 0) $
                       IntMap.unionWith (+) cs (IntMap.map (negate . (a *)) prow)
                   , b - a * pb )
            (coefs, b') = foldl substitute (coefs0, rowConst r)
                            (IntMap.toList coefs0)
            coefs' = IntMap.insert (slackBase + i) 1 coefs
        in tab { tbRows = IntMap.insert i (coefs', b') (tbRows tab)
               , tbBasis = IntMap.insert i (slackBase + i) (tbBasis tab)
               , tbCols = foldr (\k -> IntMap.insertWith IntSet.union k (IntSet.singleton i))
                            (tbCols tab) (IntMap.keys coefs')
               , tbNeg = if b' < 0 then IntSet.insert i (tbNeg tab) else tbNeg tab }
      -- every row by the columns it mentions (any row can wait: a deleted
      -- one waits again)
      waitingAt = IntMap.fromListWith IntSet.union
        [ (colOf IntMap.! v, IntSet.singleton i)
        | (i, r) <- rowList, v <- IntMap.keys (rowCoefs r) ]
      -- a waiting row held at the last point, so it can fail at this one
      -- only if one of its columns moved (the first point's predecessor is
      -- zero, which every waiting row holds at: its constant is nonnegative)
      moved p0 p1 = IntMap.keysSet $ IntMap.mergeWithKey
        (\_ x y -> if x /= y then Just () else Nothing)
        (void . IntMap.filter (/= 0)) (void . IntMap.filter (/= 0)) p0 p1
      objectiveAt point = sum
        [ fromInteger (weight (varOf IntMap.! c)) * b | (c, b) <- IntMap.toList point ]
      loop tab prev waitSet lastDeletion = do
        tab' <- go 0 tab
        let point = pointOf tab'
            value r = sum [ a * IntMap.findWithDefault 0 (colOf IntMap.! v) point
                          | (v, a) <- IntMap.toList (rowCoefs r) ]
            suspects = IntSet.intersection waitSet . IntSet.unions $
              [ IntMap.findWithDefault IntSet.empty c waitingAt
              | c <- IntSet.toList (moved prev point) ]
            violated = [ (i, r) | i <- IntSet.toAscList suspects
                       , let r = rowByIndex IntMap.! i, value r > rowConst r ]
            waiting' = IntSet.difference waitSet (IntSet.fromList (fmap fst violated))
            objective = objectiveAt point
            deleting = objective > lastDeletion
            idle = [ i | deleting, (i, c) <- IntMap.toList (tbBasis tab'), c == slackBase + i ]
            kept = foldr deleteRow tab' idle
        if null violated
          then pure tab'
          else loop (foldl (addRow (rowsOfBasics kept)) kept violated) point
                 (IntSet.union waiting' (IntSet.fromList idle))
                 (if deleting then objective else lastDeletion)
  in do
    tab <- loop (mkTab tRows basis0 obj0) IntMap.empty
      (IntSet.fromList (fmap fst waiting0)) (-1)
    pure $ IntMap.fromList
      [ (varOf IntMap.! c, b)
      | (i, (_, b)) <- IntMap.toList (tbRows tab)
      , let c = tbBasis tab IntMap.! i, c < slackBase ]

-- | How many degenerate pivots in a row 'dualSolve' makes by its own rule
-- before it falls back to Bland's.
blandAfter :: Int
blandAfter = 1000

solve :: [(Int, Integer)] -> [([Int], Int)] -> Either [([Int], Int)] [(Int, Int)]
solve ws es = either (Left . map (\e -> (eqLhs e, eqRhs e))) (Right . Map.toList)
  (solveLinear (\v -> Map.findWithDefault 0 v lbs) (\v -> 1 + abs (Map.findWithDefault 1 v wm)) [ EqR (map abs l) (abs r) "" | (l, r) <- es ])
  where
    wm = Map.fromList ws
    lbs = Map.fromList [ (k, fromIntegral (abs w) `mod` 3) | (k, w) <- ws ]
