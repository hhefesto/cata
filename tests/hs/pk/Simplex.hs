module Simplex where

import Data.Bifunctor (first)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (minimumBy, partition, sortOn)
import Data.Ord (comparing)

data EqR = EqR
  { eqLhs   :: [Int]
  , eqRhs   :: Int
  } deriving (Eq, Show)

data Row = Row
  { rowCoefs :: IntMap Rational
  , rowConst :: Rational
  , rowIsEq  :: Bool
  , rowFrom  :: [EqR]
  }

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
      combine a row = IntMap.filter (/= 0) $
        IntMap.unionWith (+) row (IntMap.map (negate . (a *)) prow')
      -- the column index is a superset: an entry that cancelled to zero
      -- stays listed and is skipped here, which is cheaper than keeping
      -- the index exact
      affected = [ j | j <- IntSet.toList (IntMap.findWithDefault IntSet.empty c cols)
                 , j /= r, IntMap.member c (fst (rows IntMap.! j)) ]
      step (rs, cs, ng) j =
        let (row, b) = rs IntMap.! j
            a = row IntMap.! c
            row' = combine a row
            b' = b - a * pb'
            new = IntMap.keys (IntMap.difference prow' row)
            cs' = foldr (\k -> IntMap.insertWith IntSet.union k (IntSet.singleton j)) cs new
            ng' = if b' < 0 then IntSet.insert j ng else IntSet.delete j ng
        in (IntMap.insert j (row', b') rs, cs', ng')
      (rows1, cols1, neg1) = foldl step (rows, cols, neg) affected
      -- scaling the pivot row changes no sparsity pattern; afterwards
      -- column c is nonzero in row r alone
      rows' = IntMap.insert r (prow', pb') rows1
      cols' = cols1
      neg' = if pb' < 0 then IntSet.insert r neg1 else IntSet.delete r neg1
      obj' = maybe obj (`combine` obj) (IntMap.lookup c obj)
  in Tab rows' (IntMap.insert r c basis) obj' cols' neg'

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
      go tab =
        case IntSet.toList (tbNeg tab) of
          [] -> Right tab
          infeasible ->
            let r = minimumBy (comparing (tbBasis tab IntMap.!)) infeasible
                (row, _) = tbRows tab IntMap.! r
                candidates =
                  [ (IntMap.findWithDefault 0 j (tbObj tab) / negate a, j)
                  | (j, a) <- IntMap.toList row, a < 0 ]
            in case candidates of
                 [] -> Left (rowFrom (rowByIndex IntMap.! r))
                 _  -> go (pivot r (snd (minimum candidates)) tab)
      -- the current point: basic structural columns carry their row's
      -- rhs, every other column is zero
      pointOf tab = IntMap.fromList
        [ (c, b) | (i, (_, b)) <- IntMap.toList (tbRows tab)
        , let c = tbBasis tab IntMap.! i, c < slackBase ]
      -- a waiting row over the current nonbasic columns: substitute every
      -- basic structural column by its tableau row
      addRow tab (i, r) =
        let rowOfCol = IntMap.fromList [ (c, ri) | (ri, c) <- IntMap.toList (tbBasis tab) ]
            coefs0 = coefsOf r
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
      loop tab waiting = do
        tab' <- go tab
        let point = pointOf tab'
            value r = sum [ a * IntMap.findWithDefault 0 (colOf IntMap.! v) point
                          | (v, a) <- IntMap.toList (rowCoefs r) ]
            (violated, waiting') = partition (\(_, r) -> value r > rowConst r) waiting
        if null violated
          then pure tab'
          else loop (foldl addRow tab' violated) waiting'
  in do
    tab <- loop (mkTab tRows basis0 obj0) waiting0
    pure $ IntMap.fromList
      [ (varOf IntMap.! c, b)
      | (i, (_, b)) <- IntMap.toList (tbRows tab)
      , let c = tbBasis tab IntMap.! i, c < slackBase ]


rowOf :: Bool -> Int -> [(Int, Int)] -> Int -> Row
rowOf e i cs k = Row { rowCoefs = IntMap.fromList [ (v, fromIntegral a) | (v, a) <- cs ], rowConst = fromIntegral k, rowIsEq = e, rowFrom = [EqR [i] k] }

exDual :: Int -> Int -> Either [EqR] [(Int, Rational)]
exDual a b = fmap IntMap.toList (dualSolve toInteger (IntMap.fromList [(0, rowOf False 0 [(1, 1), (2, -1)] a), (1, rowOf False 1 [(1, -1)] b)]))

exSimplex :: Int -> Int -> Either [EqR] [(Int, Rational)]
exSimplex a b = fmap IntMap.toList (simplexSolve toInteger (IntMap.fromList [(0, rowOf True 0 [(1, 1), (2, -1)] a), (1, rowOf False 1 [(1, -1)] b)]))
