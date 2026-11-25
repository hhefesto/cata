module MapMore where

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)

-- containers' and base's that telomare's EAL uses
sub :: Int -> IntMap Int -> IntMap Int -> IntMap Int
sub a p q = IntMap.mergeWithKey
  (\_ x y -> let z = x - a * y in if z == 0 then Nothing else Just z)
  id (IntMap.map (negate . (a *))) p q

least :: IntMap Int -> (Int, Int)
least m = IntMap.foldlWithKey' (\acc i c -> if c < fst acc then (c, i) else acc) (100, -1) m

apart :: Set Int -> Set Int -> Bool
apart = Set.disjoint

checked :: Map Int Int -> Either String (Map Int Int)
checked = Map.traverseWithKey (\k v -> if k > v then Left ("at " ++ show k) else Right (k + v))

keysOf :: Map Int (Set Int) -> Set Int
keysOf m = foldMap id m

joined :: [Map Int Int] -> Map Int Int
joined ms = mconcat ms

logged :: Int -> ([Int], Int)
logged n = do
  a <- ([n], n + 1)
  b <- ([a], a * 2)
  pure (a + b)
