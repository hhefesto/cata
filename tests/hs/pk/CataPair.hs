module CataPair where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import Data.Functor.Foldable (cata)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- A cata whose answer is a pair that holds a function of a renaming (telomare's
-- Resolve.splitExpr): the free variables, and the term for where they are
data F r = V Int | A r r | L r | Z deriving (Show, Eq)

instance Functor F where
  fmap _ (V n)   = V n
  fmap f (A x y) = A (f x) (f y)
  fmap f (L x)   = L (f x)
  fmap _ Z       = Z

type T = Cofree F Int

data O = OVar Int | OApp O O | OClo Int O O | OPair O O | ONil deriving (Show, Eq)

type B a = State Int a

label :: O -> B O
label x = do
  n <- State.get
  State.put (n + 1)
  pure (OClo n x ONil)

pairB :: B O -> B O -> B O
pairB a b = do
  x <- a
  y <- b
  pure (OPair x y)

appB :: B O -> B O -> B O
appB a b = OApp <$> a <*> b

var :: Int -> O
var n = if n < 0 then error ("var " ++ show n) else OVar n

split :: T -> O
split t0 = flip State.evalState 0 $ snd (cata f t0) unbound where
  unbound :: Int -> Int
  unbound n = error ("unbound " ++ show n)
  f :: C.CofreeF F Int (Set Int, (Int -> Int) -> B O) -> (Set Int, (Int -> Int) -> B O)
  f (anno C.:< g) =
    let tagged (frees, mk) = (frees, fmap (note anno) . mk)
        closed mk = (Set.empty, const mk)
        two (fa, ma) (fb, mb) wrap = (fa <> fb, \ren -> wrap (ma ren) (mb ren))
    in tagged $ case g of
      Z     -> closed (pure ONil)
      V n   -> (Set.singleton n, \ren -> pure . var $ ren n)
      A a b -> two a b appB
      L (bodyFrees, mkBody) ->
        let outer = Set.toAscList . Set.map (subtract 1) $ Set.filter (>= 1) bodyFrees
            positions = Map.fromList $ zip outer [1 ..]
            bodyRen n
              | n == 0 = 0
              | otherwise = Map.findWithDefault (error ("lost " ++ show n)) (n - 1) positions
            capture :: (Int -> Int) -> B O
            capture ren = foldr (pairB . pure . var . ren) (pure ONil) outer
        in (Set.fromList outer, pairB (mkBody bodyRen >>= label) . capture)

note :: Int -> O -> O
note k x = if k == 0 then x else OPair (OVar k) x
