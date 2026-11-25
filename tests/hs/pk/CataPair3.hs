module CataPair3 where

import CataB
import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import Data.Functor.Foldable (cata)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- CataPair's, its builder another module's, with an alternative that errs
-- (telomare's Resolve.splitExpr)
data F r = V Int | A r r | L r | Z | Ite r r r | Lf r | Bad Int | Cl r | Tok | Rec r r r | Ch Int
  deriving (Show, Eq)

instance Functor F where
  fmap _ (V n)       = V n
  fmap f (A x y)     = A (f x) (f y)
  fmap f (L x)       = L (f x)
  fmap _ Z           = Z
  fmap f (Ite x y z) = Ite (f x) (f y) (f z)
  fmap f (Lf x)      = Lf (f x)
  fmap _ (Bad n)     = Bad n
  fmap f (Cl x)      = Cl (f x)
  fmap _ Tok         = Tok
  fmap f (Rec x y z) = Rec (f x) (f y) (f z)
  fmap _ (Ch n)      = Ch n

type T = Cofree F Int

split :: T -> O
split t2 = flip State.evalState (0, 0) $ snd (cata f t2) unbound where
  unbound :: Int -> Int
  unbound n = error ("unbound " ++ show n)
  f :: C.CofreeF F Int (Set Int, (Int -> Int) -> B O) -> (Set Int, (Int -> Int) -> B O)
  f (anno C.:< g) =
    let tagged (frees, mk) = (frees, fmap (note anno) . mk)
        closed mk = (Set.empty, const mk)
        one (frees, mk) wrap = (frees, fmap wrap . mk)
        combine2 (fa, ma) (fb, mb) wrap = (fa <> fb, \ren -> wrap (ma ren) (mb ren))
        combine3 (fa, ma) (fb, mb) (fc, mc) wrap = (fa <> fb <> fc, \ren -> wrap (ma ren) (mb ren) (mc ren))
    in tagged $ case g of
      Z       -> closed $ pure ONil
      V n     -> (Set.singleton n, \ren -> pure . varP $ ren n)
      A a b   -> combine2 a b appS
      Ite i t e -> combine3 i t e $ \i' t' e' -> OIte <$> i' <*> t' <*> e'
      Lf x    -> one x OL
      Bad _   -> error "split: bad"
      Cl (_, mkBody) -> closed $ clamS (mkBody id)
      Ch n    -> closed $ church anno n
      Tok     -> closed $ do
        u <- State.gets snd
        State.modify (\(fi, _) -> (fi, u + 1))
        clamS (pure (OVar u))
      L (bodyFrees, mkBody) ->
        let outer = Set.toAscList . Set.map (subtract 1) $ Set.filter (>= 1) bodyFrees
            positions = Map.fromList $ zip outer [1 ..]
            bodyRen n
              | n == 0 = 0
              | otherwise = Map.findWithDefault (error ("lost " ++ show n)) (n - 1) positions
            capture :: (Int -> Int) -> B O
            capture ren = foldr (pairS . pure . varP . ren) (pure ONil) outer
        in (Set.fromList outer, pairS (mkBody bodyRen >>= deferS) . capture)

note :: Int -> O -> O
note k x = if k == 0 then x else OPair (OVar k) x
