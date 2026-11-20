{-# LANGUAGE LambdaCase, DeriveTraversable #-}
module RecV where

-- cata's rule 12 test: recursion through a function value, as telomare
-- writes it (a def passed to >>=, maybe, foldMap, any, fmap, mapM)

import Control.Comonad.Cofree (Cofree (..))
import Control.Monad (when)
import Control.Monad.State (State, evalState, gets, modify)
import qualified Data.Map as Map

data Loc = Src Int Int | Gen Int (Maybe Loc) | NoLoc
  deriving (Eq, Show)

-- IR.Loc's locStartLineColumn: the parent through >>= at Maybe
startOf :: Loc -> Maybe (Int, Int)
startOf = \case
  Src l c -> Just (l, c)
  Gen _ parent -> parent >>= startOf
  NoLoc -> Nothing

mkLoc :: [Int] -> Loc
mkLoc [] = NoLoc
mkLoc [x] = Src x (x + 1)
mkLoc (x : xs) = Gen x (if x > 0 then Just (mkLoc xs) else Nothing)

startOfList :: [Int] -> Maybe (Int, Int)
startOfList xs = startOf (mkLoc xs)

data TF f = Leaf Int | Ref Int | Node f f | Many [f]
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Cofree TF Int

mkT :: [Int] -> T
mkT [] = 0 :< Leaf 0
mkT [x] = x :< Ref x
mkT (x : y : rest)
  | x > y = x :< Node (y :< Leaf y) (mkT rest)
  | otherwise = y :< Many [x :< Leaf x, mkT rest]

-- EAL's refsOf: foldMap of itself over the functor
refsOf :: T -> [Int]
refsOf (_ :< t) = case t of
  Ref h -> [h]
  x -> foldMap refsOf x

refsOfList :: [Int] -> [Int]
refsOfList xs = refsOf (mkT xs)

-- EAL's unsizedIn: any of a local go, a map's lookup
hasRef :: Map.Map Int T -> T -> Bool
hasRef bodies = go where
  go (_ :< t) = case t of
    Leaf n -> n < 0
    Ref h -> maybe False go (Map.lookup h bodies)
    x -> any go x

hasRefList :: [Int] -> Bool
hasRefList xs = hasRef (Map.fromList [(1, 1 :< Leaf (-1))]) (mkT xs)

-- Fast's positionsIn: a tag through maybe id (:), foldMap of itself
tagsOf :: T -> [Int]
tagsOf (tag :< term) = maybe id (:) (if tag > 0 then Just tag else Nothing) (foldMap tagsOf term)

tagsOfList :: [Int] -> [Int]
tagsOfList xs = tagsOf (mkT xs)

-- fmap of itself over the functor
double :: T -> T
double (tag :< term) = (tag * 2) :< fmap double term

doubleList :: [Int] -> [Int]
doubleList xs = tagsOf (double (mkT xs))

-- EAL's walkTau: maybe (pure t) walk in State
walk :: Int -> State (Map.Map Int Int) Int
walk i = gets (Map.lookup i) >>= maybe (pure i) walk

walkList :: [Int] -> Int
walkList xs = evalState (walk 0) (Map.fromList [ (i, i + 1 + abs v) | (i, v) <- zip [0 ..] xs ])

-- EAL's presolve: a monadic value that runs again while it changes
settle :: State Int ()
settle = do
  n <- gets id
  when (n > 1) (modify (`div` 2) >> settle)

settleList :: [Int] -> Int
settleList xs = evalState (settle >> gets id) (sum (map abs xs))
