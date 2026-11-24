module PartAct where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map

-- | partial defs whose answer is an action: a monadic case that does not
-- cover (EAL's selfReferential), called in continuations
data T = Leaf Int | Two T T | Ref Int | Hole
  deriving (Eq, Show)

type M = ExceptT String (State (Map.Map Int T))

look :: Int -> M T
look i = do
  m <- get
  case Map.lookup i m of
    Nothing -> throwError "unbound"
    Just t -> pure t

-- Hole is not covered
size :: T -> M Int
size t = case t of
  Leaf _ -> pure 1
  Two a b -> do
    x <- size a
    y <- size b
    pure (x + y)
  Ref i -> look i >>= leafSize

leafSize :: T -> M Int
leafSize (Leaf n) = pure n
leafSize (Ref j) = fmap (+ 1) (look j >>= leafSize)

bindM :: Int -> T -> M ()
bindM i t = do
  n <- size t
  if n > 2
    then throwError "big"
    else modify (Map.insert i t)

run :: T -> Either String Int
run t = evalState (runExceptT (bindM 7 t >> size (Two t (Ref 7)))) (Map.fromList [(1, Leaf 4), (2, Ref 1)])

-- State alone
type S = State Int

tick :: T -> S Int
tick (Leaf n) = do
  k <- get
  put (k + n)
  pure k
tick (Two a b) = do
  x <- tick a
  y <- tick b
  pure (x + y)

runTick :: T -> (Int, Int)
runTick t = runState (tick t) 10

-- Either and Maybe: a partial call in a continuation
pick :: T -> Int
pick (Leaf n) = n
pick (Two a _) = pick a

viaEither :: T -> Either String Int
viaEither t = do
  u <- strip t
  pure (pick u + 1)

strip :: T -> Either String T
strip Hole = Left "hole"
strip t = Right t

viaMaybe :: Maybe T -> Maybe Int
viaMaybe m = do
  u <- m
  if pick u > 3 then Nothing else Just (pick u)

viaCase :: Maybe T -> Int
viaCase m = maybe 0 (\u -> pick u + 2) m
