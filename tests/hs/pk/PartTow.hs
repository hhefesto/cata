-- Machine's steps over a handler that errs (Size's refinementCheckStep,
-- getInputLimits): a partial function given to a def answering a function,
-- and through a tower of steps
{-# LANGUAGE LambdaCase, DeriveTraversable #-}
module PartTow where

import Control.Applicative (Applicative (..))
import Control.Monad ((<=<))
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.Functor.Identity (Identity (..))

data F r = Zero | Pair r r | Env | Defer Int r | Set r | Left1 r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type E = Fix F

transformND :: (F E -> E) -> E -> E
transformND f = c where
  c = f . c' . unFix
  c' = \case
    s@(Defer _ _) -> s
    x             -> fmap c x

basicStep :: (F E -> E) -> F E -> E
basicStep other = \case
  x@Zero -> Fix x
  x@(Pair _ _) -> Fix x
  x -> other x

stuckStep :: (F E -> E) -> F E -> E
stuckStep other = \case
  Set (Fix (Pair (Fix (Defer _ d)) e)) -> transformND (basicStep (stuckStep other) . repl) d where
    e' = unFix e
    repl = \case
      Env -> e'
      x   -> x
  Left1 (Fix (Pair a _)) -> a
  x@(Defer _ _) -> Fix x
  x -> other x

check :: F E -> E
check = basicStep (stuckStep other) where
  other x = error ("check: " ++ take 3 (show (size (Fix x))))

eval :: E -> E
eval = transformND check

-- the handler a parameter
evalWith :: (F E -> E) -> E -> E
evalWith h = transformND (basicStep (stuckStep h))

size :: E -> Int
size (Fix x) = case x of
  Zero -> 1
  Pair a b -> size a + size b
  Env -> 5
  Defer n a -> n + size a
  Set a -> 10 + size a
  Left1 a -> 3 + size a

zero, env :: E
zero = Fix Zero
env = Fix Env

pair :: E -> E -> E
pair a b = Fix (Pair a b)

call :: Int -> E -> E -> E
call n body arg = Fix (Set (pair (Fix (Defer n body)) arg))

exEval :: Int -> Int
exEval n = size (eval (call n (if n > 2 then pair env (call 1 env env) else Fix (Left1 zero)) (pair zero (Fix (Defer n env)))))

exWith :: Int -> Int
exWith n = size (evalWith (\x -> if n > 0 then Fix x else error "no handler") (call n (Fix (Left1 (if n > 3 then env else zero))) zero))

-- Size's refinementCheckStep: a tower of steps, some local, over a local
-- function written as a composition
abortStep :: (F E -> E) -> F E -> E
abortStep other = \case
  Left1 a@(Fix Zero) -> a
  Set (Fix (Pair (Fix Env) (Fix (Pair a _)))) -> (\x -> if size x > 100 then x else x) . Fix $ Defer 7 m where
    m = cata truncF a
    truncF = \case
      Pair x y -> Fix (Pair x y)
      _        -> Fix Zero
  x -> other x

tower :: F E -> E
tower = basicStep (stuckStep (abortStep (guardStep (gateStep other)))) where
  step = tower
  barrier = Fix . Defer 9
  gateStep other' = \case
    Left1 (Fix (Set (Fix (Pair l r)))) -> barrier (pair (step (Left1 l)) (step (Left1 r)))
    Set (Fix (Left1 e)) -> barrier . step $ Set e
    x -> other' x
  guardStep other' = \case
    Left1 (Fix (Left1 v)) -> guarded v . step $ Left1 v
    x -> other' x
  guarded c = \case
    a@(Fix Zero) -> a
    v -> barrier (pair c v)
  other = \case
    x@(Set (Fix Env)) -> barrier (Fix x)
    x -> error ("tower: " ++ show (size (Fix x)))

evalT :: E -> E
evalT = transformND tower

exTower :: Int -> Int
exTower n = size (evalT (if n > 3 then Fix (Left1 (Fix (Left1 (pair zero env)))) else if n > 1 then Fix (Set (pair env (pair zero zero))) else call n (Fix (Left1 zero)) zero))
