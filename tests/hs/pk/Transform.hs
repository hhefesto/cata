-- Machine's transformNoDefer and stuckStep: a where's functions that call
-- each other through fmap and the def's own function, at a function that
-- calls the def back
{-# LANGUAGE LambdaCase, DeriveFunctor #-}
module Transform where

import Data.Fix (Fix (..))

data F r = Zero | Pair r r | Env | Defer Int r | Set r
  deriving (Eq, Show, Functor)

type E = Fix F

transformND :: (F E -> E) -> E -> E
transformND f = c where
  c = f . c' . unFix
  c' = \case
    s@(Defer _ _) -> s
    x             -> fmap c x

step :: (F E -> E) -> F E -> E
step other = \case
  Set (Fix (Pair (Fix (Defer _ d)) e)) -> transformND (step other . repl) d where
    e' = unFix e
    repl = \case
      Env -> e'
      x   -> x
  x -> other x

eval :: E -> E
eval = transformND (step Fix)

size :: E -> Int
size (Fix x) = case x of
  Zero -> 1
  Pair a b -> size a + size b
  Env -> 5
  Defer n a -> n + size a
  Set a -> 10 + size a

zero, env :: E
zero = Fix Zero
env = Fix Env

pair :: E -> E -> E
pair a b = Fix (Pair a b)

call :: Int -> E -> E -> E
call n body arg = Fix (Set (pair (Fix (Defer n body)) arg))

exEval :: Int -> Int
exEval n = size (eval (call n (pair env (call 1 env env)) (pair zero (Fix (Defer n env)))))
