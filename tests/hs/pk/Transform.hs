-- Machine's transformNoDefer and stuckStep: a where's functions that call
-- each other through fmap and the def's own function, at a function that
-- calls the def back
{-# LANGUAGE LambdaCase, DeriveFunctor #-}
module Transform where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)

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

-- a local constant in a cata's algebra (IR.Core's compiled2Term3)
data Loc = Gen String (Maybe Loc) | Here
  deriving (Eq, Show)

data An r = An Loc Int r | End Loc
  deriving (Eq, Show, Functor)

annotate :: E -> Fix An
annotate = cata f where
  anno = Gen "annotate" Nothing
  f e = case e of
    Pair a b -> Fix (An anno 1 a)
    Set a -> Fix (An (Gen "set" (Just anno)) 2 a)
    _ -> Fix (End anno)

locs :: Fix An -> [Loc]
locs (Fix x) = case x of
  An l n r -> if n > 1 then l : locs r else locs r
  End l -> [l]

exAnno :: Int -> [Loc]
exAnno n = locs (annotate (call n (pair env env) zero))
