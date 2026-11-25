-- Machine's steps over a handler that errs (Size's refinementCheckStep,
-- getInputLimits): a partial function given to a def answering a function,
-- and through a tower of steps
{-# LANGUAGE LambdaCase, DeriveTraversable #-}
module PartEval where

import Control.Applicative (Applicative (..))
import Control.Monad ((<=<))
import Data.Foldable (asum)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.Functor.Identity (Identity (..))

data F r = Zero | Pair r r | Env | Defer Int r | Set r | Left1 r | Ab (Maybe Int)
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
  Ab m -> maybe 0 id m

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

abortStep :: (F E -> E) -> F E -> E
abortStep other = \case
  Left1 a@(Fix (Ab (Just _))) -> a
  x@(Ab _) -> Fix x
  x -> other x

-- Eval.Reference's eval: a composition over a walk with a step that errs
evalC :: E -> Either Int E
evalC = checkError . (\x -> if size x > 1000 then zero else x) . transformND step where
  step = basicStep (stuckStep (abortStep unhandled))
  unhandled x = error ("evalC unhandled " ++ show (size (Fix x)))
  findError = \case
    Ab (Just e) -> Just e
    x -> asum x
  checkError x = case cata findError x of
    Just e -> Left e
    _ -> Right x

exEvalC :: Int -> Either Int Int
exEvalC n = fmap size (evalC (if n > 3 then pair zero (Fix (Left1 (Fix (Ab (Just n))))) else if n > 1 then pair zero zero else Fix (Set env)))
