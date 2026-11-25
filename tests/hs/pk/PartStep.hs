-- Machine's steps over a handler that errs (Size's refinementCheckStep,
-- getInputLimits): a partial function given to a def answering a function,
-- and through a tower of steps
{-# LANGUAGE LambdaCase, DeriveTraversable #-}
module PartStep where

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

-- getInputLimits: the same with a monad, a writer of its own
data Acc a x = Acc { getAcc :: !a, getX :: x }
  deriving (Functor)

instance Monoid a => Applicative (Acc a) where
  pure = Acc mempty
  Acc u f <*> Acc v x = Acc (u <> v) (f x)
  liftA2 f (Acc u x) (Acc v y) = Acc (u <> v) (f x y)

instance Monoid a => Monad (Acc a) where
  Acc u x >>= f = case f x of Acc v y -> Acc (u <> v) y

transformNDM :: (Monad m) => (F E -> m E) -> E -> m E
transformNDM f = c where
  c = f <=< (c' . unFix)
  c' = \case
    s@(Defer _ _) -> pure s
    x             -> mapM c x

basicStepM :: Monad m => (F E -> m E) -> F E -> m E
basicStepM other x = f x where
  f = \case
    x'@Zero -> pure (Fix x')
    x'@(Pair _ _) -> pure (Fix x')
    _ -> other x

stuckStepM :: Monad m => (F E -> m E) -> F E -> m E
stuckStepM other x = f x where
  f = \case
    Set (Fix (Pair (Fix (Defer _ d)) e)) -> transformNDM run d where
      run = basicStepM (stuckStepM other) . repl
      e' = unFix e
      repl = \case
        Env -> e'
        y   -> y
    Left1 (Fix (Pair a _)) -> pure a
    x'@(Defer _ _) -> pure (Fix x')
    _ -> other x

limitStepM :: (F E -> Acc [Int] E) -> F E -> Acc [Int] E
limitStepM other x = f x where
  f = \case
    Env -> Acc [size (eval (Fix x))] (Fix Zero)
    _ -> other x

limits :: E -> [Int]
limits = acc . transformNDM evalStep . conv where
  acc (Acc s _) = s
  conv :: E -> E
  conv = runIdentity . cata convU
  convU = \case
    Env -> pure (Fix Env)
    Left1 r -> r
    Pair a b -> (\x y -> Fix (Pair x y)) <$> a <*> b
    Set r -> Fix . Set <$> r
    Defer n r -> Fix . Defer n <$> r
    x -> error ("conv: " ++ show (size (runIdentity (Fix <$> sequence x))))
  bad x = error ("limits: " ++ show (size (Fix x)))
  evalStep = basicStepM (stuckStepM (limitStepM bad))

exLimits :: Int -> [Int]
exLimits n = limits (call n (if n > 2 then pair env env else Fix (Left1 env)) (if n > 4 then zero else pair env env))
