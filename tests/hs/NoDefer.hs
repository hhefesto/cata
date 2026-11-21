{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module NoDefer where

-- Machine's transformNoDefer in its shape: a where-group of two locals,
-- c point-free through project, c' a \case whose last alternative maps c
-- over the layer (the recursion goes through fmap, and a deferred layer
-- is left as it is); a step applied bottom-up.

import Data.Fix (Fix (..))
import Data.Functor.Foldable (project)

data EF r = Lit Int | Add r r | Neg r | Defer Int r
  deriving (Functor, Foldable, Traversable)

type E = Fix EF

noDefer :: (EF E -> E) -> E -> E
noDefer f = c where
  c = f . c' . project
  c' = \case
    s@(Defer _ _) -> s
    x -> fmap c x

-- the same with one local: the step's own recursion through fmap
noDefer1 :: (EF E -> E) -> E -> E
noDefer1 f = c where
  c x = f (case project x of
    s@(Defer _ _) -> s
    y -> fmap c y)

step :: EF E -> E
step = \case
  Add (Fix (Lit a)) (Fix (Lit b)) -> Fix (Lit (a + b))
  Neg (Fix (Lit a)) -> Fix (Lit (negate a))
  x -> Fix x

simp :: E -> E
simp = noDefer step

simp1 :: E -> E
simp1 = noDefer1 step

render :: E -> String
render (Fix e) = case e of
  Lit n -> show n
  Add a b -> "(" ++ render a ++ " + " ++ render b ++ ")"
  Neg a -> "-" ++ render a
  Defer i a -> "defer " ++ show i ++ " " ++ render a

lit :: Int -> E
lit n = Fix (Lit n)

sample :: Int -> Int -> E
sample a b = Fix (Add (Fix (Defer 7 (Fix (Add (lit a) (lit b))))) (Fix (Add (lit a) (Fix (Neg (lit b))))))

ex1 :: Int -> Int -> String
ex1 a b = render (simp (sample a b))

ex2 :: Int -> Int -> String
ex2 a b = render (simp1 (sample a b))

ex3 :: Int -> Int -> String
ex3 a b = render (simp (Fix (Add (lit a) (Fix (Add (lit b) (lit a))))))
