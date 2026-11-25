-- IR.Builder's shapes: an action that fails given to defs that answer
-- actions (clamS, lamS, pairS), at one argument or both
module PartBuild where

import Control.Monad.State

data T = Z | P T T | L T | D Int T | E
  deriving (Eq, Show)

type B = State (Int, Int)

deferS :: T -> B T
deferS x = do
  fi <- gets fst
  modify (\(_, u) -> (succ fi, u))
  pure (D fi x)

pairS :: B T -> B T -> B T
pairS a b = do
  a' <- a
  b' <- b
  pure (P a' b')

clamS :: B T -> B T
clamS x = pairS (x >>= deferS) $ pure Z

lamS :: B T -> B T
lamS x = pairS (x >>= deferS) $ pure E

appS :: B T -> B T -> B T
appS c i = L . L <$> pairS (deferS (P Z E)) (pairS i c)

varB :: Int -> T
varB n = if n < 1 then L E else P E (varB (n - 1))

i2CB :: Int -> B T
i2CB n = clamS . lamS $ iterate (appS (pure $ varB 1)) (pure $ varB 0) !! n

wrap :: B T -> B T -> B T
wrap t r =
  let body = appS (i2CB 2) t
  in pairS (body >>= deferS) (pairS r (i2CB 3))

exI :: Int -> (T, (Int, Int))
exI n = runState (i2CB n) (0, 1)

exW :: Int -> T
exW n = evalState (wrap (pure Z) (i2CB n)) (n, 1)

-- a plain function and an action, both partial
both :: (Int -> Int) -> (Int -> Int) -> [Int] -> [Int]
both f g xs = case xs of
  [] -> []
  x : t -> f x : g x : both f g t

exBoth :: [Int] -> Int -> [Int]
exBoth xs k = both (\x -> if x > k then error "big" else x) (\x -> head (drop x xs)) xs
