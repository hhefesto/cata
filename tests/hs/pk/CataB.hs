module CataB where

import qualified Control.Monad.State as State
import Control.Monad.State (State)

data O = OVar Int | OApp O O | OClo Int O | OPair O O | ONil | OIte O O O | OL O
  deriving (Show, Eq)

type B a = State (Int, Int) a

deferS :: O -> B O
deferS x = do
  fi <- State.gets fst
  State.modify (\(_, u) -> (fi + 1, u))
  pure (OClo fi x)

pairS :: Monad m => m O -> m O -> m O
pairS a b = do
  a' <- a
  b' <- b
  pure (OPair a' b')

clamS :: B O -> B O
clamS x = pairS (x >>= deferS) $ pure ONil

appS :: B O -> B O -> B O
appS c i = OL <$> pairS (pure ONil) (pairS i c)

var :: Int -> O
var n = if n < 0 then OVar 0 else OVar n

varP :: Int -> O
varP n = iterate OL (OVar 0) !! n

wrap :: Int -> B O -> B O -> B O -> B O
wrap _loc t r b =
  let tWrap = pairS ((>>= deferS) (appS (pure $ varP 1) (pure $ varP 0))) (pairS t $ pure ONil)
      trb = pairS tWrap . pairS r . pairS b $ pure ONil
      innerBody = appS (appS (pure $ varP 1) (pure . OL $ OL ONil)) (pure $ varP 0)
      mainBody = pairS (innerBody >>= deferS) (pure ONil)
  in pairS (mainBody >>= deferS) trb

church :: Int -> Int -> B O
church _l n = clamS . clamS $ iterate (appS (pure $ varP 1)) (pure $ varP 0) !! n
