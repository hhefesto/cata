{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
-- a sizing step (telomare's sizeTermM): steps on steps, a check that runs the
-- whole traversal, a gate's knot beside it, errors at function types
module SizeKnot where

import Control.Exception (Exception, throw)
import Control.Monad ((<=<))
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata, para, project)
import Data.Functor.Identity (Identity (..))
import Data.Set (Set)
import qualified Data.Set as Set

data TF r = Z | P r r | D Int r | L r | S r | V | E Int r r | A Int r | I Int | U Int r | W Int r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

type T = Fix TF

data CF r = CZ | CP r r | CD Int r | CL r | CS r | CV
  deriving (Eq, Show, Functor, Foldable, Traversable)

type C = Fix CF

name :: TF r -> String
name = \case
  Z -> "Z"
  P _ _ -> "P"
  S _ -> "S"
  A n _ -> "A" <> show n
  _ -> "other"

count :: T -> Int
count = cata (\x -> 1 + sum x)

data Acc a = Acc [Int] a deriving (Eq, Show)

instance Functor Acc where
  fmap f (Acc n a) = Acc n (f a)

instance Applicative Acc where
  pure = Acc []
  Acc n f <*> Acc m a = Acc (n <> m) (f a)
  liftA2 f (Acc n a) (Acc m b) = Acc (n <> m) (f a b)

instance Monad Acc where
  Acc n a >>= k = case k a of Acc m b -> Acc (n <> m) b

data Gate = Gate Bool Bool (Maybe T)

newtype Bad = Bad String deriving (Eq, Show)

instance Exception Bad

transM :: Monad m => (TF T -> m T) -> T -> m T
transM f = c where
  c = f <=< (c' . project)
  c' = \case
    s@(D _ _) -> pure s
    x         -> mapM c x

basicM :: Monad m => (TF T -> m T) -> TF T -> m T
basicM other x = f x where
  f = \case
    L (Fix (P a _)) -> pure a
    y@Z             -> pure (Fix y)
    y@(P _ _)       -> pure (Fix y)
    _               -> other x

stuckM :: Monad m => (TF T -> m T) -> TF T -> m T
stuckM other x = f x where
  f = \case
    S (Fix (P (Fix (D _ d)) e)) -> transM run d where
      run = basicM (stuckM other) . repl
      e' = project e
      repl = \case
        V  -> e'
        x' -> x'
    y@(D _ _) -> pure (Fix y)
    _         -> other x

abortM :: Monad m => (TF T -> m T) -> TF T -> m T
abortM other x = f x where
  f = \case
    L a@(Fix (A _ _)) -> pure a
    y@(A _ _)         -> pure (Fix y)
    _                 -> other x

inputM :: Monad m => Set Int -> (TF T -> m T) -> TF T -> m T
inputM zs other x = f x where
  res n = if Set.member n zs then Fix Z else Fix (I n)
  f = \case
    L (Fix (I n)) -> pure . res $ n * 2 + 1
    I n           -> pure $ res n
    _             -> other x

splitM :: Monad m => (TF T -> m T) -> TF T -> m T
splitM other = \case
  S (Fix (P (Fix V) (Fix (I n)))) -> pure . Fix $ E n (Fix Z) (Fix V)
  x                               -> other x

superM :: Monad m => (T -> Gate) -> (TF T -> m T) -> (TF T -> m T) -> TF T -> m T
superM gate step other x = f x where
  pb bf = step . bf
  f = \case
    L (Fix (E n a b)) -> (\u v -> Fix (E n u v)) <$> pb L a <*> pb L b
    S (Fix (P (Fix V) (Fix (E n a b)))) -> pure $ case (gate a, gate b) of
      (Gate True _ _, Gate _ True _) -> Fix (E n a b)
      _                              -> Fix Z
    y@(E _ _ _) -> pure (Fix y)
    _ -> other x

unsizedM :: Int -> Set Int -> (Int -> T -> Acc T) -> (Int -> Acc ()) -> (TF T -> Acc T) -> TF T -> Acc T
unsizedM most _zs test acc other x = f x where
  f = \case
    U tok r | tok > most -> pure (Fix (A 7 r))
            | otherwise  -> acc tok >>= const (test tok r)
    _ -> other x

stuckSizingM :: Monad m => (TF T -> m T) -> TF T -> m T
stuckSizingM other = \case
  y@(L _)   -> pure (Fix y)
  y@(S _)   -> pure (Fix y)
  x         -> other x

gateBasic :: (T -> Gate) -> T -> Gate
gateBasic other = \case
  Fix Z       -> Gate True False Nothing
  Fix (P _ _) -> Gate False True Nothing
  x           -> other x

gateSuper :: (T -> Gate) -> (T -> Gate) -> T -> Gate
gateSuper step other = \case
  Fix (E n a b) -> let Gate la ra ba = step a
                       Gate lb rb bb = step b
                       co = case (ba, bb) of
                         (Just u, Just v) -> Just (Fix (E n u v))
                         _                -> maybe bb Just ba
                   in Gate (la || lb) (ra || rb) co
  x -> other x

testIndexed :: Set Int -> (Int -> T -> T) -> Int -> T -> T
testIndexed zs other r = \case
  Fix (I n) -> if Set.member n zs then Fix Z else Fix (A r (Fix Z))
  y         -> other r y

testSuper :: (T -> T) -> (Int -> T -> T) -> Int -> T -> T
testSuper step other r = \case
  Fix (E n a b) -> Fix (E n (step a) (step b))
  y             -> other r y

convB :: Applicative m => (TF (m C) -> m C) -> TF (m C) -> m C
convB other = \case
  Z     -> pure (Fix CZ)
  P a b -> (\u v -> Fix (CP u v)) <$> a <*> b
  x     -> other x

convS :: Applicative m => (TF (m C) -> m C) -> TF (m C) -> m C
convS other = \case
  L a   -> Fix . CL <$> a
  S a   -> Fix . CS <$> a
  D n a -> Fix . CD n <$> a
  V     -> pure (Fix CV)
  x     -> other x

toC :: T -> C
toC = runIdentity . cata (convB (convS (error "toC: unexpected node")))

exToC :: Int -> C
exToC n = toC (Fix (P (Fix (L (Fix V))) (if n > 2 then Fix (I n) else Fix Z)))

size :: Int -> Bool -> T -> Either Int ([Int], T)
size budget capped x = tidy . transM evalStep $ mx where
  zeros = Set.empty
  fuel = budget + 1
  nested = \case
    V     -> Fix Z
    other -> Fix other
  mx = if capped then Fix (S (Fix (P x (Fix (I 0))))) else cata nested x
  tidy (Acc sm r) = case foldAborted r of
    Just 7 -> Left (length sm)
    Just i -> Left (negate i)
    _      -> Right (sm, r)
  foldAborted = para f where
    f = \case
      A o (m, _) | o > 5 -> case m of
        Fix Z -> Just o
        Fix V -> error ("size foldAborted unexpected:\n" <> show o)
        _     -> Just o
      other -> foldr (\(_, b) r -> maybe r Just b) Nothing other
  unhandledGate g = error ("size unhandled gate input: " <> name (project g))
  gateResult = gateBasic (gateSuper gateResult unhandledGate)
  unsizedTest :: Int -> T -> T
  unsizedTest ri = testIndexed zeros (testSuper (unsizedTest ri) (const id)) ri
  unhandledError err = throw $ Bad ("size unhandled case\n" <> name err)
  checkStep other = \case
    W o tc c -> do
      checked <- transM evalStep (Fix (S (Fix (P tc c))))
      pure $ case checked of
        Fix (A _ _)                   -> checked
        _ | maybe False (> 3) (foldAborted checked) -> checked
          | otherwise                 -> maybe c id (narrow fuel o tc c)
    other' -> other other'
  narrow most o tc c = if o > most then Nothing else Just (if count tc == count c then Fix Z else c)
  evalStep = basicM (stuckM (abortM (inputM zeros (splitM (superM gateResult evalStep (checkStep (unsizedM fuel zeros (\ri -> pure . unsizedTest ri) (\t -> Acc [t] ()) (stuckSizingM unhandledError))))))))

exSize :: Int -> Bool -> Either Int ([Int], T)
exSize n b = size n b (Fix (D 1 (Fix (P (Fix (U 2 (Fix (P (Fix V) (Fix (L (Fix V))))))) (Fix (W 3 (Fix (D 2 (Fix (L (Fix V))))) (Fix (L (Fix (E 1 (Fix (P (Fix V) (Fix Z))) (Fix (P (Fix Z) (Fix Z)))))))))))))
