module StateTE where

-- cata's StateT rules: StateT s (Either e) a as S -> Either E (A & S), and
-- StateT s ((,) w) a as S -> W & A & S (the pair's Writer: >>= joins the
-- logs with w's <>, pure logs mempty); telomare's validateVariables
-- (StateT (Map String Term1) (Either ResolverError)) and
-- annotateUnsizedCount (StateT Integer ((,) (Set Integer)))

import Control.Monad.Trans (lift)
import Control.Monad.State (StateT, evalStateT, execStateT, runStateT)
import qualified Control.Monad.State as State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

type V = StateT (Map String Int) (Either String)

bindV :: String -> Int -> V ()
bindV n k = do
  m <- State.get
  State.put (Map.insert n k m)

lookV :: String -> V Int
lookV n = do
  m <- State.get
  case Map.lookup n m of
    Nothing -> lift (Left ("unbound " ++ n))
    Just k -> pure k

sumV :: [String] -> V Int
sumV ns = case ns of
  [] -> pure 0
  n : rest -> (+) <$> lookV n <*> sumV rest

ex1 :: Int -> Either String Int
ex1 k = evalStateT (bindV "a" k >> bindV "b" (k + 1) >> sumV ["a", "b", "a"]) Map.empty

ex2 :: String -> Either String Int
ex2 n = evalStateT (bindV "a" 3 >> lookV n) Map.empty

ex3 :: Int -> Either String [(String, Int)]
ex3 k = fmap Map.toList (execStateT (bindV "x" k >> State.modify (Map.insert "y" (2 * k))) Map.empty)

ex4 :: Int -> Either String (Int, [(String, Int)])
ex4 k = fmap (\(a, m) -> (a, Map.toList m)) (runStateT (bindV "x" k >> State.gets (Map.findWithDefault 0 "x")) Map.empty)

type C = StateT Integer ((,) (Set Integer))

fresh :: C Integer
fresh = do
  n <- State.get
  State.put (n + 1)
  lift (Set.singleton n, n)

pairC :: C (Integer, Integer)
pairC = (,) <$> fresh <*> fresh

ex5 :: Integer -> ([Integer], (Integer, Integer))
ex5 k = let (w, a) = evalStateT pairC k in (Set.toList w, a)

ex6 :: Integer -> ([Integer], Integer)
ex6 k = let (w, s) = execStateT (fresh >> fresh >> fresh) k in (Set.toList w, s)

ex7 :: Integer -> ([Integer], Integer)
ex7 k = let (w, a) = evalStateT (fmap (* 10) fresh >>= \x -> fmap (+ x) fresh) k in (Set.toList w, a)
