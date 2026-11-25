-- another module's helpers at partial actions and functions (Resolve's
-- showP through PrettyPrint.Indent)
module UseHof where

import Control.Monad.State
import ImpHof

data T = Leaf Int | Two T T | One T | Hole
  deriving (Eq, Show)

showT :: T -> State Int String
showT t = case t of
  Leaf n -> pure (show n)
  Two a b -> withTwo "P" (showT a) (showT b)
  One a -> withOne "L" (showT a)
  Hole -> error "showT: a hole"

pretty :: T -> String
pretty t = evalState (showT t) 0

ok :: T -> State Int String
ok t = withOne "ok" (pure (show (size t)))

size :: T -> Int
size t = case t of
  Leaf _ -> 1
  Two a b -> size a + size b
  One a -> size a
  Hole -> 0

exOk :: T -> (String, Int)
exOk t = runState (ok t) 1

exApply :: Int -> Int -> Int
exApply a b = apply2 (\x -> if x > 3 then error "big" else x) a b

exPick :: Int -> Int
exPick n = pick (\x -> if x > 2 then error "over" else if x > 0 then Just x else Nothing) n
