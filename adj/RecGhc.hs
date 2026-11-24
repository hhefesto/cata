{-# LANGUAGE ExistentialQuantification, FlexibleInstances, LambdaCase, TypeFamilies #-}
-- adj/RecGhc.hs: GHC's own recursion and functions as values, written as
-- Bend equations (adj/REC.bend) that Bend's checker and BendTT's kernel
-- compute against Core.bend's HR (section 14: eval.hp, and F's program,
-- eval.bp): so the model's mutual recursion and its closures are GHC's, not
-- ones written to fit the proof.  Each program is written once, over the
-- class Lang; its instance I runs it as it stands (Haskell's recursion,
-- Haskell's functions, Haskell's data types), and its instance C writes
-- the model's program: a named function (fun) is a definition of the
-- table, a lambda (lam) the closure of the definition it is lifted to,
-- over the variables around it.  GHC's answer (an error where it throws)
-- is the equation's right side.  A program marked Gap answers in GHC, whose
-- laziness never forces an argument that errs, where the strict model errs
-- (section 9): its equation says so.  Run by adj/int.zsh; REC.bend is its
-- output, not edited by hand.
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad.State.Strict (State, get, modify, put, runState)
import qualified Data.Map.Strict as M
import Numeric.Natural (Natural)

-- the language -------------------------------------------------------------------

class Lang r where
  nat :: Natural -> r Natural
  unit :: r ()
  pair :: r a -> r b -> r (a, b)
  first :: r (a, b) -> r a
  second :: r (a, b) -> r b
  inl :: r a -> r (Either a b)
  inr :: r b -> r (Either a b)
  match :: r (Either a b) -> (r a -> r c) -> (r b -> r c) -> r c
  nil :: r [a]
  cons :: r a -> r [a] -> r [a]
  uncons :: r [a] -> r (Either () (a, [a]))
  add, sub, divi, modu :: r Natural -> r Natural -> r Natural
  lt :: r Natural -> r Natural -> r Bool
  if_ :: r Bool -> r a -> r a -> r a
  let_ :: r a -> (r a -> r b) -> r b
  lam :: (r a -> r b) -> r (a -> b)
  app :: r (a -> b) -> r a -> r b
  -- a named function, applied, and as a value
  fun :: String -> (r a -> r b) -> r a -> r b
  val :: String -> (r a -> r b) -> r (a -> b)
  -- a data type's value, as the sum of products it is, and back
  open :: D a => r a -> r (Rep a)
  close :: D a => r (Rep a) -> r a

-- a data type and the sum of products it is
class D a where
  type Rep a
  toRep :: a -> Rep a
  fromRep :: Rep a -> a

-- Haskell itself --------------------------------------------------------------------

newtype I a = I {unI :: a}

instance Lang I where
  nat = I
  unit = I ()
  pair (I a) (I b) = I (a, b)
  first (I p) = I (fst p)
  second (I p) = I (snd p)
  inl (I a) = I (Left a)
  inr (I b) = I (Right b)
  match (I s) f g = case s of Left a -> f (I a); Right b -> g (I b)
  nil = I []
  cons (I a) (I as) = I (a : as)
  uncons (I l) = I (case l of [] -> Left (); a : as -> Right (a, as))
  add (I a) (I b) = I (a + b)
  sub (I a) (I b) = I (a - b)
  divi (I a) (I b) = I (a `div` b)
  modu (I a) (I b) = I (a `mod` b)
  lt (I a) (I b) = I (a < b)
  if_ (I c) a b = if c then a else b
  let_ a f = f a
  lam f = I (\a -> unI (f (I a)))
  app (I f) (I a) = I (f a)
  fun _ f = f
  val _ f = I (\a -> unI (f (I a)))
  open (I a) = I (toRep a)
  close (I a) = I (fromRep a)

-- the model's program ----------------------------------------------------------------

-- the definitions so far: a named function's number, each definition's body
data Defs = Defs {names :: M.Map String Int, bodies :: M.Map Int String}

-- a term, d variables around it: its environment is (.. ((), x0) .., x(d-1))
newtype C a = C {unC :: Int -> State Defs String}

-- the variable bound at depth l, seen from depth d
var :: Int -> C a
var l = C (\d -> pure ("C.HrTm{" ++ iterate (\t -> "C.HComp{" ++ t ++ ", C.HFst{}}") "C.HSnd{}" !! (d - 1 - l) ++ "}"))

tm :: String -> C a
tm t = C (\_ -> pure ("C.HrTm{" ++ t ++ "}"))

after :: String -> C a -> C b
after t (C a) = C (\d -> (\x -> "C.HrComp{C.HrTm{" ++ t ++ "}, " ++ x ++ "}") <$> a d)

two :: String -> C a -> C b -> C c
two k (C a) (C b) = C (\d -> (\x y -> "C." ++ k ++ "{" ++ x ++ ", " ++ y ++ "}") <$> a d <*> b d)

prim :: String -> C a -> C b -> C c
prim p a b = after ("C.HPrim{C.P" ++ p ++ "{}}") (two "HrPr" a b)

-- a body under one more variable, at depth d
under :: (C a -> C b) -> Int -> State Defs String
under f d = unC (f (var d)) (d + 1)

fresh :: State Defs Int
fresh = do
  s <- get
  let j = M.size (bodies s)
  put s {bodies = M.insert j "" (bodies s)}
  pure j

fill :: Int -> String -> State Defs ()
fill j b = modify (\s -> s {bodies = M.insert j b (bodies s)})

-- a named function's number, its body written once
define :: String -> (C a -> C b) -> State Defs Int
define n f = do
  s <- get
  case M.lookup n (names s) of
    Just j -> pure j
    Nothing -> do
      j <- fresh
      modify (\t -> t {names = M.insert n j (names t)})
      under f 0 >>= fill j
      pure j

instance Lang C where
  nat n = tm ("C.HLit{" ++ show n ++ "n}")
  unit = tm "C.HUnit{}"
  pair = two "HrPr"
  first = after "C.HFst{}"
  second = after "C.HSnd{}"
  inl = after "C.HInl{}"
  inr = after "C.HInr{}"
  match (C s) f g = C (\d -> do
    x <- s d
    l <- under f d
    r <- under g d
    pure ("C.HrComp{C.HrCase{" ++ l ++ ", " ++ r ++ "}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, " ++ x ++ "}}}"))
  nil = tm "C.HNil{}"
  cons = two "HrCons"
  uncons = after "C.HFold{C.HComp{C.HInl{}, C.HUnit{}}, C.HComp{C.HInr{}, C.HPr{C.HFst{}, C.HComp{C.HCase{C.HNil{}, C.HCons{C.HFst{}, C.HSnd{}}}, C.HSnd{}}}}}"
  add = prim "Add"
  sub = prim "Sub"
  divi = prim "Div"
  modu = prim "Mod"
  lt = prim "Lt"
  if_ (C c) (C a) (C b) = C (\d -> (\x y z -> "C.HrIf{" ++ x ++ ", " ++ y ++ ", " ++ z ++ "}") <$> c d <*> a d <*> b d)
  let_ (C a) f = C (\d -> do
    x <- a d
    b <- under f d
    pure ("C.HrComp{" ++ b ++ ", C.HrPr{C.HrTm{C.HId{}}, " ++ x ++ "}}"))
  lam f = C (\d -> do
    j <- fresh
    under f d >>= fill j
    pure ("C.HrTm{C.clo(" ++ show j ++ "n)}"))
  app f a = C (\d -> (\x -> "C.HrComp{C.HrApp{}, " ++ x ++ "}") <$> unC (two "HrPr" f a) d)
  fun n f (C a) = C (\d -> do
    j <- define n f
    x <- a d
    pure ("C.HrComp{C.HrCall{" ++ show j ++ "n}, C.HrPr{C.HrTm{C.HUnit{}}, " ++ x ++ "}}"))
  val n f = C (\_ -> (\j -> "C.HrTm{C.HPr{C.HLit{" ++ show j ++ "n}, C.HUnit{}}}") <$> define n f)
  open (C a) = C a
  close (C a) = C a

-- the model's program for a function
program :: (C a -> C b) -> String
program f =
  let (b, s) = runState (under f 0) (Defs M.empty M.empty)
   in "C.HPg{" ++ foldr (\t r -> "C.HdCons{" ++ t ++ ", C.HvNat{0n}, " ++ r ++ "}") "C.HdNil{}" (M.elems (bodies s)) ++ ", " ++ b ++ "}"

-- values -----------------------------------------------------------------------------

class Val a where
  text :: a -> String

instance Val Natural where
  text n = "C.HvNat{" ++ show n ++ "n}"

instance Val Bool where
  text b = "C.HvBool{" ++ show b ++ "{}}"

instance Val () where
  text () = "C.HvUnit{}"

instance (Val a, Val b) => Val (a, b) where
  text (a, b) = "C.HvPair{" ++ text a ++ ", " ++ text b ++ "}"

instance (Val a, Val b) => Val (Either a b) where
  text = \case Left a -> "C.HvInl{" ++ text a ++ "}"; Right b -> "C.HvInr{" ++ text b ++ "}"

instance Val a => Val [a] where
  text = foldr (\a r -> "C.HvCons{" ++ text a ++ ", " ++ r ++ "}") "C.HvNil{}"

-- two data types with fields of each other, twice: trees and their forests,
-- a little language's expressions and its blocks
data Rose = Rose Natural Forest

data Forest = None | More Rose Forest

instance D Rose where
  type Rep Rose = (Natural, Forest)
  toRep (Rose n f) = (n, f)
  fromRep (n, f) = Rose n f

instance D Forest where
  type Rep Forest = Either () (Rose, Forest)
  toRep = \case None -> Left (); More r f -> Right (r, f)
  fromRep = \case Left () -> None; Right (r, f) -> More r f

instance Val Rose where text = text . toRep

instance Val Forest where text = text . toRep

data Ex = Num Natural | Minus Ex Ex | Over Ex Ex | Do Block

data Block = Return Ex | Seq Ex Block

instance D Ex where
  type Rep Ex = Either Natural (Either (Ex, Ex) (Either (Ex, Ex) Block))
  toRep = \case Num n -> Left n; Minus a b -> Right (Left (a, b)); Over a b -> Right (Right (Left (a, b))); Do b -> Right (Right (Right b))
  fromRep = \case Left n -> Num n; Right (Left (a, b)) -> Minus a b; Right (Right (Left (a, b))) -> Over a b; Right (Right (Right b)) -> Do b

instance D Block where
  type Rep Block = Either Ex (Ex, Block)
  toRep = \case Return e -> Left e; Seq e b -> Right (e, b)
  fromRep = \case Left e -> Return e; Right (e, b) -> Seq e b

instance Val Ex where text = text . toRep

instance Val Block where text = text . toRep

-- the programs ------------------------------------------------------------------------

true, false :: Lang r => r Bool
true = lt (nat 0) (nat 1)
false = lt (nat 1) (nat 0)

-- mutual recursion
evenN, oddN :: Lang r => r Natural -> r Bool
evenN = fun "even" (\n -> if_ (lt n (nat 1)) true (oddN (sub n (nat 1))))
oddN = fun "odd" (\n -> if_ (lt n (nat 1)) false (evenN (sub n (nat 1))))

-- three functions in a cycle, one of them partial: an error from below 0
hofF, hofM, hofG :: Lang r => r Natural -> r Natural
hofF = fun "hofF" (\n -> if_ (lt n (nat 1)) (nat 1) (sub n (hofM (hofF (sub n (nat 1))))))
hofM = fun "hofM" (\n -> if_ (lt n (nat 1)) (nat 0) (sub n (hofF (hofM (sub n (nat 1))))))
hofG = fun "hofG" (\n -> add (hofF n) (sub (hofM n) (nat 1)))

-- nested recursion
ack :: Lang r => r (Natural, Natural) -> r Natural
ack = fun "ack" (\p -> if_ (lt (first p) (nat 1)) (add (second p) (nat 1)) (if_ (lt (second p) (nat 1)) (ack (pair (sub (first p) (nat 1)) (nat 1))) (ack (pair (sub (first p) (nat 1)) (ack (pair (first p) (sub (second p) (nat 1))))))))

-- a recursion no argument measures
collatz :: Lang r => r Natural -> r Natural
collatz = fun "collatz" (\n -> if_ (lt n (nat 2)) (nat 0) (add (nat 1) (collatz (if_ (lt (modu n (nat 2)) (nat 1)) (divi n (nat 2)) (add (nat 1) (add n (add n n)))))))

-- functions as values: an argument, a field, an answer
mapL :: Lang r => r (a -> b, [a]) -> r [b]
mapL = fun "map" (\p -> match (uncons (second p)) (\_ -> nil) (\q -> cons (app (first p) (first q)) (mapL (pair (first p) (second q)))))

foldrL :: Lang r => r ((a, b) -> b, (b, [a])) -> r b
foldrL = fun "foldr" (\p -> match (uncons (second (second p))) (\_ -> first (second p)) (\q -> app (first p) (pair (first q) (foldrL (pair (first p) (pair (first (second p)) (second q)))))))

addAll :: Lang r => r (Natural, [Natural]) -> r [Natural]
addAll p = mapL (pair (lam (\x -> add x (first p))) (second p))

-- a list of functions, each applied
applyAll :: Lang r => r Natural -> r [Natural]
applyAll n = mapL (pair (lam (\f -> app f n)) (cons (lam (\x -> add x x)) (cons (val "succ" (\x -> add x (nat 1))) (cons (lam (\x -> divi x n)) nil))))

twice :: Lang r => r (a -> a) -> r (a -> a)
twice = fun "twice" (\f -> lam (\x -> app f (app f x)))

twiceTwice :: Lang r => r Natural -> r Natural
twiceTwice n = app (twice (twice (lam (\x -> add x n)))) n

-- foldl by foldr: the accumulator a function
foldlL :: Lang r => r ((b, a) -> b, (b, [a])) -> r b
foldlL p = app (foldrL (pair (lam (\q -> lam (\acc -> app (second q) (app (first p) (pair acc (first q)))))) (pair (lam (\x -> x)) (second (second p))))) (first (second p))

minusAll :: Lang r => r (Natural, [Natural]) -> r Natural
minusAll p = foldlL (pair (lam (\q -> sub (first q) (second q))) p)

-- continuations
factK :: Lang r => r (Natural, Natural -> Natural) -> r Natural
factK = fun "factK" (\p -> if_ (lt (first p) (nat 1)) (app (second p) (nat 1)) (factK (pair (sub (first p) (nat 1)) (lam (\v -> app (second p) (times (pair (first p) v)))))))

times :: Lang r => r (Natural, Natural) -> r Natural
times = fun "times" (\p -> if_ (lt (first p) (nat 1)) (nat 0) (add (second p) (times (pair (sub (first p) (nat 1)) (second p)))))

fact :: Lang r => r Natural -> r Natural
fact n = factK (pair n (lam (\v -> v)))

-- a class: its dictionary (the neutral, the operation), and two instances
mconcatD :: Lang r => r ((a, (a, a) -> a), [a]) -> r a
mconcatD p = foldrL (pair (second (first p)) (pair (first (first p)) (second p)))

sumD :: Lang r => r (Natural, (Natural, Natural) -> Natural)
sumD = pair (nat 0) (lam (\q -> add (first q) (second q)))

appendD :: Lang r => r ([a], ([a], [a]) -> [a])
appendD = pair nil (lam (\q -> foldrL (pair (lam (\c -> cons (first c) (second c))) (pair (second q) (first q)))))

sumConcat :: Lang r => r [[Natural]] -> r (Natural, [Natural])
sumConcat xss = let_ (mconcatD (pair appendD xss)) (\xs -> pair (mconcatD (pair sumD xs)) xs)

-- mutually recursive data types, each with its functions
roseSum, roseDepth :: Lang r => r Rose -> r Natural
roseSum = fun "roseSum" (\t -> let_ (open t) (\p -> add (first p) (forestSum (second p))))
roseDepth = fun "roseDepth" (\t -> add (nat 1) (forestDepth (second (open t))))

forestSum, forestDepth :: Lang r => r Forest -> r Natural
forestSum = fun "forestSum" (\f -> match (open f) (\_ -> nat 0) (\q -> add (roseSum (first q)) (forestSum (second q))))
forestDepth = fun "forestDepth" (\f -> match (open f) (\_ -> nat 0) (\q -> let_ (pair (roseDepth (first q)) (forestDepth (second q))) (\m -> if_ (lt (first m) (second m)) (second m) (first m))))

-- and one that builds the other's values: a tree with each label doubled
roseMap :: Lang r => r (Natural -> Natural, Rose) -> r Rose
roseMap = fun "roseMap" (\p -> let_ (open (second p)) (\q -> close (pair (app (first p) (first q)) (forestMap (pair (first p) (second q))))))

forestMap :: Lang r => r (Natural -> Natural, Forest) -> r Forest
forestMap = fun "forestMap" (\p -> match (open (second p)) (\_ -> close (inl unit)) (\q -> close (inr (pair (roseMap (pair (first p) (first q))) (forestMap (pair (first p) (second q)))))))

roseDouble :: Lang r => r Rose -> r Rose
roseDouble t = roseMap (pair (lam (\x -> add x x)) t)

-- an interpreter of the little language, partial: (-) below 0, div by 0
evalEx :: Lang r => r Ex -> r Natural
evalEx = fun "evalEx" (\e -> match (open e) (\n -> n) (\r -> match r (\p -> sub (evalEx (first p)) (evalEx (second p))) (\s -> match s (\p -> divi (evalEx (first p)) (evalEx (second p))) evalBlock)))

evalBlock :: Lang r => r Block -> r Natural
evalBlock = fun "evalBlock" (\b -> match (open b) evalEx (\p -> add (evalEx (first p)) (evalBlock (second p))))

-- an argument that errs, never forced
constErr :: Lang r => r Natural -> r Natural
constErr n = app (app (lam (\x -> lam (\_ -> x))) n) (sub (nat 0) (nat 1))

-- the equations ------------------------------------------------------------------------

data Mode = Same | Gap

-- a program's name, its depth of calls, whether the strict model agrees, its
-- inputs; the equations of it
data P = forall a b. (Val a, Val b) => P String Int Mode (I a -> I b) (C a -> C b) [a]

programs :: [P]
programs =
  [ P "even" 40 Same evenN evenN [0, 1, 2, 7, 10],
    P "hofG" 60 Same hofG hofG [0, 1, 3, 5],
    P "hofF" 60 Same hofF hofF [0, 1, 4, 6],
    P "ack" 60 Same ack ack [(0, 3), (1, 2), (2, 2), (2, 3)],
    P "collatz" 60 Same collatz collatz [1, 3, 6, 7],
    P "addAll" 30 Same addAll addAll [(5, []), (5, [1, 2, 3])],
    P "applyAll" 30 Same applyAll applyAll [0, 1, 4],
    P "twiceTwice" 30 Same twiceTwice twiceTwice [0, 3],
    P "minusAll" 30 Same minusAll minusAll [(10, [1, 2, 3]), (3, [2, 2]), (4, [])],
    P "fact" 60 Same fact fact [0, 1, 4],
    P "sumConcat" 40 Same sumConcat sumConcat [[], [[1, 2], [], [3]]],
    P "roseSum" 40 Same roseSum roseSum roses,
    P "roseDepth" 40 Same roseDepth roseDepth roses,
    P "roseDouble" 40 Same roseDouble roseDouble roses,
    P "evalEx" 40 Same evalEx evalEx exs,
    P "constErr" 30 Gap constErr constErr [4]
  ]
  where
    roses = [Rose 4 None, Rose 1 (More (Rose 2 (More (Rose 5 None) None)) (More (Rose 3 None) None))]
    exs = [Num 3, Minus (Num 7) (Num 2), Minus (Num 2) (Num 7), Over (Num 9) (Num 2), Over (Num 9) (Num 0), Do (Seq (Num 1) (Seq (Minus (Num 9) (Num 4)) (Return (Do (Return (Num 2)))))), Do (Seq (Over (Num 1) (Num 0)) (Return (Num 2)))]

equations :: P -> IO [String]
equations (P n k m hi hc xs) = do
  eqs <- mapM one (zip [1 :: Int ..] xs)
  pure (("def " ++ n ++ "() -> C.HPg:\n  " ++ program hc) : concat eqs)
  where
    one (i, x) = do
      r <- try (let t = text (unI (hi (I x))) in evaluate (length t) >> pure t)
      let v = case (m, r) of
            (Gap, Right _) -> "None{}"
            (_, Right t) -> "Some{" ++ t ++ "}"
            (_, Left e) -> const "None{}" (e :: SomeException)
          input = "C.HvPair{C.HvUnit{}, " ++ text x ++ "}"
          name = "ghc." ++ n ++ ".i" ++ show i
          note = case (m, r) of (Gap, Right t) -> "# GHC answers " ++ t ++ " (an argument that errs, never forced)\n"; _ -> ""
      pure
        [ note ++ "def " ++ name ++ "() -> {C.eval.hp(" ++ show k ++ "n, " ++ n ++ "(), " ++ input ++ ") == C.RDone{" ++ v ++ "} : C.Run}:\n  {==}",
          "def " ++ name ++ ".F() -> {C.eval.bp(C.F.pn(" ++ show k ++ "n, " ++ n ++ "()), C.enc(" ++ input ++ ")) == C.encM(" ++ v ++ ") : Maybe<&2, C.BV>}:\n  {==}"
        ]

main :: IO ()
main = do
  putStr "# GHC's recursion and functions as values, against Core.bend's (section 14):\n# written by RecGhc.hs (adj/int.zsh), not by hand\n\nimport Base\nimport ./Core.bend as C\n"
  ls <- concat <$> mapM equations programs
  mapM_ (\l -> putStr ("\n" ++ l ++ "\n")) ls
