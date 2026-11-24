{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, LambdaCase, TypeFamilies #-}
-- adj/CataGhc.hs: GHC's own catamorphisms (recursion-schemes' cata) on
-- three data types, written as Bend equations (adj/CATA.bend) that Bend's
-- checker and BendTT's kernel compute against Core.bend's HCata (eval.h,
-- strict) and its lazy meaning (eval.lz): so the model's cata is GHC's,
-- not one written to fit the proof.  A value is built here, in Haskell,
-- and written as the model's rose by recursion-schemes' project and the
-- base functor's derived Foldable (its children, left to right), and a
-- shape function per type (the constructor, its fields that are not the
-- type); each algebra is written twice, as the model's term and as the
-- Haskell cata runs, and GHC's answer (None{} where it throws) is the
-- equation's right side.  The strict equation is written where GHC's
-- answer forces every child (the model's eval.h is strict: section 9);
-- the lazy one always.  Run by adj/int.zsh; CATA.bend is its output, not
-- edited by hand.
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Data.Foldable (toList)
import Data.Functor.Foldable (Base, Recursive (..), cata)
import Numeric.Natural (Natural)

-- the model's values (Core.bend's HV), as Bend text
data M = MNat Natural | MUnit | MPair M M | MInl M | MInr M | MList [M]

showM :: M -> String
showM = \case
  MNat n -> "C.HvNat{" ++ show n ++ "n}"
  MUnit -> "C.HvUnit{}"
  MPair a b -> "C.HvPair{" ++ showM a ++ ", " ++ showM b ++ "}"
  MInl a -> "C.HvInl{" ++ showM a ++ "}"
  MInr b -> "C.HvInr{" ++ showM b ++ "}"
  MList xs -> foldr (\h t -> "C.HvCons{" ++ showM h ++ ", " ++ t ++ "}") "C.HvNil{}" xs

-- a value as the model's rose: its layer's shape and its children's roses
rose :: (Recursive t, Foldable (Base t)) => (Base t t -> M) -> t -> M
rose sh x = let l = project x in MPair (sh l) (MList (map (rose sh) (toList l)))

-- a binary tree
data Tree = Leaf Natural | Node Tree Tree

data TreeF r = LeafF Natural | NodeF r r deriving (Functor, Foldable, Traversable)

type instance Base Tree = TreeF

instance Recursive Tree where
  project (Leaf n) = LeafF n
  project (Node a b) = NodeF a b

treeSh :: TreeF a -> M
treeSh (LeafF n) = MInl (MNat n)
treeSh (NodeF _ _) = MInr MUnit

-- a rose tree: a label and a list of children
data Rose = Rose Natural [Rose]

data RoseF r = RoseF Natural [r] deriving (Functor, Foldable, Traversable)

type instance Base Rose = RoseF

instance Recursive Rose where
  project (Rose n rs) = RoseF n rs

roseSh :: RoseF a -> M
roseSh (RoseF n _) = MNat n

-- an expression with Natural's partial (-) and div, and two constructors
-- whose algebras never look at one child (the second, the first)
data Expr = Lit Natural | Sub Expr Expr | Div Expr Expr | Fst Expr Expr | Snd Expr Expr

data ExprF r = LitF Natural | SubF r r | DivF r r | FstF r r | SndF r r deriving (Functor, Foldable, Traversable)

type instance Base Expr = ExprF

instance Recursive Expr where
  project (Lit n) = LitF n
  project (Sub a b) = SubF a b
  project (Div a b) = DivF a b
  project (Fst a b) = FstF a b
  project (Snd a b) = SndF a b

exprSh :: ExprF a -> M
exprSh = \case
  LitF n -> MInl (MNat n)
  SubF _ _ -> MInr (MInl MUnit)
  DivF _ _ -> MInr (MInr (MInl MUnit))
  FstF _ _ -> MInr (MInr (MInr (MInl MUnit)))
  SndF _ _ -> MInr (MInr (MInr (MInr MUnit)))

-- the model's terms ------------------------------------------------------------

-- at (shape, answers): (answers, shape), then the shape's alternative with
-- the answers beside it
byShape :: String -> String -> String
byShape l r = "C.HComp{C.HCase{" ++ l ++ ", " ++ r ++ "}, C.HComp{C.HDist{}, C.HPr{C.HSnd{}, C.HFst{}}}}"

-- the sum, and the largest (0 for none), of a list of numbers
sumL, maxL :: String
sumL = "C.HFold{C.HLit{0n}, C.HPrim{C.PAdd{}}}"
maxL = "C.HFold{C.HLit{0n}, C.HIf{C.HPrim{C.PLt{}}, C.HSnd{}, C.HFst{}}}"

-- 1 + p
succ' :: String -> String
succ' p = "C.HComp{C.HPrim{C.PAdd{}}, C.HPr{C.HLit{1n}, " ++ p ++ "}}"

-- a list's first two elements as a pair: [a, b] to (a, (b, ())), then (a, b)
two :: String
two = "C.HComp{C.HPr{C.HFst{}, C.HComp{C.HFst{}, C.HSnd{}}}, C.HFold{C.HUnit{}, C.HId{}}}"

-- a primitive at a node's two answers
at2 :: String -> String
at2 p = "C.HComp{C.HComp{C.HPrim{C.P" ++ p ++ "{}}, " ++ two ++ "}, C.HFst{}}"

-- the algebras, each the model's term and the Haskell ------------------------

treeSum, treeDepth, treeSize, treeDiff :: String
treeSum = byShape "C.HSnd{}" ("C.HComp{" ++ sumL ++ ", C.HFst{}}")
treeDepth = byShape "C.HLit{0n}" (succ' ("C.HComp{" ++ maxL ++ ", C.HFst{}}"))
treeSize = byShape "C.HLit{1n}" ("C.HComp{" ++ sumL ++ ", C.HFst{}}")
treeDiff = byShape "C.HSnd{}" (at2 "Sub")

hTreeSum, hTreeDepth, hTreeSize, hTreeDiff :: TreeF Natural -> Natural
hTreeSum = \case LeafF n -> n; NodeF a b -> a + b
hTreeDepth = \case LeafF _ -> 0; NodeF a b -> 1 + max a b
hTreeSize = \case LeafF _ -> 1; NodeF a b -> a + b
hTreeDiff = \case LeafF n -> n; NodeF a b -> a - b

-- at (label, answers)
roseSum, roseSize, roseDepth :: String
roseSum = "C.HComp{C.HPrim{C.PAdd{}}, C.HPr{C.HFst{}, C.HComp{" ++ sumL ++ ", C.HSnd{}}}}"
roseSize = succ' ("C.HComp{" ++ sumL ++ ", C.HSnd{}}")
roseDepth = succ' ("C.HComp{" ++ maxL ++ ", C.HSnd{}}")

hRoseSum, hRoseSize, hRoseDepth :: RoseF Natural -> Natural
hRoseSum (RoseF n rs) = n + sum rs
hRoseSize (RoseF _ rs) = 1 + sum rs
hRoseDepth (RoseF _ rs) = 1 + maximum (0 : rs)

exprEval :: String
exprEval = byShape "C.HSnd{}" (byShape' (at2 "Sub") (byShape' (at2 "Div") (byShape' "C.HComp{C.HComp{C.HFst{}, C.HFold{C.HUnit{}, C.HId{}}}, C.HFst{}}" "C.HComp{C.HComp{C.HComp{C.HFst{}, C.HSnd{}}, C.HFold{C.HUnit{}, C.HId{}}}, C.HFst{}}")))
  where
    -- at (answers, shape): the shape's alternative, the answers beside it
    byShape' l r = "C.HComp{C.HCase{" ++ l ++ ", " ++ r ++ "}, C.HDist{}}"

hExprEval :: ExprF Natural -> Natural
hExprEval = \case
  LitF n -> n
  SubF a b -> a - b
  DivF a b -> a `div` b
  FstF a _ -> a
  SndF _ b -> b

-- GHC's answer: the number, or None{} where it throws ---------------------------

answer :: Natural -> IO (Maybe Natural)
answer x = either (\e -> const Nothing (e :: SomeException)) Just <$> try (evaluate x)

strict :: Maybe Natural -> String
strict = maybe "None{}" (\n -> "Some{C.HvNat{" ++ show n ++ "n}}")

lazy :: Maybe Natural -> String
lazy = maybe "None{}" (\n -> "Some{C.LvNat{" ++ show n ++ "n}}")

-- one value at one algebra: the lazy equation always, the strict one where
-- GHC's answer forces every child (st)
law :: (Recursive t, Foldable (Base t)) => String -> Bool -> (Base t t -> M) -> String -> (Base t Natural -> Natural) -> t -> IO ()
law name st sh alg h v = do
  a <- answer (cata h v)
  let r = showM (rose sh v)
  if st
    then do
      putStrLn ("def ghc." ++ name ++ "() -> {C.eval.h(C.HCata{" ++ alg ++ "}, " ++ r ++ ") == " ++ strict a ++ " : Maybe<&2, C.HV>}:")
      putStrLn "  {==}"
      putStrLn ""
    else pure ()
  putStrLn ("def ghc." ++ name ++ ".lz() -> {C.eval.lz(C.HCata{" ++ alg ++ "}, Some{C.lz(" ++ r ++ ")}) == " ++ lazy a ++ " : Maybe<&2, C.LV>}:")
  putStrLn "  {==}"
  putStrLn ""

-- the strict model where GHC answers and it does not: an error (section 9)
gap :: (Recursive t, Foldable (Base t)) => String -> (Base t t -> M) -> String -> t -> IO ()
gap name sh alg v = do
  putStrLn ("def ghc." ++ name ++ ".strict() -> {C.eval.h(C.HCata{" ++ alg ++ "}, " ++ showM (rose sh v) ++ ") == None{} : Maybe<&2, C.HV>}:")
  putStrLn "  {==}"
  putStrLn ""

main :: IO ()
main = do
  putStrLn "# generated by adj/CataGhc.hs (adj/int.zsh) from GHC; do not edit"
  putStrLn "# Each def: the model's catamorphism (Core.bend's HCata) of an algebra"
  putStrLn "# at a value's rose is GHC's answer for recursion-schemes' cata at that"
  putStrLn "# value: strict (eval.h) where GHC forces every child, lazy (eval.lz)"
  putStrLn "# always; None{}: GHC throws.  .strict: the strict model errs where"
  putStrLn "# GHC's laziness answers (PROPOSED.bend's section 9)."
  putStrLn ""
  putStrLn "import Base"
  putStrLn "import ./Core.bend as C"
  putStrLn ""
  let t1 = Leaf 7
      t2 = Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
      t3 = Node (Node (Leaf 4) (Leaf 0)) (Node (Leaf 5) (Node (Leaf 1) (Leaf 1)))
      t4 = Node (Leaf 5) (Node (Leaf 3) (Leaf 1))
      t5 = Node (Leaf 1) (Leaf 2)
  sequence_
    [ law ("tree.sum" ++ show i) True treeSh treeSum hTreeSum t | (i, t) <- zip [1 :: Int ..] [t1, t2, t3] ]
  sequence_
    [ law ("tree.depth" ++ show i) True treeSh treeDepth hTreeDepth t | (i, t) <- zip [1 :: Int ..] [t1, t2, t3] ]
  sequence_
    [ law ("tree.size" ++ show i) True treeSh treeSize hTreeSize t | (i, t) <- zip [1 :: Int ..] [t1, t3] ]
  law "tree.diff1" True treeSh treeDiff hTreeDiff t4
  law "tree.diff2" True treeSh treeDiff hTreeDiff t5
  let r1 = Rose 3 []
      r2 = Rose 1 [Rose 2 [], Rose 3 [Rose 4 [], Rose 5 [], Rose 6 []], Rose 7 []]
      r3 = Rose 0 [Rose 0 [Rose 0 [Rose 9 []]]]
  sequence_
    [ law ("rose.sum" ++ show i) True roseSh roseSum hRoseSum r | (i, r) <- zip [1 :: Int ..] [r1, r2, r3] ]
  sequence_
    [ law ("rose.size" ++ show i) True roseSh roseSize hRoseSize r | (i, r) <- zip [1 :: Int ..] [r1, r2, r3] ]
  sequence_
    [ law ("rose.depth" ++ show i) True roseSh roseDepth hRoseDepth r | (i, r) <- zip [1 :: Int ..] [r1, r2, r3] ]
  let e1 = Sub (Div (Lit 9) (Lit 2)) (Lit 3)
      e2 = Sub (Lit 1) (Lit 2)
      e3 = Div (Lit 4) (Sub (Lit 2) (Lit 2))
      e4 = Fst (Lit 1) (Sub (Lit 0) (Lit 1))
      e5 = Sub (Fst (Lit 8) (Lit 0)) (Div (Lit 6) (Snd (Lit 9) (Lit 3)))
      e6 = Snd (Sub (Lit 0) (Lit 1)) (Lit 2)
  law "expr.eval1" True exprSh exprEval hExprEval e1
  law "expr.eval2" True exprSh exprEval hExprEval e2
  law "expr.eval3" True exprSh exprEval hExprEval e3
  law "expr.eval4" False exprSh exprEval hExprEval e4
  gap "expr.eval4" exprSh exprEval e4
  law "expr.eval5" True exprSh exprEval hExprEval e5
  law "expr.eval6" False exprSh exprEval hExprEval e6
  gap "expr.eval6" exprSh exprEval e6
