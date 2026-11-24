-- shows at a type of the package's own (a derived Show, a newtype's record) and
-- inside a Show1 instance (IR.Base's StuckF and LamTermF)
{-# LANGUAGE LambdaCase, DeriveFunctor #-}
module ShowOwn where

import Data.Functor.Classes
import Data.Fix (Fix (..))

newtype FI = FI { unFI :: Int } deriving (Eq, Ord, Show)
data LTy l = Open l | Closed l | LetB Int l deriving (Eq, Show, Ord)

data SF x = DeferSF FI x | EnvSF | LeftSF x deriving (Eq, Show, Functor)
data LF l v x = VarF v | AppF x x | LamF l x deriving (Eq, Show, Functor)

instance Show1 SF where
  liftShowsPrec sp _ _ = \case
    DeferSF fi x -> shows "DeferSF " . shows fi . shows " (" . sp 0 x . shows ")"
    EnvSF -> shows "EnvSF"
    LeftSF x -> shows "LeftSF (" . sp 0 x . shows ")"

instance (Show l, Show v) => Show1 (LF l v) where
  liftShowsPrec sp _ _ = \case
    VarF s -> showString "VarUPF " . shows s
    AppF f x -> showString "AppUPF " . sp 11 f . showChar ' ' . sp 11 x
    LamF var body -> showString "LamUPF " . shows var . showChar ' ' . sp 11 body

showFI :: FI -> String
showFI fi = shows fi ""

showLT :: LTy () -> String
showLT l = shows l ""

showSF :: SF String -> String
showSF x = showsPrec1 0 x ""

showLF :: LF (LTy ()) Int String -> String
showLF x = showsPrec1 0 x ""

showFixSF :: Fix SF -> String
showFixSF x = show x

showFixLF :: Fix (LF (LTy ()) Int) -> String
showFixLF x = show x

-- Show at Fix inside a list of pairs (UnprocessedParsedTermF's derived Show)
data CaseF p r = CaseN r [(p, r)] | LitN Int
  deriving (Eq, Show, Functor)

instance Show p => Show1 (CaseF p) where
  liftShowsPrec sp _ d c = case c of
    CaseN s as -> showParen (d > 10) (showString "CaseN " . sp 11 s . shows (length as))
    LitN n -> showString "LitN " . shows n

showCase :: CaseF (Fix SF) Int -> String
showCase c = show c

exCase :: Int -> Int -> String
exCase a b = showCase (CaseN a [(Fix (LeftSF (Fix EnvSF)), b), (Fix (DeferSF (FI b) (Fix EnvSF)), a)])
