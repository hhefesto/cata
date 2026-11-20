module Shows where

data Color = Red | Green | Blue deriving (Eq, Show)

data Shape = Circle Int | Rect Int Int | Named String Color deriving (Eq, Show)

data Pt = Pt { px :: Int, py :: Int } deriving (Eq, Show)

newtype Wrap = Wrap Shape deriving (Eq, Show)

data Box = Box (Maybe Int) [Bool] deriving (Eq, Show)

describe :: Color -> String
describe = show

shape :: Shape -> String
shape = show

point :: Pt -> String
point p = show p

wrapped :: Wrap -> String
wrapped = show

shapes :: [Shape] -> String
shapes = show

box :: Box -> String
box = show

nums :: [Int] -> String
nums = show

maybeInt :: Maybe Int -> String
maybeInt = show

quoted :: String -> String
quoted = show

ch :: Char -> String
ch = show

inParens :: Int -> Shape -> String
inParens d s = showsPrec d s ""

label :: Int -> String
label n = "n = " ++ show n ++ "!"
