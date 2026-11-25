-- shows at a list and a Maybe of an earlier module's types (Surface's
-- LocatedName), and of this one's
module UseShow where

import ImpShow

data T = A Int | B [T]
  deriving (Eq, Show)

line :: [Name] -> ShowS
line ns = showString "names " . shows ns . showChar ' ' . shows (map (\(Name (l, _)) -> Just l) ns)

own :: [T] -> Maybe T -> String
own ts m = shows ts (shows m (show (ts, 1 :: Int)))

exLine :: Int -> String
exLine n = line [Name (Loc n, "a"), Name (Gen "g" (Just (Loc 2)), "b")] "."

exOwn :: Int -> String
exOwn n = own [A n, B [A 2, B []]] (if n > 2 then Nothing else Just (A (n - 1)))
