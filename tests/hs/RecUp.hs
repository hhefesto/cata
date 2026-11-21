module RecUp where

-- Shapes from telomare: a record update whose new value GHC binds to a
-- local named as the field, then a call of the field's selector (EAL's
-- freshInt); a record update inside a tuple (Fast's tickApply); C {} at a
-- constructor without field names (IC's valueKind); maybe at a function
-- (EAL's walkTau, at a State action).

data Meter = Meter { applies :: Int, gates :: Int }

data Kind = KZero | KRef Int Int | KPair

bump :: Meter -> (Meter, Int)
bump m = (m { applies = applies m + 1 }, applies m)

tick :: (Meter, Int) -> (Meter, Int)
tick (m, f) = (m { gates = gates m + 1 }, f)

isRef :: Kind -> Bool
isRef KRef {} = True
isRef _ = False

adder :: Maybe Int -> Int -> Int
adder = maybe id (+)

ex1 :: Int -> Int
ex1 n = case bump (Meter n 0) of
  (m, a) -> applies m + a

ex2 :: Int -> Int
ex2 n = case tick (Meter 0 n, n) of
  (m, f) -> gates m + f

ex3 :: Int -> Int
ex3 n = (if isRef (KRef n n) then 1 else 0) + (if isRef KZero then 10 else 0)

ex4 :: Int -> Int
ex4 n = adder (Just n) 3 + adder Nothing n
