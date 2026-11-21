module LcPat where

-- a comprehension's generator whose pattern fails inside a tuple (Driver's
-- [ (h, g) | (h, Right g) <- Map.toList (ealGuidance lr) ]): the elements
-- it does not match are skipped

rightsOf :: [(Int, Either String Int)] -> [(Int, Int)]
rightsOf xs = [(h, g) | (h, Right g) <- xs]

sumJusts :: [(Int, Maybe Int)] -> [Int]
sumJusts xs = [a + b | (a, Just b) <- xs]

trues :: [(Int, (Bool, Int))] -> [Int]
trues xs = [n + k | (k, (True, n)) <- xs]

-- a literal inside a tuple
zeros :: [(Int, Int)] -> [Int]
zeros xs = [b | (0, b) <- xs]
