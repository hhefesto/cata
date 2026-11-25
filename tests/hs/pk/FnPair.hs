-- a function in what a call answers, run more than once (Expand's
-- udtSlots and listAssignmentSlots)
module FnPair where

data T = Lst [T] | Let [(String, T)] T | Lam String T | Var String | Num Int
  deriving (Eq, Show)

slotsE :: String -> T -> Either String ([T], T -> T)
slotsE name = go where
  go (Lst xs) = Right (xs, id)
  go (Let bs inner) = do
    (xs, wrap) <- go inner
    pure (xs, \e -> Let bs (wrap e))
  go other = Left (name ++ " not a list: " ++ show other)

slotsM :: T -> Maybe ([T], T -> T)
slotsM = go where
  go (Lst xs) = Just (xs, id)
  go (Let bs inner) = do
    (xs, wrap) <- go inner
    pure (xs, \e -> Let bs (wrap e))
  go (Lam v inner) = do
    (xs, wrap) <- go inner
    pure (xs, \e -> Lam v (wrap e))
  go _ = Nothing

assign :: [String] -> T -> Either String [(String, T)]
assign names body = case slotsM body of
  Just (slots, wrap)
    | length names == length slots -> Right (zipWith (\n s -> (n, wrap s)) names slots)
    | otherwise -> Left "arity"
  Nothing -> Right (zipWith (\n i -> (n, Num i)) names [0 ..])

udt :: String -> [String] -> T -> Either String [(String, T)]
udt tn names body = case body of
  Lam h inner -> do
    (slots, wrap) <- slotsE tn inner
    let core = take 1 slots
        rest = drop 1 slots
        wrapped = Let [(tn, Var h)] (wrap (Lst core))
        hoist n s = (n, Let [(h, Num 1)] (wrap s))
    if null names then Left "no names" else pure ((tn, Lam h wrapped) : zipWith hoist names rest)
  _ -> Right (zipWith (\n i -> (n, Num i)) names [0 ..])

exAssign :: Int -> Either String [(String, T)]
exAssign n = assign ["a", "b"] (Lam "x" (Let [("y", Num n)] (Lst [Var "x", Num n])))

exUdt :: Int -> Either String [(String, T)]
exUdt n = udt "T" (if n < 0 then [] else ["p", "q"]) (if n > 3 then Lam "h" (Var "z") else Lam "h" (Let [("k", Num n)] (Lst [Num 1, Var "h", Num 3])))
