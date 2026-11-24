module FunField where

-- data types that hold functions are Types in Bend, used at most once
-- (Fold's fd.kd): a State and a parser written out, a type that holds one,
-- a list and a Maybe of one

newtype State s a = State { runState :: s -> (a, s) }

unit :: a -> State s a
unit a = State (\s -> (a, s))

bind :: State s a -> (a -> State s b) -> State s b
bind (State m) k = State (\s -> case m s of (a, s') -> runState (k a) s')

getS :: State s s
getS = State (\s -> (s, s))

putS :: s -> State s ()
putS s = State (\_ -> ((), s))

tick :: Int -> State Int Int
tick k = bind getS (\n -> bind (putS (n + k)) (\_ -> unit n))

ticks :: Int -> Int -> (Int, Int)
ticks k n = runState (bind (tick k) (\a -> bind (tick k) (\b -> unit (a + b)))) n

newtype Parser a = Parser (String -> Maybe (a, String))

parse :: Parser a -> String -> Maybe (a, String)
parse (Parser p) s = p s

item :: Parser Char
item = Parser (\s -> case s of { [] -> Nothing; c : t -> Just (c, t) })

orElse :: Parser a -> a -> Parser a
orElse (Parser p) d = Parser (\s -> case p s of { Nothing -> Just (d, s); Just r -> Just r })

firstChar :: String -> Maybe (Char, String)
firstChar s = parse (orElse item '?') s

data Rule = Rule String (Int -> Int)

apply :: Rule -> Int -> Int
apply (Rule _ f) n = f n

rule :: Int -> Rule
rule k = if k > 1 then Rule "big" (\n -> n + k) else Rule "small" (\n -> n * 2)

useRule :: Int -> Int -> Int
useRule k n = apply (rule k) n

data Entry = Entry Int Rule

entry :: Int -> Int -> Int
entry k n = case Entry k (rule k) of Entry j r -> j + apply r n

maybeRule :: Int -> Maybe Rule
maybeRule k = if k > 0 then Just (rule k) else Nothing

runMaybe :: Int -> Int -> Int
runMaybe k n = case maybeRule k of { Nothing -> n; Just r -> apply r n }
