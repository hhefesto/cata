-- IO as the state of its console and files: Driver's loop, an accumulator
-- shown or kept, a file written and read
module InOut where

import Control.Monad (forM_, unless, void, when)

printAcc :: String -> String -> IO String
printAcc _ out = putStrLn out >> pure ""

keepAcc :: String -> String -> IO String
keepAcc acc out = pure $ if acc == "" then out else acc <> "\n" <> out

loop :: (Int -> (String, Maybe Int)) -> (String -> String -> IO String) -> String -> [String] -> Int -> IO (Int, String)
loop f accum acc0 inputs0 n0 = go 0 acc0 inputs0 n0 where
  go k acc inputs n = do
    let (out, next) = f n
    acc' <- accum acc out
    case next of
      Nothing -> pure (k, acc' <> "\ndone")
      Just m -> do
        (line, rest) <- case inputs of
          [] -> (\l -> (l, [])) <$> getLine
          i : is -> pure (i, is)
        go (k + 1) acc' rest (m - length line - 1)

stepOf :: Int -> (String, Maybe Int)
stepOf n = (show n, if n > 0 then Just n else Nothing)

runShown :: Int -> IO ()
runShown n = void $ loop stepOf printAcc "" [] n

runKept :: [String] -> Int -> IO String
runKept is n = snd <$> loop stepOf keepAcc "" is n

save :: FilePath -> [Int] -> IO ()
save p xs = writeFile p (unlines (map show xs))

load :: FilePath -> IO Int
load p = do
  s <- readFile p
  pure (length (lines s))

report :: [Int] -> IO ()
report xs = do
  forM_ xs $ \x -> when (x > 1) $ print x
  unless (null xs) $ putStr "end\n"

roundTrip :: FilePath -> [Int] -> IO Int
roundTrip p xs = save p xs >> load p

echo :: IO ()
echo = interact reverse

session :: IO ()
session = do
  report [1, 2, 3]
  n <- roundTrip "f" [4, 5]
  print (n, "x")
  echo
