-- adj/gen/FragRt.hs: GHC's answer at a program of the fragment against the
-- model's (Gen.bend's rows): same, both errors, the model erring where
-- GHC's laziness answers (lazier), or different (printed).
module FragRt (r, done) where

import Control.Exception (SomeException, evaluate, try)
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

counts :: IORef (Int, Int, Int, Int)
counts = unsafePerformIO (newIORef (0, 0, 0, 0))
{-# NOINLINE counts #-}

r :: (Eq a, Show a) => String -> Maybe a -> a -> IO ()
r n m x = do
  g <- try (evaluate (let s = show x in length s `seq` s)) :: IO (Either SomeException String)
  case (m, g) of
    (Just v, Right s)
      | show v == s -> bump (\(a, b, c, d) -> (a + 1, b, c, d))
      | otherwise -> diff (show v) s
    (Nothing, Left _) -> bump (\(a, b, c, d) -> (a, b + 1, c, d))
    (Nothing, Right _) -> bump (\(a, b, c, d) -> (a, b, c + 1, d))
    (Just v, Left e) -> diff (show v) ("error: " ++ show e)
  where
    bump f = modifyIORef' counts f
    diff v s = putStrLn ("DIFFER " ++ n ++ ": model " ++ v ++ ", GHC " ++ s) >> bump (\(a, b, c, d) -> (a, b, c, d + 1))

done :: IO ()
done = do
  (a, b, c, d) <- readIORef counts
  putStrLn ("same " ++ show a ++ ", both err " ++ show b ++ ", GHC answers where the strict model errs " ++ show c ++ ", differ " ++ show d)
