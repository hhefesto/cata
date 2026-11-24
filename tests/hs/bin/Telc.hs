{-# LANGUAGE LambdaCase #-}
-- The Binary model's test (prelude/Cata/Binary.hs): binary's Get and Put,
-- utf8-string and filepath the way telomare's Artifact codec uses them
-- (its putInt', getString, putMaybe, getList, a tagged sum read back), run
-- by GHC with the real libraries against cata's translation, which runs the
-- model. A package with Cata/Binary.hs (spec maps the libraries to it):
-- tests/hs/bin/run.zsh.
module Telc where

import Data.Binary.Get (Get, getInt64le, getLazyByteString, getWord8,
                        runGetOrFail)
import Data.Binary.Put (Put, putInt64le, putLazyByteString, putWord8, runPut)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.UTF8 as UTF8
import System.FilePath (takeExtension)

putInt' :: Int -> Put
putInt' = putInt64le . fromIntegral

getInt' :: Get Int
getInt' = fromIntegral <$> getInt64le

putString :: String -> Put
putString s = do
  let bytes = BL.fromStrict (UTF8.fromString s)
  putInt' (fromIntegral (BL.length bytes))
  putLazyByteString bytes

getString :: Get String
getString = do
  n <- getInt'
  UTF8.toString . BL.toStrict <$> getLazyByteString (fromIntegral n)

putMaybe :: (a -> Put) -> Maybe a -> Put
putMaybe p = \case
  Nothing -> putWord8 0
  Just x -> putWord8 1 >> p x

getMaybe :: Get a -> Get (Maybe a)
getMaybe g = getWord8 >>= \case
  0 -> pure Nothing
  _ -> Just <$> g

getList :: Get a -> Get [a]
getList g = getInt' >>= \n -> mapM (const g) [1 .. n]

data Shape = Dot | Box Int Int | Named String (Maybe Int)
  deriving (Eq, Show)

putShape :: Shape -> Put
putShape = \case
  Dot -> putWord8 0
  Box w h -> putWord8 1 >> putInt' w >> putInt' h
  Named s m -> putWord8 2 >> putString s >> putMaybe putInt' m

getShape :: Get Shape
getShape = getWord8 >>= \case
  0 -> pure Dot
  1 -> Box <$> getInt' <*> getInt'
  2 -> Named <$> getString <*> getMaybe getInt'
  n -> fail $ "unknown shape tag " <> show n

bytes :: [Int] -> BL.ByteString
bytes = BL.pack . map fromIntegral

-- runGetOrFail's answer, the offsets as Int
run :: Get a -> [Int] -> Either ([Int], Int, String) ([Int], Int, a)
run g xs = case runGetOrFail g (bytes xs) of
  Left (r, n, e) -> Left (map fromIntegral (BL.unpack r), fromIntegral n, e)
  Right (r, n, a) -> Right (map fromIntegral (BL.unpack r), fromIntegral n, a)

encShape :: Shape -> [Int]
encShape s = map fromIntegral (BL.unpack (runPut (putShape s)))

roundShape :: Shape -> Either String Shape
roundShape s = case runGetOrFail getShape (runPut (putShape s)) of
  Left (_, _, e) -> Left e
  Right (_, _, x) -> Right x

decShape :: [Int] -> Either ([Int], Int, String) ([Int], Int, Shape)
decShape = run getShape

decString :: [Int] -> Either ([Int], Int, String) ([Int], Int, String)
decString = run getString

decInts :: [Int] -> Either ([Int], Int, String) ([Int], Int, [Int])
decInts = run (getList getInt')

decWord :: [Int] -> Either ([Int], Int, String) ([Int], Int, Int)
decWord = run (fromIntegral <$> getWord8)

decTwo :: [Int] -> Either ([Int], Int, String) ([Int], Int, [Int])
decTwo = run (getWord8 >> (map fromIntegral . BL.unpack <$> getLazyByteString 4))

encInt :: Int -> [Int]
encInt n = map fromIntegral (BL.unpack (runPut (putInt' n)))

utf8 :: [Int] -> String
utf8 xs = UTF8.toString (BL.toStrict (bytes xs))

isTelc :: String -> Bool
isTelc = (== ".telc") . takeExtension
