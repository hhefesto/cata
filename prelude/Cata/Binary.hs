-- | cata's model of what telomare's Artifact codec uses of binary-0.8.9.3
-- (Data.Binary.Get, Data.Binary.Put), utf8-string-1.0.2
-- (Data.ByteString.UTF8), crypton (Crypto.Hash, Data.ByteArray) and
-- filepath (System.FilePath), written in the Haskell cata takes, so no new
-- monad in Fold: a ByteString (strict or lazy) is a list of Word8, as cata
-- has it everywhere; PutM is a Writer of the bytes (WriterT [Word8]
-- Identity); Get an ExceptT String over a State of the bytes left and how
-- many were read. Spec's sp.bin.* maps binary's types and names to these;
-- tests/hs/bin checks this model against the libraries themselves.
--
-- binary's behaviour kept: a read past the end fails with "not enough
-- bytes" and consumes nothing (getLazyByteString 4 on 3 bytes leaves them
-- all); a failure keeps the input and offset where it happened
-- (runGetOrFail's Left triple); getLazyByteString of a count <= 0 reads
-- nothing; the Int64s are two's complement, little-endian.
module Cata.Binary where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, get, put, runState)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriter, writer)
import Data.Functor.Identity (Identity)
import Data.Int (Int64)
import Data.Char (chr)
import Data.Word (Word8)




-- | Data.Binary.Get

-- | The first k bytes and the rest, if there are k (none when k <= 0).
takeBytes :: [Word8] -> Int64 -> Maybe ([Word8], [Word8])
takeBytes bs k =
  if k <= 0
    then Just ([], bs)
    else case bs of
      [] -> Nothing
      b : rest -> case takeBytes rest (k - 1) of
        Nothing -> Nothing
        Just (xs, r) -> Just (b : xs, r)

getLazyByteString :: Int64 -> ExceptT String (State ([Word8], Int64)) [Word8]
getLazyByteString k = do
  st <- get
  case st of
    (bs, n) -> case takeBytes bs k of
      Nothing -> throwError "not enough bytes"
      Just (xs, rest) -> do
        put (rest, n + fromIntegral (length xs))
        pure xs

getWord8 :: ExceptT String (State ([Word8], Int64)) Word8
getWord8 = do
  st <- get
  case st of
    (bs, n) -> case bs of
      [] -> throwError "not enough bytes"
      b : rest -> do
        put (rest, n + 1)
        pure b

-- | The number little-endian bytes write, unsigned. (Never 2^64 itself: the
-- law check counts a Nat, so a small Int64 must cost its size, not 2^64.)
leValue :: [Word8] -> Integer
leValue bs = case bs of
  [] -> 0
  b : rest -> toInteger b + 256 * leValue rest

-- | A byte's bits flipped, 255 - b.
flipByte :: Word8 -> Word8
flipByte b = fromIntegral (255 - fromIntegral b :: Int)

-- | Whether the last (highest) byte has its top bit.
isNegative :: [Word8] -> Bool
isNegative bs = case bs of
  [] -> False
  b : rest -> case rest of
    [] -> (fromIntegral b :: Int) >= 128
    _ -> isNegative rest

-- | The Int64 its 8 bytes write, two's complement: a negative n is
-- -1 - (the number n's flipped bytes write).
int64Of :: [Word8] -> Int64
int64Of bs = fromInteger (if isNegative bs then -1 - leValue (map flipByte bs) else leValue bs)

getInt64le :: ExceptT String (State ([Word8], Int64)) Int64
getInt64le = fmap int64Of (getLazyByteString 8)

failGet :: String -> ExceptT String (State ([Word8], Int64)) a
failGet e = throwError e

runGetOrFail :: ExceptT String (State ([Word8], Int64)) a -> [Word8] -> Either ([Word8], Int64, String) ([Word8], Int64, a)
runGetOrFail g bs = case runState (runExceptT g) (bs, 0) of
  (Left e, (rest, n)) -> Left (rest, n, e)
  (Right a, (rest, n)) -> Right (rest, n, a)

-- | Data.Binary.Put

putWord8 :: Word8 -> WriterT [Word8] Identity ()
putWord8 b = writer ((), [b])

putLazyByteString :: [Word8] -> WriterT [Word8] Identity ()
putLazyByteString bs = writer ((), bs)

-- | A natural's lowest byte.
lowByte :: Integer -> Word8
lowByte v = fromIntegral (v `mod` 256)

-- | The 8 little-endian bytes of a number in 0 .. 2^63 - 1.
bytes8 :: Integer -> [Word8]
bytes8 v0 =
  let v1 = v0 `div` 256
      v2 = v1 `div` 256
      v3 = v2 `div` 256
      v4 = v3 `div` 256
      v5 = v4 `div` 256
      v6 = v5 `div` 256
      v7 = v6 `div` 256
   in [lowByte v0, lowByte v1, lowByte v2, lowByte v3, lowByte v4, lowByte v5, lowByte v6, lowByte v7]

putInt64le :: Int64 -> WriterT [Word8] Identity ()
putInt64le x =
  let v = toInteger x
   in writer ((), if v >= 0 then bytes8 v else map flipByte (bytes8 (-1 - v)))

runPut :: WriterT [Word8] Identity () -> [Word8]
runPut m = case runWriter m of
  (_, w) -> w

-- | Data.ByteString.Lazy.length
byteLength :: [Word8] -> Int64
byteLength bs = fromIntegral (length bs)

-- | GHC.Word's show at Word8
showWord8 :: Word8 -> String
showWord8 b = show (toInteger b)

-- | Data.ByteString.UTF8.toString (utf8-string's decode, its replacement
-- character and how many bytes each bad sequence takes)

replacement :: Char
replacement = '\xfffd'

-- | Whether a byte follows in a sequence (10xxxxxx).
follows :: Word8 -> Bool
follows r = fromIntegral r >= (128 :: Int) && fromIntegral r < (192 :: Int)

-- | acc's six bits more from a follower.
combine :: Int -> Word8 -> Int
combine acc r = acc * 64 + fromIntegral r `mod` 64

-- | One def, each call on a part of its list (no helpers calling it back).
utf8Decode :: [Word8] -> String
utf8Decode bs = case bs of
  [] -> []
  b : rest ->
    let c = fromIntegral b :: Int
     in if c < 128
          then chr c : utf8Decode rest
          else if c < 192 || c >= 248
            then replacement : utf8Decode rest
            else case rest of
              [] -> replacement : utf8Decode rest
              r1 : rest1 ->
                if not (follows r1)
                  then replacement : utf8Decode rest
                  else if c < 224
                    then
                      let d = combine (c `mod` 32) r1
                       in if d >= 128 then chr d : utf8Decode rest1 else replacement : utf8Decode rest
                    else case rest1 of
                      [] -> replacement : utf8Decode rest1
                      r2 : rest2 ->
                        if not (follows r2)
                          then replacement : utf8Decode rest1
                          else if c < 240
                            then
                              let d = combine (combine (c `mod` 16) r1) r2
                               in if (d >= 2048 && d < 55296) || (d > 57343 && d < 65534) then chr d : utf8Decode rest2 else replacement : utf8Decode rest2
                            else case rest2 of
                              [] -> replacement : utf8Decode rest2
                              r3 : rest3 ->
                                if not (follows r3)
                                  then replacement : utf8Decode rest2
                                  else
                                    let d = combine (combine (combine (c `mod` 8) r1) r2) r3
                                     in if d >= 65536 && d < 1114112 then chr d : utf8Decode rest3 else replacement : utf8Decode rest3

-- | System.FilePath.Posix.takeExtension: from the last '.' of the file
-- name (after the last '/'), "" when it has none
takeExtension :: String -> String
takeExtension p = extOf (fileName p)

fileName :: String -> String
fileName p = case p of
  [] -> []
  c : rest -> case fileName rest of
    f -> if hasSlash rest then f else if c == '/' then rest else p

hasSlash :: String -> Bool
hasSlash s = case s of
  [] -> False
  c : rest -> c == '/' || hasSlash rest

extOf :: String -> String
extOf f = case f of
  [] -> []
  c : rest -> if hasDot rest then extOf rest else if c == '.' then f else []

hasDot :: String -> Bool
hasDot s = case s of
  [] -> False
  c : rest -> c == '.' || hasDot rest
