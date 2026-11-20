module Dig where

-- cata's Digest SHA256: crypton's hash in Bend (SHA-256), its show (hex),
-- its order (bytes), a Map keyed by digests, utf8-string's encode

import Codec.Binary.UTF8.String (encode)
import Crypto.Hash (Digest, SHA256, hash)
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.Map as Map

digestOf :: String -> Digest SHA256
digestOf = hash . BS.pack . encode

hexOf :: String -> String
hexOf s = show (digestOf s)

sameDigest :: String -> String -> Bool
sameDigest a b = digestOf a == digestOf b

orderOf :: String -> String -> Ordering
orderOf a b = compare (digestOf a) (digestOf b)

firstBytes :: String -> [Int]
firstBytes s = map fromIntegral (take 4 (BA.unpack (digestOf s)))

table :: [String] -> [(String, Int)]
table xs = map (\(d, n) -> (show d, n)) (Map.toList (Map.fromListWith (+) [(digestOf x, 1) | x <- xs]))
