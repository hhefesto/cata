module PkTyE where

-- bytes, digests and rationals in laws
import Crypto.Hash (Digest, SHA256)
import qualified Data.Map as M
import Data.Word (Word8)

data R = R { rq :: Rational, rb :: [Word8], rd :: Maybe (Digest SHA256) }

scale :: Rational -> Rational -> Rational
scale a b = a * b + 1

bump :: Word8 -> [Word8] -> [Word8]
bump w = map (\x -> if x < w then w else x)

pick :: Digest SHA256 -> Digest SHA256 -> Digest SHA256
pick a b = if a < b then a else b

rows :: M.Map Int Rational -> [Rational]
rows = M.elems

byName :: M.Map (Digest SHA256) Int -> Digest SHA256 -> Int
byName m d = M.findWithDefault 0 d m
