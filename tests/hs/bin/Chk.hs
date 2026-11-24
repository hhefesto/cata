-- The model (prelude/Cata/Binary.hs) against binary, utf8-string and filepath
-- themselves: runghc -i../../../prelude Chk.hs, with a GHC that has them; each
-- line says how many runs differ (0).
import qualified Cata.Binary as M
import Data.Binary.Get
import Data.Binary.Put
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.UTF8 as UTF8
import Data.Int (Int64)
import Data.Word (Word8)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State)
import qualified System.FilePath as FP

alpha :: [Word8]
alpha = [0, 1, 0x41, 0x7f, 0x80, 0x9f, 0xbf, 0xc0, 0xc2, 0xdf, 0xe0, 0xed, 0xef, 0xf0, 0xf4, 0xf7, 0xf8, 0xff]

upto :: Int -> [[Word8]]
upto 0 = [[]]
upto n = [] : [b : t | b <- alpha, t <- upto (n - 1)]

real :: Get a -> [Word8] -> Either ([Word8], Int64, String) ([Word8], Int64, a)
real g bs = case runGetOrFail g (BL.pack bs) of
  Left (r, n, e) -> Left (BL.unpack r, n, e)
  Right (r, n, a) -> Right (BL.unpack r, n, a)

progs :: [(String, Get [Int64], ExceptT String (State ([Word8], Int64)) [Int64])]
progs =
  [ ("w8", fmap (\b -> [fromIntegral b]) getWord8, fmap (\b -> [fromIntegral b]) M.getWord8)
  , ("w8w8", (\a b -> [fromIntegral a, fromIntegral b]) <$> getWord8 <*> getWord8, (\a b -> [fromIntegral a, fromIntegral b]) <$> M.getWord8 <*> M.getWord8)
  , ("lbs2", map fromIntegral . BL.unpack <$> getLazyByteString 2, map fromIntegral <$> M.getLazyByteString 2)
  , ("w8lbs3", getWord8 >> (map fromIntegral . BL.unpack <$> getLazyByteString 3), M.getWord8 >> (map fromIntegral <$> M.getLazyByteString 3))
  , ("lbsneg", map fromIntegral . BL.unpack <$> getLazyByteString (-2), map fromIntegral <$> M.getLazyByteString (-2))
  , ("w8fail", getWord8 >> fail "boom", M.getWord8 >> M.failGet "boom")
  , ("i64", (: []) <$> getInt64le, (: []) <$> M.getInt64le)
  , ("w8i64", (\a b -> [fromIntegral a, b]) <$> getWord8 <*> getInt64le, (\a b -> [fromIntegral a, b]) <$> M.getWord8 <*> M.getInt64le)
  ]

main :: IO ()
main = do
  let ins = upto 3 ++ [replicate 8 255, [1 .. 9], replicate 9 0x80, [254, 255, 255, 255, 255, 255, 255, 127], [0, 0, 0, 0, 0, 0, 0, 128]]
      bad = [(n, bs) | (n, g, m) <- progs, bs <- ins, real g bs /= M.runGetOrFail m bs]
  putStrLn ("get: " ++ show (length progs * length ins) ++ " runs, differ " ++ show (length bad) ++ " " ++ show (take 3 bad))
  let ns = [0, 1, -1, -2, 255, 256, 2 ^ 63 - 1, -(2 ^ 63), 123456789012345, -98765432109876] :: [Int64]
      pbad = [n | n <- ns, BL.unpack (runPut (putInt64le n >> putWord8 7 >> putLazyByteString (BL.pack [1, 2]))) /= M.runPut (M.putInt64le n >> M.putWord8 7 >> M.putLazyByteString [1, 2])]
  putStrLn ("put: " ++ show (length ns) ++ " runs, differ " ++ show pbad)
  let u4 = upto 4
      ubad = [bs | bs <- u4, UTF8.toString (BL.toStrict (BL.pack bs)) /= M.utf8Decode bs]
  putStrLn ("utf8: " ++ show (length u4) ++ " runs, differ " ++ show (length ubad) ++ " " ++ show (take 3 ubad))
  let ps = ["", "a", "a.b", ".b", "a.", "a/b.c", "a.b/c", "a/.b", "a.b.c", "/x/y.z/", "x/y.tar.gz", "..", "a/..", "./a.telc"]
      fbad = [p | p <- ps, FP.takeExtension p /= M.takeExtension p]
  putStrLn ("takeExtension: " ++ show (length ps) ++ " runs, differ " ++ show fbad)
  putStrLn ("show Word8: differ " ++ show [b | b <- [0 .. 255 :: Word8], show b /= M.showWord8 b])
