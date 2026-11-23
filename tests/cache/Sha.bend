import Base
import ../../bend/a2b/Sys.bend as S
import ../../bend/Cache.bend as C

# sha FILE...: each file's SHA-256 by bend/Cache.bend, as sha256sum prints
# it (tests/cache/sha.zsh compares the two); then `put`/`get` of each
# file's bytes under its key in $CACHE_TEST (an entry read back whole), and
# a cut entry read back as none
def sha.one(+f: String) -> IO(Unit):
  do IO<Unit>:
    +bs : List<&2, U32> <- S.read(f)
    IO.print(S.str(C.ch.hex(C.ch.sha(bs))) ++ "  " ++ f)

def sha.all(fs: List<&1, String>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        sha.one(f)
        sha.all(t)

def sha.same(+a: Maybe<&2, List<&2, U32>>, +b: List<&2, U32>) -> String:
  match a:
    case Some{+x}:
      Bool.pick(String, S.eq(x, b), "same", "DIFFERENT")
    case None{}:
      "NONE"

def sha.none(a: Maybe<&2, List<&2, U32>>) -> String:
  match a:
    case Some{x}:
      "SOME"
    case None{}:
      "none"

def sha.cut(+bs: List<&2, U32>) -> List<&2, U32>:
  +e = C.ch.entry(bs)
  List.take(&2, U32, e, Nat.sub(List.length(&2, U32, e), 1n))

def sha.round.k(+dir: String, +f: String, +bs: List<&2, U32>, +k: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    C.ch.put(dir, k, bs)
    +got : Maybe<&2, List<&2, U32>> <- C.ch.get(dir, k)
    S.write(C.ch.file(dir, k), sha.cut(bs))
    +cut : Maybe<&2, List<&2, U32>> <- C.ch.get(dir, k)
    IO.print("round " ++ sha.same(got, bs) ++ " cut " ++ sha.none(cut) ++ "  " ++ f)

def sha.round(+dir: String, +f: String) -> IO(Unit):
  do IO<Unit>:
    +bs : List<&2, U32> <- S.read(f)
    sha.round.k(dir, f, bs, C.ch.key([S.b("test"), bs]))

def sha.rounds(+dir: String, fs: List<&1, String>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> t:
      do IO<Unit>:
        sha.round(dir, f)
        sha.rounds(dir, t)

def sha.args(xs: List<&1, String>) -> List<&1, String>:
  match xs:
    case _ <> t:
      t
    case Nil{}:
      Nil{}

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    again : List<String> <- IO.args()
    +dir : String <- S.env("CACHE_TEST", "")
    sha.all(sha.args(argv))
    sha.rounds(dir, sha.args(again))
