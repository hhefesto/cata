import Base
import ./a2b/Sys.bend as S

# Cache: the answers of cata's oracles (bend's check, GHC's interpreter)
# kept under the digest of everything they read, so a run asks each oracle
# only what no run asked before (PLAN.md, "cata as a functor").
#
# A key is the SHA-256 of its parts, each framed as its length, a colon and
# its bytes, so two lists of parts share a key only when they are equal
# (up to a SHA-256 collision). An entry is the file DIR/KEY holding
#
#   cata-cache 1 N
#   N bytes
#
# and a file cut short (a full disk, a run writing it while another reads)
# is no entry: its length is not N. Nothing here decides what a key holds;
# Law.bend names the parts (bend's identity, the text, its imports'
# digests; GHC's, the script, the sources).
#
# Every def is prefixed `ch.`.

# SHA-256 (FIPS 180-4) -----------------------------------------------------
# The fold's own (Fold.bend's HsPrelude text, crypton's Digest SHA256),
# here as code; its answers are sha256sum's (tests/cache/sha.zsh).

def ch.sha.rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def ch.sha.ch(+x: U32, y: U32, z: U32) -> U32:
  U32.xor(U32.and(x, y), U32.and(U32.not(x), z))

def ch.sha.maj(+x: U32, +y: U32, +z: U32) -> U32:
  U32.xor(U32.xor(U32.and(x, y), U32.and(x, z)), U32.and(y, z))

def ch.sha.bs0(+x: U32) -> U32:
  U32.xor(U32.xor(ch.sha.rotr(x, 2n), ch.sha.rotr(x, 13n)), ch.sha.rotr(x, 22n))

def ch.sha.bs1(+x: U32) -> U32:
  U32.xor(U32.xor(ch.sha.rotr(x, 6n), ch.sha.rotr(x, 11n)), ch.sha.rotr(x, 25n))

def ch.sha.ss0(+x: U32) -> U32:
  U32.xor(U32.xor(ch.sha.rotr(x, 7n), ch.sha.rotr(x, 18n)), U32.shrn(x, 3n))

def ch.sha.ss1(+x: U32) -> U32:
  U32.xor(U32.xor(ch.sha.rotr(x, 17n), ch.sha.rotr(x, 19n)), U32.shrn(x, 10n))

def ch.sha.k() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221, 3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580, 3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

def ch.sha.h0() -> List<&2, U32>:
  [1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225]

def ch.sha.nth(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case x <> t Zero{}:
      x
    case x <> t Succ{k}:
      ch.sha.nth(t, k)
    case Nil{} _:
      0

# the message padded: 0x80, zeros to 56 mod 64, the length in bits (8 bytes)
def ch.sha.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case Zero{}:
      Nil{}
    case Succ{k}:
      0 <> ch.sha.zeros(k)

def ch.sha.be8.go(n: Nat, +v: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Zero{}:
      acc
    case Succ{k}:
      ch.sha.be8.go(k, Nat.div(v, 256n), U32.from_nat(Nat.mod(v, 256n)) <> acc)

def ch.sha.pad(+m: List<&2, U32>) -> List<&2, U32>:
  +l = List.length(&2, U32, m)
  +r = Nat.mod(l, 64n)
  +z = Bool.pick(Nat, Nat.is_le(r, 55n), Nat.sub(55n, r), Nat.sub(119n, r))
  List.append(&2, U32, m, 128 <> List.append(&2, U32, ch.sha.zeros(z), ch.sha.be8.go(8n, Nat.mul(l, 8n), Nil{})))

# four bytes, big-endian, as a word
def ch.sha.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.shln(a, 24n), U32.shln(b, 16n)), U32.or(U32.shln(c, 8n), d))

# a 64-byte block's 16 words, and the bytes after it
type ChBlk is Data:
  ChBlk{ws: List<&2, U32>, rest: List<&2, U32>}

def ch.sha.words(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> ChBlk:
  match n bs:
    case Succ{k} a <> b <> c <> d <> t:
      ch.sha.words(k, t, ch.sha.word(a, b, c, d) <> acc)
    case _ t:
      ChBlk{List.reverse(&2, U32, acc), t}

# the schedule: w16..w63 from the last sixteen
def ch.sha.sched(n: Nat, +win: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Zero{}:
      List.reverse(&2, U32, acc)
    case Succ{k}:
      +w = U32.add(U32.add(ch.sha.ss1(ch.sha.nth(win, 14n)), ch.sha.nth(win, 9n)), U32.add(ch.sha.ss0(ch.sha.nth(win, 1n)), ch.sha.nth(win, 0n)))
      ch.sha.sched(k, List.append(&2, U32, List.tail(&2, U32, win), [w]), w <> acc)

type ChSt is Data:
  ChSt{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def ch.sha.round(s: ChSt, k: U32, w: U32) -> ChSt:
  match s:
    case ChSt{+a, +b, +c, d, +e, +f, +g, h}:
      +t1 = U32.add(U32.add(U32.add(h, ch.sha.bs1(e)), U32.add(ch.sha.ch(e, f, g), k)), w)
      +t2 = U32.add(ch.sha.bs0(a), ch.sha.maj(a, b, c))
      ChSt{U32.add(t1, t2), a, b, c, U32.add(d, t1), e, f, g}

def ch.sha.rounds(ks: List<&2, U32>, ws: List<&2, U32>, s: ChSt) -> ChSt:
  match ks ws:
    case k <> kt w <> wt:
      ch.sha.rounds(kt, wt, ch.sha.round(s, k, w))
    case _ _:
      s

def ch.sha.st(hs: List<&2, U32>) -> ChSt:
  match hs:
    case a <> b <> c <> d <> e <> f <> g <> h <> _:
      ChSt{a, b, c, d, e, f, g, h}
    case _:
      ChSt{0, 0, 0, 0, 0, 0, 0, 0}

def ch.sha.add(hs: List<&2, U32>, s: ChSt) -> List<&2, U32>:
  match hs s:
    case a <> b <> c <> d <> e <> f <> g <> h <> _ ChSt{a2, b2, c2, d2, e2, f2, g2, h2}:
      [U32.add(a, a2), U32.add(b, b2), U32.add(c, c2), U32.add(d, d2), U32.add(e, e2), U32.add(f, f2), U32.add(g, g2), U32.add(h, h2)]
    case _ _:
      Nil{}

def ch.sha.block(+hs: List<&2, U32>, +ws: List<&2, U32>) -> List<&2, U32>:
  ch.sha.add(hs, ch.sha.rounds(ch.sha.k(), ch.sha.sched(48n, ws, List.reverse(&2, U32, ws)), ch.sha.st(hs)))

# the padded message in 64-byte chunks (k of them)
def ch.sha.chunks(k: Nat, +bs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match k:
    case Zero{}:
      Nil{}
    case Succ{p}:
      List.take(&2, U32, bs, 64n) <> ch.sha.chunks(p, List.drop(&2, U32, bs, 64n))

def ch.sha.ws.of(b: ChBlk) -> List<&2, U32>:
  match b:
    case ChBlk{ws, rest}:
      ws

def ch.sha.run(cs: List<&2, List<&2, U32>>, hs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      hs
    case c <> t:
      ch.sha.run(t, ch.sha.block(hs, ch.sha.ws.of(ch.sha.words(16n, c, Nil{}))))

# a word's four bytes, big-endian
def ch.sha.bytes(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> t:
      U32.and(U32.shrn(w, 24n), 255) <> U32.and(U32.shrn(w, 16n), 255) <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(w, 255) <> ch.sha.bytes(t)


# a list of bytes' SHA-256, its 32 bytes
def ch.sha(+m: List<&2, U32>) -> List<&2, U32>:
  +p = ch.sha.pad(m)
  ch.sha.bytes(ch.sha.run(ch.sha.chunks(Nat.div(List.length(&2, U32, p), 64n), p), ch.sha.h0()))

def ch.hexd(+n: U32) -> U32:
  Bool.pick(U32, U32.is_lt(n, 10), U32.add(n, 48), U32.add(n, 87))

# bytes as lowercase hex digits (sha256sum's)
def ch.hex(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> t:
      ch.hexd(U32.shrn(b, 4n)) <> ch.hexd(U32.and(b, 15)) <> ch.hex(t)

# Keys ---------------------------------------------------------------------

# a text as bytes, one to one, before tail: a value below 255 is that byte,
# any other is 255 and its four bytes (cata's texts are bytes already, so
# this is the file's bytes)
def ch.enc.at(lo: Bool, +x: U32, t: List<&2, U32>) -> List<&2, U32>:
  match lo:
    case True{}:
      x <> t
    case False{}:
      255 <> U32.shrn(x, 24n) <> U32.and(U32.shrn(x, 16n), 255) <> U32.and(U32.shrn(x, 8n), 255) <> U32.and(x, 255) <> t

def ch.enc(xs: List<&2, U32>, tail: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      tail
    case +x <> t:
      ch.enc.at(U32.is_lt(x, 255), x, ch.enc(t, tail))

def ch.digits(+n: Nat) -> List<&2, U32>:
  S.b(Nat.show(n))

# the parts framed: each its length (in values), a colon, its bytes
def ch.frame(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      List.append(&2, U32, ch.digits(List.length(&2, U32, p)), 58 <> ch.enc(p, ch.frame(t)))

# the key of a list of parts: the hex SHA-256 of their frame
def ch.key(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  ch.hex(ch.sha(ch.frame(ps)))

# Entries ------------------------------------------------------------------

def ch.head() -> List<&2, U32>:
  S.b("cata-cache 1 ")

def ch.entry(+v: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, ch.head(), List.append(&2, U32, ch.digits(List.length(&2, U32, v)), 10 <> v))

# a number's digits up to a newline (at: the next value is the newline),
# and what follows it
type ChN is Data:
  ChN{n: Nat, rest: List<&2, U32>}

def ch.num(xs: List<&2, U32>, +acc: Nat, at: Bool) -> Maybe<&2, ChN>:
  match xs at:
    case Nil{} _:
      None{}
    case c <> t True{}:
      Some{ChN{acc, t}}
    case +c <> +t False{}:
      ch.num(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))), S.head.is(t, 10))

def ch.whole(+c: ChN) -> Maybe<&2, List<&2, U32>>:
  match c:
    case ChN{+n, +rest}:
      Bool.pick(Maybe<&2, List<&2, U32>>, Nat.is_eq(n, List.length(&2, U32, rest)), Some{rest}, None{})

def ch.got.num(m: Maybe<&2, ChN>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      ch.whole(c)

def ch.got.body(ok: Bool, +xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      +r = List.drop(&2, U32, xs, List.length(&2, U32, ch.head()))
      ch.got.num(ch.num(r, 0n, S.head.is(r, 10)))

# an entry's value, if the file is one whole
def ch.got(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+xs}:
      ch.got.body(S.prefix(xs, ch.head()), xs)

def ch.file(+dir: String, +key: List<&2, U32>) -> String:
  dir ++ "/" ++ S.str(key)

# the value under key, if there is one
def ch.get(+dir: String, +key: List<&2, U32>) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    m : Maybe<&2, List<&2, U32>> <- S.slurp(ch.file(dir, key))
    return ch.got(m)

def ch.put(+dir: String, +key: List<&2, U32>, +v: List<&2, U32>) -> IO(Unit):
  S.write(ch.file(dir, key), ch.entry(v))

def ch.split.got(m: Maybe<&2, ChN>, v: List<&2, U32>) -> ChN:
  match m:
    case Some{c}:
      c
    case None{}:
      ChN{0n, v}

# a number's value and the rest (an oracle's exit status, then its text)
def ch.split.num(+v: List<&2, U32>) -> ChN:
  ch.split.got(ch.num(v, 0n, S.head.is(v, 10)), v)
