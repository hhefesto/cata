import Base
import ./Text.bend as Tx
import ./HsPrelude.bend as HsPrelude
import ./Telomare_Parse.bend as Parse
import ./Telomare_IR_Surface.bend as Surface
import ./Telomare_IR_Loc.bend as Loc

# The files of a program: app/Main.hs's getModulesFor, the reads its own and
# the modules' parse telomare's.

def Str() -> Data:
  List<&2, Char>

# a module's name and its text
def Mod() -> Data:
  Sigma<&2, &2, List<&2, Char>, (_ => List<&2, Char>)>

def Item() -> Data:
  Surface.ModuleItem<HsPrelude.Cofree<(r_ => Surface.ParsedTermF<HsPrelude.Fix<(r_ => Surface.PatternF<Surface.AnnotatedPST, r_>)>, r_>), Loc.LocTag>>

# the path's parts
# ----------------

def cut.slash(cs: List<&2, Char>, +dir: List<&2, Char>, +cur: List<&2, Char>) -> Mod():
  match cs:
    case Nil{}:
      (dir, cur)
    case +c <> t:
      match c:
        case '/':
          cut.slash(t, List.append(&2, Char, dir, List.append(&2, Char, cur, '/' <> [])), [])
        case d:
          cut.slash(t, dir, List.append(&2, Char, cur, d <> []))

def dir.of(p: Mod()) -> List<&2, Char>:
  (d, _) = p
  d

def file.of(p: Mod()) -> List<&2, Char>:
  (_, f) = p
  f

# a file's name up to its last dot (reversed, so its first)
def base.go(cs: List<&2, Char>) -> Maybe<&2, List<&2, Char>>:
  match cs:
    case Nil{}:
      None{}
    case c <> t:
      match c:
        case '.':
          Some{t}
        case d:
          base.go(t)

def base.or(m: Maybe<&2, List<&2, Char>>, all: List<&2, Char>) -> List<&2, Char>:
  match m:
    case None{}:
      all
    case Some{r}:
      List.reverse(&2, Char, r)

def base.name(+file: List<&2, Char>) -> List<&2, Char>:
  base.or(base.go(List.reverse(&2, Char, file)), file)

# the imports
# -----------

def imports(xs: List<&2, Item()>) -> List<&2, List<&2, Char>>:
  match xs:
    case Nil{}:
      []
    case x <> t:
      match x:
        case Surface.ModuleItem.ModuleImportItem{d}:
          match d:
            case Surface.ImportDecl.ImportDecl{_, m, _}:
              Loc.locatedNameText(m) <> imports(t)
        case Surface.ModuleItem.ModuleDefinitionItem{_}:
          imports(t)

def imports.of(e: Either<&2, &2, List<&2, Char>, List<&2, Item()>>) -> List<&2, List<&2, Char>>:
  match e:
    case Inl{_}:
      []
    case Inr{xs}:
      imports(xs)

def has(+m: List<&2, Char>, xs: List<&2, Mod()>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      (n, _) = x
      Bool.or(String.eq(String.from_list(m), String.from_list(n)), has(m, t))

# the loads
# ---------

def orDie(r: Result<&1, &1, String, String>) -> IO(String):
  match r:
    case Done{s}:
      IO.pure(String, s)
    case Fail{e}:
      IO.die(String, 1, e)

# a file, or the one at the other path if it isn't there
def or.other(r: Result<&1, &1, String, String>, path: String) -> IO(String):
  match r:
    case Done{s}:
      IO.pure(String, s)
    case Fail{_}:
      do IO<String>:
        r2 : Result<&1, &1, String, String> <- Tx.read_file(path)
        orDie(r2)

def path.of(dir: List<&2, Char>, file: List<&2, Char>) -> String:
  String.from_list(List.append(&2, Char, dir, file))

# the entry from its own path, an import beside it or else here
def text.of(isEntry: Bool, dir: List<&2, Char>, file: List<&2, Char>, +name: List<&2, Char>) -> IO(String):
  match isEntry:
    case True{}:
      do IO<String>:
        r : Result<&1, &1, String, String> <- Tx.read_file(path.of(dir, file))
        orDie(r)
    case False{}:
      do IO<String>:
        r : Result<&1, &1, String, String> <- Tx.read_file(String.append(path.of(dir, name), ".tel"))
        or.other(r, String.append(String.from_list(name), ".tel"))

# go: the queue of names, its head and whether it is loaded, its text once read
type St is Data:
  Queue{+queue: List<&2, List<&2, Char>>, +done: List<&2, Mod()>}
  Ask{+seen: Bool, +name: List<&2, Char>, +rest: List<&2, List<&2, Char>>, +done: List<&2, Mod()>}
  Got{+name: List<&2, Char>, +text: List<&2, Char>, +rest: List<&2, List<&2, Char>>, +done: List<&2, Mod()>}

def same(a: List<&2, Char>, b: List<&2, Char>) -> Bool:
  String.eq(String.from_list(a), String.from_list(b))

def load(fuel: Nat, +dir: List<&2, Char>, +file: List<&2, Char>, +entry: List<&2, Char>, st: St) -> IO(List<&2, Mod()>):
  match fuel:
    case Zero{}:
      IO.die(List<&2, Mod()>, 1, "too many modules")
    case Succ{f}:
      match st:
        case Queue{queue, +done}:
          match queue:
            case Nil{}:
              IO.pure(List<&2, Mod()>, done)
            case +m <> +rest:
              load(f, dir, file, entry, Ask{has(m, done), m, rest, done})
        case Ask{seen, +m, +rest, +done}:
          match seen:
            case True{}:
              load(f, dir, file, entry, Queue{rest, done})
            case False{}:
              do IO<List<&2, Mod()>>:
                s : String <- text.of(same(m, entry), dir, file, m)
                load(f, dir, file, entry, Got{m, String.to_list(s), rest, done})
        case Got{+m, +text, rest, done}:
          load(f, dir, file, entry, Queue{List.append(&2, List<&2, Char>, rest, imports.of(Parse.runParseModule(m, text))), Tuple{m, text} <> done})

# every module reachable from the entry, as getModulesFor lists them
def modules(+p: Mod()) -> IO(List<&2, Mod()>):
  +file = file.of(p)
  +entry = base.name(file)
  load(4096n, dir.of(p), file, entry, Queue{entry <> [], []})

def split(+path: List<&2, Char>) -> Mod():
  cut.slash(path, [], [])
