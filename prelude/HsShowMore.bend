# Show at pairs, at Data.Map's maps and at Data.Set's sets (Fold.bend's
# fd.sp), each given showsPrec at its parts, as HsShow.maybe is. GHC.Show's
# pair: showsPrec d (a, b) r = '(' : shows a (',' : shows b (')' : r)),
# each part at precedence 0 and d unused. containers' map and set:
# showsPrec d m = showParen (d > 10) (showString "fromList " . shows
# (toList m)), the list in key order, a map's entries as pairs.
def HsShow.pair(~A: Data, ~B: Data, ~sa: HsInt -> A -> List<&2, Char> -> List<&2, Char>, ~sb: HsInt -> B -> List<&2, Char> -> List<&2, Char>, p: Sigma<&2, &2, A, _ => B>, r: List<&2, Char>) -> List<&2, Char>:
  match p:
    case Tuple{a, b}:
      '(' <> sa(HsInt.Pos{0n})(a)(',' <> sb(HsInt.Pos{0n})(b)(')' <> r))

def HsShow.map(~K: Data, ~V: Data, ~sk: HsInt -> K -> List<&2, Char> -> List<&2, Char>, ~sv: HsInt -> V -> List<&2, Char> -> List<&2, Char>, d: HsInt, m: HsMap<K, V>, r: List<&2, Char>) -> List<&2, Char>:
  HsShow.paren(HsInt.is_ge(d, HsInt.Pos{11n}), s => List.append(&2, Char, String.to_list("fromList "), HsShow.list(~Sigma<&2, &2, K, _ => V>, ~(y => t => HsShow.pair(~K, ~V, ~sk, ~sv, y, t)), HsMap.toList(~K, ~V, m), s)), r)

def HsShow.set(~K: Data, ~sk: HsInt -> K -> List<&2, Char> -> List<&2, Char>, d: HsInt, m: HsSet<K>, r: List<&2, Char>) -> List<&2, Char>:
  HsShow.paren(HsInt.is_ge(d, HsInt.Pos{11n}), s => List.append(&2, Char, String.to_list("fromList "), HsShow.list(~K, ~(y => t => sk(HsInt.Pos{0n})(y)(t)), HsSet.toList(~K, m), s)), r)

# showsPrec at a list and at a pair, its precedence unused (Spec's sp.shw:
# at a type that holds one of the package's, spList and spPair)
def HsShow.listP(~A: Data, ~sp: HsInt -> A -> List<&2, Char> -> List<&2, Char>, d: HsInt, xs: List<&2, A>, r: List<&2, Char>) -> List<&2, Char>:
  HsShow.list(~A, ~(y => t => sp(HsInt.Pos{0n})(y)(t)), xs, r)

def HsShow.pairP(~A: Data, ~B: Data, ~sa: HsInt -> A -> List<&2, Char> -> List<&2, Char>, ~sb: HsInt -> B -> List<&2, Char> -> List<&2, Char>, d: HsInt, p: Sigma<&2, &2, A, _ => B>, r: List<&2, Char>) -> List<&2, Char>:
  HsShow.pair(~A, ~B, ~sa, ~sb, p, r)
