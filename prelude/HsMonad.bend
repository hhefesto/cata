# Control.Monad's list functions at Either e and at Maybe (Fold.bend's
# fd.mapm.at and fd.mlist.at; State's and ExceptT-over-State's are in each
# module's prelude, fd.pre.state and fd.pre.exs): mapM_ (forM_, traverse_),
# mapM (forM, traverse), sequence (sequenceA), foldM, filterM and zipWithM_
# at a list. The answer
# is GHC's: the first Left (Nothing) in the list's order, else the values.
# Bend computes a call's arguments first, so the rest of the list is walked
# even after a Left (a match takes no computed value): the same answer,
# more work.

# x's Left, else rest
def HsList.either.then(~E: Data, ~B: Data, ~C: Data, r: Either<&2, &2, E, B>, rest: Either<&2, &2, E, C>) -> Either<&2, &2, E, C>:
  match r:
    case Inl{e}:
      Inl{e}
    case Inr{b}:
      rest

def HsList.either.cons(~E: Data, ~B: Data, r: Either<&2, &2, E, B>, rest: Either<&2, &2, E, List<&2, B>>) -> Either<&2, &2, E, List<&2, B>>:
  match r rest:
    case Inl{e} _:
      Inl{e}
    case Inr{b} Inl{e}:
      Inl{e}
    case Inr{b} Inr{bs}:
      Inr{b <> bs}

def HsList.keep(~A: Data, k: Bool, x: A, ys: List<&2, A>) -> List<&2, A>:
  match k:
    case True{}:
      x <> ys
    case False{}:
      ys

def HsList.either.keep(~E: Data, ~A: Data, x: A, r: Either<&2, &2, E, Bool>, rest: Either<&2, &2, E, List<&2, A>>) -> Either<&2, &2, E, List<&2, A>>:
  match r rest:
    case Inl{e} _:
      Inl{e}
    case Inr{k} Inl{e}:
      Inl{e}
    case Inr{k} Inr{ys}:
      Inr{HsList.keep(~A, k, x, ys)}

def HsList.either.mapm_(~E: Data, ~A: Data, ~B: Data, ~f: A -> Either<&2, &2, E, B>, xs: List<&2, A>) -> Either<&2, &2, E, Unit>:
  match xs:
    case Nil{}:
      Inr{Unit{}}
    case h <> t:
      HsList.either.then(~E, ~B, ~Unit, f(h), HsList.either.mapm_(~E, ~A, ~B, ~f, t))

def HsList.either.mapm(~E: Data, ~A: Data, ~B: Data, ~f: A -> Either<&2, &2, E, B>, xs: List<&2, A>) -> Either<&2, &2, E, List<&2, B>>:
  match xs:
    case Nil{}:
      Inr{Nil{}}
    case h <> t:
      HsList.either.cons(~E, ~B, f(h), HsList.either.mapm(~E, ~A, ~B, ~f, t))

# sequence (sequenceA) at a list: mapM id
def HsList.either.seq(~E: Data, ~B: Data, xs: List<&2, Either<&2, &2, E, B>>) -> Either<&2, &2, E, List<&2, B>>:
  match xs:
    case Nil{}:
      Inr{Nil{}}
    case h <> t:
      HsList.either.cons(~E, ~B, h, HsList.either.seq(~E, ~B, t))

def HsList.either.step(~E: Data, ~A: Data, ~B: Data, ~f: B -> A -> Either<&2, &2, E, B>, acc: Either<&2, &2, E, B>, h: A) -> Either<&2, &2, E, B>:
  match acc:
    case Inl{e}:
      Inl{e}
    case Inr{z}:
      f(z)(h)

def HsList.either.foldm.go(~E: Data, ~A: Data, ~B: Data, ~f: B -> A -> Either<&2, &2, E, B>, xs: List<&2, A>, acc: Either<&2, &2, E, B>) -> Either<&2, &2, E, B>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      HsList.either.foldm.go(~E, ~A, ~B, ~f, t, HsList.either.step(~E, ~A, ~B, ~f, acc, h))

def HsList.either.foldm(~E: Data, ~A: Data, ~B: Data, ~f: B -> A -> Either<&2, &2, E, B>, xs: List<&2, A>, z: B) -> Either<&2, &2, E, B>:
  HsList.either.foldm.go(~E, ~A, ~B, ~f, xs, Inr{z})

def HsList.either.filterm(~E: Data, ~A: Data, ~p: A -> Either<&2, &2, E, Bool>, xs: List<&2, A>) -> Either<&2, &2, E, List<&2, A>>:
  match xs:
    case Nil{}:
      Inr{Nil{}}
    case +h <> t:
      HsList.either.keep(~E, ~A, h, p(h), HsList.either.filterm(~E, ~A, ~p, t))

def HsList.either.zipwithm_(~E: Data, ~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> Either<&2, &2, E, C>, xs: List<&2, A>, ys: List<&2, B>) -> Either<&2, &2, E, Unit>:
  match xs ys:
    case x <> xt y <> yt:
      HsList.either.then(~E, ~C, ~Unit, f(x)(y), HsList.either.zipwithm_(~E, ~A, ~B, ~C, ~f, xt, yt))
    case _ _:
      Inr{Unit{}}

# at Maybe
def HsList.maybe.then(~B: Data, ~C: Data, r: Maybe<&2, B>, rest: Maybe<&2, C>) -> Maybe<&2, C>:
  match r:
    case None{}:
      None{}
    case Some{b}:
      rest

def HsList.maybe.cons(~B: Data, r: Maybe<&2, B>, rest: Maybe<&2, List<&2, B>>) -> Maybe<&2, List<&2, B>>:
  match r rest:
    case None{} _:
      None{}
    case Some{b} None{}:
      None{}
    case Some{b} Some{bs}:
      Some{b <> bs}

def HsList.maybe.keep(~A: Data, x: A, r: Maybe<&2, Bool>, rest: Maybe<&2, List<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match r rest:
    case None{} _:
      None{}
    case Some{k} None{}:
      None{}
    case Some{k} Some{ys}:
      Some{HsList.keep(~A, k, x, ys)}

def HsList.maybe.mapm_(~A: Data, ~B: Data, ~f: A -> Maybe<&2, B>, xs: List<&2, A>) -> Maybe<&2, Unit>:
  match xs:
    case Nil{}:
      Some{Unit{}}
    case h <> t:
      HsList.maybe.then(~B, ~Unit, f(h), HsList.maybe.mapm_(~A, ~B, ~f, t))

def HsList.maybe.mapm(~A: Data, ~B: Data, ~f: A -> Maybe<&2, B>, xs: List<&2, A>) -> Maybe<&2, List<&2, B>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case h <> t:
      HsList.maybe.cons(~B, f(h), HsList.maybe.mapm(~A, ~B, ~f, t))

# sequence (sequenceA) at a list: mapM id
def HsList.maybe.seq(~B: Data, xs: List<&2, Maybe<&2, B>>) -> Maybe<&2, List<&2, B>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case h <> t:
      HsList.maybe.cons(~B, h, HsList.maybe.seq(~B, t))

def HsList.maybe.step(~A: Data, ~B: Data, ~f: B -> A -> Maybe<&2, B>, acc: Maybe<&2, B>, h: A) -> Maybe<&2, B>:
  match acc:
    case None{}:
      None{}
    case Some{z}:
      f(z)(h)

def HsList.maybe.foldm.go(~A: Data, ~B: Data, ~f: B -> A -> Maybe<&2, B>, xs: List<&2, A>, acc: Maybe<&2, B>) -> Maybe<&2, B>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      HsList.maybe.foldm.go(~A, ~B, ~f, t, HsList.maybe.step(~A, ~B, ~f, acc, h))

def HsList.maybe.foldm(~A: Data, ~B: Data, ~f: B -> A -> Maybe<&2, B>, xs: List<&2, A>, z: B) -> Maybe<&2, B>:
  HsList.maybe.foldm.go(~A, ~B, ~f, xs, Some{z})

def HsList.maybe.filterm(~A: Data, ~p: A -> Maybe<&2, Bool>, xs: List<&2, A>) -> Maybe<&2, List<&2, A>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case +h <> t:
      HsList.maybe.keep(~A, h, p(h), HsList.maybe.filterm(~A, ~p, t))

def HsList.maybe.zipwithm_(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> Maybe<&2, C>, xs: List<&2, A>, ys: List<&2, B>) -> Maybe<&2, Unit>:
  match xs ys:
    case x <> xt y <> yt:
      HsList.maybe.then(~C, ~Unit, f(x)(y), HsList.maybe.zipwithm_(~A, ~B, ~C, ~f, xt, yt))
    case _ _:
      Some{Unit{}}
