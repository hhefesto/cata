{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | hs-export: GHC 9.10's typechecked syntax of one Haskell module, as
--   S-expressions (FORMAT.md).  `hs-export OUT.sexp FILE.hs` type-checks
--   FILE against GHC's own packages and writes OUT.sexp: the module's
--   header, its types, classes and instances, and every binding with the
--   type GHC gave each binder and the instance GHC chose for each class
--   method.  It translates and decides nothing: cata's Bend side does.  A
--   module GHC rejects is written as one (error ...) line.
module Main (main) where

import Control.Exception (SomeException, displayException, evaluate, try)
import Control.Monad (forM)
import qualified Control.Monad.Catch as MC
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (State, evalState, get, gets, modify', put)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as B
import Data.Data (Data, showConstr, toConstr)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Ratio (denominator, numerator)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO

import GHC
import GHC.Paths (libdir)
import GHC.Core (CoreExpr, Expr (..))
import GHC.Core.Class (classMethods, classSCTheta, classTyVars)
import GHC.Core.ConLike (ConLike (..))
import GHC.Core.DataCon (dataConExTyCoVars, dataConFieldLabels, dataConOrigArgTys, dataConTheta)
import GHC.Core.InstEnv (ClsInst (..))
import GHC.Core.FamInstEnv (FamInst (..))
import GHC.Core.TyCo.Rep (Scaled (..), TyLit (..), Type (..))
import GHC.Core.TyCon (isAlgTyCon, isNewTyCon, synTyConDefn_maybe, tyConClass_maybe, tyConDataCons, tyConTyVars)
import GHC.Core.Type (filterOutInvisibleTypes)
import GHC.Data.Bag (bagToList)
import GHC.Data.FastString (unpackFS)
import GHC.Driver.Session (DynFlags (..), Language (..))
import GHC.Hs
import GHC.Tc.Types (TcGblEnv (..))
import GHC.Tc.Utils.TcType (tcSplitDFunTy)
import GHC.Core.Class (Class)
import GHC.Tc.Types.Evidence (EvBind (..), EvTerm (..), HsWrapper (..), TcEvBinds (..))
import GHC.Types.Basic (Origin (..), RecFlag (..))
import GHC.Types.FieldLabel (FieldLabel (..))
import GHC.Types.Id (idType, isClassOpId_maybe, isDFunId, isDataConId_maybe, isRecordSelector)
import GHC.Types.Name (getOccString, getSrcSpan, isExternalName, nameModule_maybe)
import GHC.Types.SourceText (FractionalLit (..), IntegralLit (..), SourceText (..), rationalFromFractionalLit)
import GHC.Types.SrcLoc
import GHC.Types.Unique (Uniquable (..), getKey)
import GHC.Types.Var (FunTyFlag, VarBndr (..), isInvisibleFunArg)
import GHC.Driver.Backend (noBackend)
import GHC.Utils.Outputable (showPprUnsafe)
import GHC.Utils.Logger (pushLogHook)
import GHC.Driver.Monad (modifyLogger)
import GHC.Data.Graph.Directed (flattenSCCs)
import GHC.Unit.Module.Graph (ModuleGraphNode (..))

import HsExport.Sexp (Sexp (A, I, S), list, render, tagged)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--package", outDir, flagFile] -> do
      ls <- lines <$> readFile flagFile
      let (flags, files) = break (== "--") (filter (not . null) ls)
      exportPackage outDir flags (drop 1 files)
    [out, file] -> exportFile out file
    _ -> do
      hPutStrLn stderr "usage: hs-export OUT.sexp FILE.hs\n       hs-export --package OUTDIR ARGS  (ARGS: GHC flags, a line `--`, then the modules' files, one per line)"
      exitFailure

-- | A package's modules at once: GHC loads them all (no code), then each is
--   type-checked again in the loaded session and written to
--   OUTDIR/MODULE.sexp (each . of MODULE as _); OUTDIR/modules.txt lists them in dependency order
--   (a module after every home module it imports), one file per line.  A
--   module GHC rejects, or one that imports a rejected one, is its header
--   and one (error ...) line.  The flags are GHC's (-i, -X, -package-db).
exportPackage :: FilePath -> [String] -> [FilePath] -> IO ()
exportPackage outDir flags files = do
  r <- try (runGhc (Just libdir) (packageGhc outDir flags files))
  case r of
    Left (e :: SomeException) -> hPutStrLn stderr (displayException e) >> exitFailure
    Right outs -> writeFile (outDir ++ "/modules.txt") (unlines outs)

-- | Load the package, then write each module, in dependency order, from
--   inside the loaded session (its imports come from the home package).
packageGhc :: FilePath -> [String] -> [FilePath] -> Ghc [FilePath]
packageGhc outDir flags files = do
  df0 <- getSessionDynFlags
  logger <- getLogger
  (df1, _, _) <- parseDynamicFlags logger df0 {language = Just GHC2021} (map noLoc ("-w" : flags))
  _ <- setSessionDynFlags df1 {backend = noBackend, ghcLink = NoLink, verbosity = 0}
  modifyLogger (pushLogHook (const (\_ _ _ _ -> pure ())))
  ts <- mapM (\f -> guessTarget f Nothing Nothing) files
  setTargets ts
  _ <- load LoadAllTargets
  mg <- getModuleGraph
  let mss = flattenSCCs (topSortModuleGraph False mg Nothing)
  forM [ms | ModuleNode _ ms <- mss] $ \ms -> do
    let name = moduleNameString (ms_mod_name ms)
        file = maybe name id (ml_hs_file (ms_location ms))
        -- a Bend module path is plain names: M.N is written M_N
        out = outDir ++ "/" ++ map (\c -> if c == '.' then '_' else c) name ++ ".sexp"
    r <- MC.try (summaryGhc file ms)
    let xs = case r of
          Right ys -> ys
          Left (e :: SomeException) -> [header file, tagged "error" [S (displayException e)]]
    liftIO $ withFile out WriteMode $ \h -> do
      hSetBinaryMode h True
      mapM_ (\s -> B.hPutBuilder h (render s <> B.char7 '\n')) xs
    pure out

-- | One module of the loaded session, as exportGhc writes it.
summaryGhc :: FilePath -> ModSummary -> Ghc [Sexp]
summaryGhc file ms = do
  p <- parseModule ms
  tcm <- typecheckModule p
  let env = fst (tm_internals_ tcm)
      modName = moduleNameString (ms_mod_name ms)
      imps = [ tagged "import" [S (moduleNameString (unLoc (ideclName d))), A (if isImportDeclQualified (ideclQualified d) then "qualified" else "open")]
             | L _ d <- hsmodImports (unLoc (pm_parsed_source p)) ]
      body = evalState (moduleS env) st0
  _ <- liftIO (evaluate (length body))
  pure (header file : tagged "module" [S modName, list imps] : body)

-- | Type-check FILE and write its export (or one (error ...) line) to OUT.
exportFile :: FilePath -> FilePath -> IO ()
exportFile out file = do
  r <- try (runGhc (Just libdir) (exportGhc file) >>= \xs -> evaluate (length xs) >> pure xs)
  let xs = case r of
        Right ys -> ys
        Left (e :: SomeException) -> [header file, tagged "error" [S (displayException e)]]
  withFile out WriteMode $ \h -> do
    hSetBinaryMode h True
    mapM_ (\x -> B.hPutBuilder h (render x <> B.char7 '\n')) xs

header :: FilePath -> Sexp
header file = tagged "hs-export" [I 1, tagged "ghc" [S "9.10.3"], tagged "file" [S file]]

exportGhc :: FilePath -> Ghc [Sexp]
exportGhc file = do
  df0 <- getSessionDynFlags
  logger <- getLogger
  -- GHC2021, as the ghc and runghc commands default to; no warnings
  (df1, _, _) <- parseDynamicFlags logger df0 {language = Just GHC2021} [noLoc "-w"]
  _ <- setSessionDynFlags df1 {backend = noBackend, ghcLink = NoLink, verbosity = 0}
  -- a file's own OPTIONS_GHC may turn warnings back on: drop every log
  -- message (errors arrive as the SourceError written as (error ...))
  modifyLogger (pushLogHook (const (\_ _ _ _ -> pure ())))
  t <- guessTarget file Nothing Nothing
  setTargets [t]
  mg <- depanal [] False
  case mgModSummaries mg of
    [ms] -> do
      p <- parseModule ms
      tcm <- typecheckModule p
      let env = fst (tm_internals_ tcm)
          modName = moduleNameString (ms_mod_name ms)
          imps = [ tagged "import" [S (moduleNameString (unLoc (ideclName d))), A (if isImportDeclQualified (ideclQualified d) then "qualified" else "open")]
                 | L _ d <- hsmodImports (unLoc (pm_parsed_source p)) ]
          body = evalState (moduleS env) st0
      pure (header file : tagged "module" [S modName, list imps] : body)
    mss -> liftIO (ioError (userError ("expected one module, found " ++ show (length mss))))

-- Naming -------------------------------------------------------------------

-- | The export's state: each local binder's number (in order of first
--   sight, so the numbering is the same on every run), and the monomorphic
--   Ids of the enclosing AbsBinds, each mapped to its polymorphic Id.
data St = St
  { stLocal :: !(M.Map Integer Int)
  , stNext :: !Int
  , stMono :: !(M.Map Integer Id)
  }

st0 :: St
st0 = St M.empty 0 M.empty

type M = State St

keyOf :: Uniquable a => a -> Integer
keyOf = toInteger . getKey . getUnique

modOf :: NamedThing a => a -> String
modOf x = maybe "" (moduleNameString . moduleName) (nameModule_maybe (getName x))

-- | A variable occurrence: (g MOD NAME KIND) for a top-level or imported
--   name, (l NAME N) for a local one, (self X) for a recursive reference to
--   the binding X being defined (an AbsBinds' monomorphic Id).
varS :: Id -> M Sexp
varS v = do
  mono <- gets stMono
  case M.lookup (keyOf v) mono of
    Just p -> (\x -> tagged "self" [x]) <$> varS p
    Nothing
      | isExternalName (getName v) -> pure (globalS v)
      | otherwise -> localS v

globalS :: Id -> Sexp
globalS v = tagged "g" [S (modOf v), S (getOccString v), kind]
  where
    kind
      | Just _ <- isDataConId_maybe v = A "con"
      | Just cls <- isClassOpId_maybe v = tagged "method" [S (modOf cls), S (getOccString cls)]
      | isRecordSelector v = A "sel"
      | isDFunId v = A "dfun"
      | otherwise = A "var"

localS :: NamedThing a => Uniquable a => a -> M Sexp
localS v = do
  st <- get
  let k = keyOf v
  n <- case M.lookup k (stLocal st) of
    Just n -> pure n
    Nothing -> do
      put st {stLocal = M.insert k (stNext st) (stLocal st), stNext = stNext st + 1}
      pure (stNext st)
  pure (tagged "l" [S (getOccString v), I (toInteger n)])

-- | A binder with its type: (bv VAR TYPE).
binderS :: Id -> M Sexp
binderS v = do
  x <- varS v
  pure (tagged "bv" [x, typeS (idType v)])

unsupported :: Data a => a -> Sexp
unsupported x = tagged "unsupported" [S (showConstr (toConstr x))]

-- Types --------------------------------------------------------------------

typeS :: Type -> Sexp
typeS = \case
  TyVarTy v -> tagged "tv" [S (getOccString v)]
  AppTy a b -> tagged "tapp" [typeS a, typeS b]
  TyConApp tc args -> tagged "tc" (S (modOf tc) : S (getOccString tc) : map typeS (filterOutInvisibleTypes tc args))
  FunTy {ft_af = af, ft_arg = a, ft_res = r} -> tagged (funTag af) [typeS a, typeS r]
  ForAllTy (Bndr v _) b -> tagged "tforall" [S (getOccString v), typeS b]
  LitTy (NumTyLit n) -> tagged "tnum" [I n]
  LitTy (StrTyLit s) -> tagged "tstr" [S (unpackFS s)]
  LitTy (CharTyLit c) -> tagged "tchar" [S [c]]
  CastTy t _ -> typeS t
  CoercionTy _ -> A "tcoercion"

funTag :: FunTyFlag -> String
funTag af = if isInvisibleFunArg af then "tctx" else "tfun"

-- Spans --------------------------------------------------------------------

spanS :: SrcSpan -> Sexp
spanS = \case
  RealSrcSpan r _ ->
    tagged "span" [I (toInteger (srcSpanStartLine r)), I (toInteger (srcSpanStartCol r)), I (toInteger (srcSpanEndLine r)), I (toInteger (srcSpanEndCol r))]
  UnhelpfulSpan _ -> A "nospan"

-- The module ---------------------------------------------------------------

moduleS :: TcGblEnv -> M [Sexp]
moduleS env = do
  tcs <- mapM tyConS (tcg_tcs env)
  insts <- mapM instS (tcg_insts env)
  let fams = map famInstS (tcg_fam_insts env)
  evs <- mapM evBindS (bagToList (tcg_ev_binds env))
  let binds = sortOn (spanKey . getLocA) (bagToList (tcg_binds env))
  bs <- mapM bindS binds
  pure (tcs ++ insts ++ fams ++ [tagged "top-evbinds" evs] ++ map (\b -> tagged "top" [b]) bs)

spanKey :: SrcSpan -> (Int, Int)
spanKey = \case
  RealSrcSpan r _ -> (srcSpanStartLine r, srcSpanStartCol r)
  UnhelpfulSpan _ -> (maxBound, 0)

tyConS :: TyCon -> M Sexp
tyConS tc
  | Just cls <- tyConClass_maybe tc =
      pure $ tagged "class"
        [ S (getOccString tc)
        , list [S (getOccString v) | v <- classTyVars cls]
        , list [tagged "method" [S (getOccString m), typeS (idType m)] | m <- classMethods cls]
        , list (map typeS (classSCTheta cls))
        , spanS (getSrcSpan tc)
        ]
  | Just (tvs, rhs) <- synTyConDefn_maybe tc =
      pure $ tagged "synonym" [S (getOccString tc), list [S (getOccString v) | v <- tvs], typeS rhs, spanS (getSrcSpan tc)]
  | isAlgTyCon tc =
      pure $ tagged (if isNewTyCon tc then "newtype" else "data")
        [ S (getOccString tc)
        , list [S (getOccString v) | v <- tyConTyVars tc]
        , list (map conS (tyConDataCons tc))
        , spanS (getSrcSpan tc)
        ]
  | otherwise = pure (tagged "unsupported" [S "tycon", S (getOccString tc)])
  where
    conS dc =
      tagged "con"
        [ S (getOccString dc)
        , list [S (getOccString (flSelector fl)) | fl <- dataConFieldLabels dc]
        , list [typeS t | Scaled _ t <- dataConOrigArgTys dc]
        , tagged "ex" [I (toInteger (length (dataConExTyCoVars dc))), I (toInteger (length (dataConTheta dc)))]
        ]

-- (faminst FAMMOD FAM (ARG...) RHS): a type family's instance, its
-- arguments' variables free (an associated type's too)
famInstS :: FamInst -> Sexp
famInstS fi = tagged "faminst" [S (modOf (fi_fam fi)), S (getOccString (fi_fam fi)), list (map typeS (fi_tys fi)), typeS (fi_rhs fi)]

instS :: ClsInst -> M Sexp
instS ci = do
  d <- varS (is_dfun ci)
  let (_, _, cls, _) = tcSplitDFunTy (idType (is_dfun ci))
  pure $ tagged "instance" [S (modOf (is_cls ci)), S (getOccString (is_cls ci)), list (map typeS (is_tys ci)), d, spanS (getSrcSpan (is_dfun ci)), clsInfoS cls]

-- (cls (TV...) (METHOD...) NSUPER): an instance's class, its dictionary's
-- fields: NSUPER superclasses, then the methods in this order
clsInfoS :: Class -> Sexp
clsInfoS cls = tagged "cls" [list [S (getOccString v) | v <- classTyVars cls], list [S (getOccString m) | m <- classMethods cls], I (toInteger (length (classSCTheta cls)))]

-- Bindings -----------------------------------------------------------------

bindS :: LHsBind GhcTc -> M Sexp
bindS lb@(L _ b) = case b of
  FunBind {fun_id = L _ f, fun_matches = mg, fun_ext = (w, _)} -> do
    f' <- varS f
    m <- mgS mg
    wr <- wrapS w (A "hole")
    pure (tagged "fun" [f', typeS (idType f), spanS (getLocA lb), m, wr])
  PatBind {pat_lhs = p, pat_rhs = rhs} -> do
    p' <- lpatS p
    r <- grhssS rhs
    pure (tagged "patbind" [p', spanS (getLocA lb), r])
  VarBind {var_id = v, var_rhs = e} -> do
    v' <- varS v
    e' <- lexprS e
    pure (tagged "varbind" [v', typeS (idType v), e'])
  XHsBindsLR ab -> do
    modify' (\st -> st {stMono = foldr (\e -> M.insert (keyOf (abe_mono e)) (abe_poly e)) (stMono st) (abs_exports ab)})
    evs <- mapM binderS (abs_ev_vars ab)
    exps <- forM (abs_exports ab) $ \e -> do
      p <- varS (abe_poly e)
      pure (tagged "export" [p, typeS (idType (abe_poly e))])
    ebs <- mapM evBindsS (abs_ev_binds ab)
    bs <- mapM bindS (bagToList (abs_binds ab))
    pure $ tagged "abs"
      [ list [S (getOccString v) | v <- abs_tvs ab]
      , list evs
      , list exps
      , list ebs
      , list bs
      , spanS (getLocA lb)
      ]
  PatSynBind {} -> pure (unsupported b)

mgS :: MatchGroup GhcTc (LHsExpr GhcTc) -> M Sexp
mgS (MG ext (L _ alts)) = do
  ms <- mapM matchS alts
  pure $ tagged "matches"
    [ list [typeS t | Scaled _ t <- mg_arg_tys ext]
    , typeS (mg_res_ty ext)
    , A (case mg_origin ext of FromSource -> "source"; Generated {} -> "generated")
    , list ms
    ]

matchS :: LMatch GhcTc (LHsExpr GhcTc) -> M Sexp
matchS (L _ m) = do
  ps <- mapM lpatS (m_pats m)
  g <- grhssS (m_grhss m)
  pure (tagged "match" [list ps, g])

grhssS :: GRHSs GhcTc (LHsExpr GhcTc) -> M Sexp
grhssS g = do
  rs <- mapM grhsS (grhssGRHSs g)
  bs <- localBindsS (grhssLocalBinds g)
  pure (tagged "grhss" [list rs, bs])

grhsS :: LGRHS GhcTc (LHsExpr GhcTc) -> M Sexp
grhsS (L _ (GRHS _ guards body)) = do
  gs <- mapM stmtS guards
  e <- lexprS body
  pure (tagged "grhs" [list gs, e])

localBindsS :: HsLocalBinds GhcTc -> M Sexp
localBindsS = \case
  HsValBinds _ (XValBindsLR (NValBinds groups _)) -> do
    gs <- forM groups $ \(rf, bs) -> do
      bs' <- mapM bindS (bagToList bs)
      pure (tagged (case rf of Recursive -> "rec"; NonRecursive -> "nonrec") bs')
    pure (tagged "binds" gs)
  EmptyLocalBinds _ -> pure (tagged "binds" [])
  other -> pure (unsupported other)

stmtS :: ExprLStmt GhcTc -> M Sexp
stmtS (L _ s) = case s of
  LastStmt _ e _ _ -> (\x -> tagged "last" [x]) <$> lexprS e
  BindStmt _ p e -> do
    p' <- lpatS p
    e' <- lexprS e
    pure (tagged "bind" [p', e'])
  BodyStmt _ e _ _ -> (\x -> tagged "body" [x]) <$> lexprS e
  LetStmt _ bs -> (\x -> tagged "letstmt" [x]) <$> localBindsS bs
  other -> pure (unsupported other)

-- Evidence -----------------------------------------------------------------

evBindsS :: TcEvBinds -> M Sexp
evBindsS = \case
  EvBinds bag -> tagged "evbinds" <$> mapM evBindS (bagToList bag)
  TcEvBinds _ -> pure (A "evbinds-unzonked")

evBindS :: EvBind -> M Sexp
evBindS eb = do
  l <- binderS (eb_lhs eb)
  r <- evTermS (eb_rhs eb)
  pure (tagged "evbind" [l, r])

evTermS :: EvTerm -> M Sexp
evTermS = \case
  EvExpr ce -> coreS ce
  EvTypeable t _ -> pure (tagged "typeable" [typeS t])
  EvFun {} -> pure (A "evfun")

-- | Evidence is a Core expression: dictionary functions applied to types
--   and other dictionaries.
coreS :: CoreExpr -> M Sexp
coreS = \case
  Var v -> varS v
  App f (Type t) -> (\f' -> tagged "tyapp" [f', typeS t]) <$> coreS f
  App f (Coercion _) -> coreS f
  App f a -> do
    f' <- coreS f
    a' <- coreS a
    pure (tagged "evapp" [f', a'])
  Cast e _ -> coreS e
  Tick _ e -> coreS e
  Type t -> pure (typeS t)
  Lit l -> pure (tagged "corelit" [S (showPprUnsafe l)])
  _ -> pure (A "core-other")

wrapS :: HsWrapper -> Sexp -> M Sexp
wrapS w e = case w of
  WpHole -> pure e
  WpCompose a b -> wrapS b e >>= wrapS a
  WpTyApp t -> pure (tagged "tyapp" [e, typeS t])
  WpEvApp ev -> (\d -> tagged "evapp" [e, d]) <$> evTermS ev
  WpTyLam v -> pure (tagged "tylam" [S (getOccString v), e])
  WpEvLam v -> (\b -> tagged "evlam" [b, e]) <$> binderS v
  WpLet ebs -> (\bs -> tagged "evlet" [bs, e]) <$> evBindsS ebs
  WpCast _ -> pure (tagged "cast" [e])
  WpFun {} -> pure (tagged "wpfun" [e])
  WpMultCoercion _ -> pure e

-- Expressions --------------------------------------------------------------

lexprS :: LHsExpr GhcTc -> M Sexp
lexprS (L _ e) = exprS e

exprS :: HsExpr GhcTc -> M Sexp
exprS ex = case ex of
  HsVar _ (L _ v) -> varS v
  HsRecSel _ fo -> varS (foExt fo)
  HsOverLit _ ol -> overLitS ol
  HsLit _ l -> pure (litS l)
  HsLam _ variant mg -> (\m -> tagged "lam" [A (lamName variant), m]) <$> mgS mg
  HsApp _ f a -> do
    f' <- lexprS f
    a' <- lexprS a
    pure (tagged "app" [f', a'])
  HsAppType ty e _ -> (\e' -> tagged "tyapp" [e', typeS ty]) <$> lexprS e
  NegApp _ e se -> do
    e' <- lexprS e
    n <- syntaxS se
    pure (tagged "negapp" [e', n])
  HsPar _ e -> lexprS e
  ExplicitTuple _ args _ -> tagged "tuple" <$> mapM tupArgS args
  HsCase _ scrut mg -> do
    s <- lexprS scrut
    m <- mgS mg
    pure (tagged "case" [s, m])
  HsIf _ c t e -> do
    c' <- lexprS c
    t' <- lexprS t
    e' <- lexprS e
    pure (tagged "if" [c', t', e'])
  HsMultiIf ty grhss -> (\gs -> tagged "multiif" [typeS ty, list gs]) <$> mapM grhsS grhss
  HsLet _ bs body -> do
    bs' <- localBindsS bs
    b <- lexprS body
    pure (tagged "let" [bs', b])
  HsDo ty flav (L _ stmts) -> (\ss -> tagged "do" [A (doName flav), typeS ty, list ss]) <$> mapM stmtS stmts
  ExplicitList ty es -> (\es' -> tagged "list" [typeS ty, list es']) <$> mapM lexprS es
  RecordCon {rcon_con = L _ con, rcon_flds = flds} -> do
    fs <- forM (rec_flds flds) $ \(L _ fb) -> do
      sel <- varS (foExt (unLoc (hfbLHS fb)))
      v <- lexprS (hfbRHS fb)
      pure (tagged "field" [sel, v])
    pure (tagged "reccon" [conLikeS con, list fs, A (maybe "nodots" (const "dotdot") (rec_dotdot flds))])
  ExprWithTySig _ e _ -> lexprS e
  ArithSeq w _ info -> do
    w' <- exprS w
    i <- case info of
      From a -> (\x -> tagged "from" [x]) <$> lexprS a
      FromThen a b -> (\x y -> tagged "fromthen" [x, y]) <$> lexprS a <*> lexprS b
      FromTo a b -> (\x y -> tagged "fromto" [x, y]) <$> lexprS a <*> lexprS b
      FromThenTo a b c -> (\x y z -> tagged "fromthento" [x, y, z]) <$> lexprS a <*> lexprS b <*> lexprS c
    pure (tagged "arith" [w', i])
  HsPragE _ _ e -> lexprS e
  XExpr x -> case x of
    WrapExpr (HsWrap w e) -> exprS e >>= wrapS w
    ExpandedThingTc orig e -> (\e' -> tagged "expanded" [origS orig, e']) <$> exprS e
    ConLikeTc con _ _ -> pure (conLikeS con)
    HsTick _ e -> lexprS e
    HsBinTick _ _ e -> lexprS e
  _ -> pure (unsupported ex)

origS :: HsThingRn -> Sexp
origS = \case
  OrigExpr e -> tagged "expr" [S (showConstr (toConstr e))]
  OrigStmt _ -> A "stmt"
  OrigPat _ -> A "pat"

lamName :: HsLamVariant -> String
lamName = \case
  LamSingle -> "single"
  LamCase -> "case"
  LamCases -> "cases"

doName :: HsDoFlavour -> String
doName = \case
  DoExpr _ -> "do"
  MDoExpr _ -> "mdo"
  GhciStmtCtxt -> "ghci"
  ListComp -> "listcomp"
  MonadComp -> "monadcomp"

tupArgS :: HsTupArg GhcTc -> M Sexp
tupArgS = \case
  Present _ e -> lexprS e
  Missing (Scaled _ t) -> pure (tagged "missing" [typeS t])

syntaxS :: SyntaxExpr GhcTc -> M Sexp
syntaxS = \case
  SyntaxExprTc {syn_expr = e} -> exprS e
  NoSyntaxExprTc -> pure (A "nosyntax")

conLikeS :: ConLike -> Sexp
conLikeS = \case
  RealDataCon dc -> tagged "g" [S (modOf dc), S (getOccString dc), A "con"]
  PatSynCon ps -> tagged "unsupported" [S "PatSynCon", S (getOccString ps)]

litS :: HsLit GhcTc -> Sexp
litS l = case l of
  HsChar _ c -> tagged "char" [I (toInteger (fromEnum c))]
  HsString _ fs -> tagged "string" [S (unpackFS fs)]
  HsInt _ il -> tagged "int" [I (il_value il)]
  HsIntPrim _ n -> tagged "intprim" [I n]
  HsWordPrim _ n -> tagged "wordprim" [I n]
  HsInteger _ n t -> tagged "integer" [I n, typeS t]
  HsRat _ fl t -> tagged "rat" [fracS fl, typeS t]
  HsStringPrim _ bs -> tagged "stringprim" [S (map (toEnum . fromIntegral) (BS.unpack bs))]
  HsWord64Prim _ n -> tagged "wordprim" [I n]
  HsInt64Prim _ n -> tagged "intprim" [I n]
  HsFloatPrim _ fl -> tagged "floatprim" [fracS fl]
  HsDoublePrim _ fl -> tagged "doubleprim" [fracS fl]
  HsCharPrim _ c -> tagged "charprim" [I (toInteger (fromEnum c))]
  _ -> unsupported l

fracS :: FractionalLit -> Sexp
fracS fl =
  let r = rationalFromFractionalLit fl
      txt = case fl_text fl of
        SourceText s -> unpackFS s
        NoSourceText -> ""
   in tagged "frac" [I (numerator r), I (denominator r), S txt]

overLitS :: HsOverLit GhcTc -> M Sexp
overLitS (OverLit ext val) = do
  w <- exprS (ol_witness ext)
  let v = case val of
        HsIntegral il -> tagged "int" [I (il_value il)]
        HsFractional fl -> fracS fl
        HsIsString _ fs -> tagged "string" [S (unpackFS fs)]
  pure (tagged "olit" [v, typeS (ol_type ext), w])

-- Patterns -----------------------------------------------------------------

lpatS :: LPat GhcTc -> M Sexp
lpatS (L _ p) = patS p

patS :: Pat GhcTc -> M Sexp
patS p = case p of
  WildPat ty -> pure (tagged "pwild" [typeS ty])
  VarPat _ (L _ v) -> (\b -> tagged "pvar" [b]) <$> binderS v
  LazyPat _ q -> (\x -> tagged "plazy" [x]) <$> lpatS q
  AsPat _ (L _ v) q -> do
    b <- binderS v
    q' <- lpatS q
    pure (tagged "pas" [b, q'])
  ParPat _ q -> lpatS q
  BangPat _ q -> (\x -> tagged "pbang" [x]) <$> lpatS q
  ListPat ty qs -> (\xs -> tagged "plist" [typeS ty, list xs]) <$> mapM lpatS qs
  TuplePat _ qs _ -> (\xs -> tagged "ptuple" [list xs]) <$> mapM lpatS qs
  ConPat ext (L _ con) details -> do
    args <- case details of
      PrefixCon _ qs -> (\xs -> tagged "args" xs) <$> mapM lpatS qs
      InfixCon a b -> (\x y -> tagged "args" [x, y]) <$> lpatS a <*> lpatS b
      RecCon flds -> do
        fs <- forM (rec_flds flds) $ \(L _ fb) -> do
          sel <- varS (foExt (unLoc (hfbLHS fb)))
          v <- lpatS (hfbRHS fb)
          pure (tagged "pfield" [sel, v])
        pure (tagged "fields" fs)
    pure (tagged "pcon" [conLikeS con, list (map typeS (cpt_arg_tys ext)), args])
  ViewPat _ e q -> do
    e' <- lexprS e
    q' <- lpatS q
    pure (tagged "pview" [e', q'])
  LitPat _ l -> pure (tagged "plit" [litS l])
  NPat ty (L _ ol) neg _ -> do
    o <- overLitS ol
    pure (tagged "pnlit" [o, A (maybe "pos" (const "neg") neg), typeS ty])
  NPlusKPat _ (L _ v) (L _ ol) _ _ _ -> do
    b <- binderS v
    o <- overLitS ol
    pure (tagged "pnplusk" [b, o])
  SigPat _ q _ -> lpatS q
  XPat (CoPat _ q _) -> patS q
  XPat (ExpansionPat _ q) -> patS q
  _ -> pure (unsupported p)
