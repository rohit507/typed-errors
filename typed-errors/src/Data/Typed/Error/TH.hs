{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Data.Typed.Error.TH (makeErrClassHelpers) where

import Intro hiding (Type)
import Language.Haskell.TH
-- import Language.Haskell.TH.Syntax
import Language.Haskell.TH.PprLib hiding ((<>))
import Data.Data hiding (typeOf, typeRep,TypeRep)
-- import Data.Type.Equality
-- import Data.Constraint hiding (Class)
import Data.Typed.Error.Internal
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error.TH.Types
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Type.Reflection
import Data.Generics.Schemes

makeErrClassHelpers :: TypedErrorRules -> Name -> Q [Dec]
makeErrClassHelpers ter n = do
  i <- reify n
  res <- runREQ ter $ do
    ci <- genClassInfo i
    (gi, gds) <- genGADTDecs ci
    teids <- genTErrClassInst ci gi
    grids   <- genGADTRewriteInst ci gi
    (gci, gcds) <- genGetClass ci gi
    ggids <- genGADTGetInst ci gi gci
    gteids <- genTypErrGetInst ci gi gci
    patds <- genErrPatterns ci gi gci
    tfds  <- genThrowFuncs ci
    wfds  <- genWhileFuncs ci
    pure $ gds <> [teids,grids,gcds,ggids,gteids] <> patds <> tfds <> wfds
  case res of
    Left e -> do
      reportError $ show e
      pure []
    Right ds -> do
      if (dryRun ter)
      then (reportWarning . show . sep . map ppr $ ds) *> pure []
      else pure ds

liftSYB :: forall a b. (Typeable a, Data b) => (a -> a) -> b -> b
liftSYB f b = case eqTypeRep (typeRep @a) (typeRep @b) of
  Nothing -> b
  Just HRefl -> f b

genClassInfo :: Info -> REQ (ClassInfo Class)
genClassInfo (ClassI d i) = case d of
  ClassD _ name [] _ _ -> whileWithinClass name throwMissingErrorTyVar
  ClassD ccxt name tyVars funDeps dec
    -> whileWithinClass name $ do
      (cTyVs, eTyV) <- splitTyVars tyVars
      ClassInfo
        <$> (pure $ C ccxt)
        <*> (pure $ C name)
        <*> (pure $ C cTyVs)
        <*> (pure $ C eTyV)
        <*> (pure $ C funDeps)
        <*> (Map.fromList <$> traverse (genFuncInfo tyVars ccxt) dec)
        <*> (pure $ C i)
  d' -> throwNonClassDec d'
  where

    splitTyVars :: [TyVarBndr] -> REQ ([TyVarBndr], TyVarBndr)
    splitTyVars l = case lastMay l of
      Nothing   -> throwMissingErrorTyVar
      Just eTyV -> pure (initDef [] l,eTyV)

    genFuncInfo :: C 'TyVars -> C 'Ctxt ->  Dec
      -> REQ (Name, FuncInfo Class)
    genFuncInfo t c (SigD nm typ)
      = let (a,b,ps) = extrFromTyp t c typ in do
          -- liftQ $ reportWarning . show $ (a,b,ps)
          pure . (nm,) $
            FuncInfo
              (C a)
              (C nm)
              (C b)
              (map C ps :: [Class 'Param])
    genFuncInfo _ _ n = throwInvalidClassDec n

    extrFromTyp :: C 'TyVars -> C 'Ctxt -> Type
        -> (C 'Ctxt, C 'TyVars, [C 'Param])
    extrFromTyp ctv ccxt (ForallT ftv fcxt typ)
      | ftv == ctv = case extrFromTyp ctv ccxt typ of
          (a, b, p) -> (fcxt <> a,  b, p)
      | otherwise = case extrFromTyp ctv ccxt typ of
          (a, b, p) -> (fcxt <> a, ftv <> b, p)
    extrFromTyp ctv ccxt (AppT (AppT ArrowT p) t)
      = let (a,b,ps) = extrFromTyp ctv ccxt t in (a,b,p : ps)
    extrFromTyp _ctv _ccxt t = (mempty, mempty, [t])

genClassInfo i = throwNonClassInfo i

nameToStr :: Name -> String
nameToStr = nameBase

tyVarName :: TyVarBndr -> Name
tyVarName (PlainTV n) = n
tyVarName (KindedTV n _) = n

appTypes :: Type -> [Type] -> Type
appTypes = foldl' AppT

appFuncTypes :: [Type] -> Type
appFuncTypes (v : []) = v
appFuncTypes (v : vs) = AppT (AppT ArrowT v) (appFuncTypes vs)
appFuncTypes _ = panic "empty list not allowed"

genGADTDecs :: ClassInfo Class -> REQ (ClassInfo GADT, [Dec])
genGADTDecs (ClassInfo (C ctxt) (C nm) (C tv) (C etv) (C _fd) fn (C _inst))
  = whileBuildingGADT nm $ do
      -- liftQ . reportError . show $ etv
      (ci,gName,gDec) <- genGADTDef

      etDec <- errorTypeInst gName
      pure (ci,[gDec,etDec])

  where

    errorTypeInst :: Name -> REQ Dec
    errorTypeInst gnm = do
      let fvar = appTypes (ConT nm) (map (VarT . tyVarName) tv)
          vars = map (VarT . tyVarName) tv
      pure . TySynInstD ''ErrorType . TySynEqn [fvar] $ appTypes (ConT gnm) vars

    genGADTDef :: REQ (ClassInfo GADT, Name, Dec)
    genGADTDef = do
      gName <- (nameGADT <$> ask) <*> pure (nameToStr nm) >>= \case
        Nothing -> throwInvalidClassNameForGADT nm
        Just a  -> pure $ mkName a
      cons <- traverse (genGADTConst gName) fn
      let dec = DataD (mempty) gName (tv <> [etv]) Nothing (snd <$> Map.elems cons) []
          ci = ClassInfo (G mempty) (G gName) (G ()) (G StarT) (G ()) (fst <$> cons) (G ())
      pure (ci,gName, dec)

    genGADTConst :: Name -> FuncInfo Class -> REQ (FuncInfo GADT, Con)
    genGADTConst gName (FuncInfo (C fCxt) (C fnm) (C ftv) (map getC -> p))
      = whileWithinFunction fnm $ do
          cName <- ((\ f -> f (nameBase nm) (nameBase fnm)) . nameGADTCons <$> ask) >>= \case
             Nothing -> do
               throwInvalidFuncNameForGADT nm fnm
             Just a  -> pure $ mkName a
          (rType,ps) <- case lastMay p of
            Nothing -> throwFunctionWithNoParams
            Just e  -> pure (e, initDef [] p)
          unless (rType == VarT (tyVarName etv)) $ throwInvalidFuncType rType
          let fCtxt = ctxt <> fCxt
              fi     = FuncInfo (G fCtxt) (G cName) (G ()) (map G ps)
              rType' = appTypes (ConT gName) (map (VarT . tyVarName) (tv <> [etv]))
              ftype  = appFuncTypes (ps <> [rType'])
              con    = ForallC (tv <> ftv <> [etv]) fCtxt $ GadtC [cName] [] ftype
          pure (fi, con)

varNameList :: [String]
varNameList = map (:[]) letters <> [ p : r | p <- letters, r <- varNameList]
  where
    letters :: String
    letters = ['a'..'z']

genTErrClassInst :: ClassInfo Class -> ClassInfo GADT -> REQ Dec
genTErrClassInst
  (ClassInfo (C  ccxt) (C  cnm) (C  ctv) (C cetv) (C _cfd) cfns (C _cinst))
  (ClassInfo (G _gcxt) (G _gnm) (G _gtv) (G _getv) (G _gfd) gfns (G _ginst))
    = whileBuildingClassInst (mkName "TypedError p") $ do
           funs <- (Map.mergeA
              (Map.traverseMissing $ \ k _ ->
                  throwExtraFuncInfo k (someTypeRep $ typeRep @TypedError))
              (Map.traverseMissing $ \ k _ ->
                  throwMissingFuncInfo k (someTypeRep $ typeRep @TypedError))
              (Map.zipWithAMatched $ \ _ a b -> genMemberFunc a b)
              cfns gfns)
           tyVar <- liftQ $ VarT <$> newName "p"
           let tepvar = (AppT (ConT ''TypedError) tyVar)
               repetv :: Type -> Type
               repetv (VarT e)
                  | e == tyVarName cetv = tepvar
                  | otherwise = (VarT e)
               repetv e = e
               nccxt = everywhere (liftSYB repetv) ccxt
               classT = (ConT cnm)
               instT = appTypes classT $ map (VarT . tyVarName) ctv
               icxt = (AppT (AppT (ConT ''HasError) instT) tyVar) : nccxt
               typ = AppT instT tepvar
           pure $ InstanceD Nothing icxt typ (Map.elems funs)
  where

    genMemberFunc :: FuncInfo Class -> FuncInfo GADT -> REQ Dec
    genMemberFunc
      (FuncInfo (C _cfcxt) (C cfnm) (C _cftv) (  cfps))
      (FuncInfo (G _gfcxt) (G gfnm) (G _gftv) (map getG -> _gfps))
        = do params <- traverse
                         (liftQ . newName)
                         (zipWith const varNameList (initDef [] cfps))
             let pat = map VarP params
                 fexp = AppE (VarE 'toError)
                             (foldl' AppE (ConE gfnm) (map VarE params))
                 body = NormalB fexp
                 clse = Clause pat body []
             pure $ FunD cfnm [clse]

genGADTRewriteInst :: ClassInfo Class -> ClassInfo GADT -> REQ Dec
genGADTRewriteInst
  (ClassInfo (C _ccxt) (C  cnm) (C  ctv) (C _cetv) (C _cfd) cfns (C _cinst))
  (ClassInfo (G _gcxt) (G  gnm) (G _gtv) (G _getv) (G _gfd) gfns (G _ginst))
    = whileBuildingClassInst (mkName "RewriteError") $ do
           funs <- (Map.mergeA
                   (Map.traverseMissing $ \ k _ ->
                       throwExtraFuncInfo k (someTypeRep $ typeRep @TypedError))
                   (Map.traverseMissing $ \ k _ ->
                       throwMissingFuncInfo k (someTypeRep $ typeRep @TypedError))
                   (Map.zipWithAMatched $ \ _ a b -> genMemberClause a b)
                   cfns gfns)
           tyVar <- liftQ $ VarT <$> newName "e"
           let func = FunD 'rewriteError (Map.elems funs)
               cvars = map (VarT . tyVarName) ctv
               param = appTypes (ConT cnm) cvars
               gtyp  = appTypes (ConT gnm) cvars
               icxt =  AppT param tyVar -- : ccxt
               ityp = AppT (AppT (ConT ''RewriteError) tyVar) gtyp
           pure $ InstanceD Nothing [icxt] ityp [func]
  where

    genMemberClause :: FuncInfo Class -> FuncInfo GADT -> REQ Clause
    genMemberClause
      (FuncInfo (C _cfcxt) (C cfnm) (C _cftv) (  cfps))
      (FuncInfo (G _gfcxt) (G gfnm) (G _gftv) (map getG -> _gfps))
        = do params <- traverse
                         (liftQ . newName)
                         (zipWith const varNameList (initDef [] cfps))
             let pat = ConP gfnm $ map VarP params
                 fexp = (foldl' AppE (VarE cfnm) (map VarE params))
                 body = NormalB fexp
             pure $ Clause [pat] body []

-- genParamTupleTyp :: [Type] -> Type
-- genParamTupleTyp [] = ConT ''()
-- genParamTupleTyp (a:[]) = a
-- genParamTupleTyp l = appTypes (TupleT $ length l) l

-- genParamTupleExp :: [Exp] -> Exp
-- genParamTupleExp [] = ConE '()
-- genParamTupleExp (a:[]) = a
-- genParamTupleExp l = TupE l

genGetClass :: ClassInfo Class -> ClassInfo GADT -> REQ (ClassInfo GetClass, Dec)
genGetClass
  (ClassInfo (C  _ccxt) (C  cnm) (C ctv) (C cetv) (C _cfd) _cfns (C _cinst))
  (ClassInfo (G  _gcxt) (G  gnm) (G _gtv) (G _getv) (G _gfd) _gfns (G _ginst))
    = do cName :: Name <- ((\ f -> f $ nameBase cnm) . nameGetClass <$> ask) >>= \case
             Nothing -> do
               throwInvalidClassNameForGetClass cnm
             Just a  -> pure $ mkName a
         fName :: Name <- ((\ f -> f $ nameBase cnm) . nameGetFunc <$> ask) >>= \case
             Nothing -> do
               throwInvalidClassNameForGetClass cnm
             Just a  -> pure $ mkName a
         do
           let params = map (VarT . tyVarName) ctv
               cType = appTypes (ConT cnm) params
               atv = tyVarName cetv
           ftv <- liftQ $ newName "f"
           let cns = [AppT cType (VarT ftv)] --, AppT cType (VarT atv)]
           let
               tvs = map PlainTV [ftv, atv]
               fd  = FunDep [ftv] [atv]
               mType = AppT (ConT ''Maybe)
                            (appTypes (ConT gnm) (params <> [VarT atv]))
               tpType = AppT (AppT ArrowT (VarT ftv)) mType
               fnType = ForallT [] cns tpType
               fnDec = SigD fName fnType
               ci = ClassInfo
                    (GC cns)
                    (GC cName)
                    (GC $ map (VarT . tyVarName) ctv)
                    (GC (ftv,atv))
                    (GC fName)
                    []
                    (GC ())
               dec = ClassD mempty cName (ctv <> tvs) [fd] [fnDec]
           pure (ci, dec)


genGADTGetInst :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass -> REQ Dec
genGADTGetInst
  (ClassInfo (C  _ccxt)  (C  ccnm) (C _cctv) (C _ccetv) (C _ccfd) _ccfns (C _ccinst))
  (ClassInfo (G  _gcxt) (G   gnm) (G  _gtv) (G  _getv) (G  _gfd) _gfns (G  _ginst))
  (ClassInfo (GC _gccxt) (GC  cnm) (GC  ctv) (GC (_ftv,atv)) (GC fname) _cfns (GC cinst))
    = whileBuildingClassInst (mkName "Get GADT") $ do
       let fbod = NormalB $ ConE 'Just
           impl = FunD fname [Clause [] fbod []]
           decs = [impl]
           ftv' = appTypes (ConT gnm) (ctv <> [VarT atv])
           iTyp = appTypes (ConT cnm) (ctv <> [ftv', VarT atv])
           cons = map (\ n -> appTypes (ConT ccnm) (ctv <> [n])) [{-ftv',-} VarT atv]
       pure $ InstanceD Nothing cons iTyp decs


genTypErrGetInst :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass -> REQ Dec
genTypErrGetInst
  (ClassInfo (C  _ccxt)  (C  ccnm) (C  _cctv) (C _ccetv) (C _ccfd) _ccfns (C _ccinst))
  (ClassInfo (G  _gcxt) (G   _gnm) (G  _gtv) (G  _getv) (G  _gfd) _gfns (G  _ginst))
  (ClassInfo (GC _gccxt) (GC  cnm) (GC  ctv) (GC (_ftv,_atv)) (GC fname) _cfns (GC cinst))
    = whileBuildingClassInst (mkName "Get GADT") $ do
       pVar <- liftQ $ newName "p"
       let leType = AppT (ConT ''TypedError) (VarT pVar)
           impl = FunD fname [Clause [] fbod []]
           decs = [impl]
           fbod = NormalB $ AppTypeE (VarE 'fromError) (appTypes (ConT ccnm) ctv)
           iTyp = appTypes (ConT cnm) (ctv <> [leType, leType])
           ecpre = appTypes (ConT ccnm) ctv
           _cons = AppT ecpre leType
           mcon = AppT (AppT (ConT ''HasError) ecpre) (VarT pVar)
       pure $ InstanceD Nothing [mcon] iTyp decs


genErrPatterns :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass
  -> REQ [Dec]
genErrPatterns
  (ClassInfo (C  ccxt)  (C  cnm) (C  ctv) (C  cetv) (C _cfd) ccfns (C _ccinst))
  (ClassInfo (G  _gcxt) (G   gnm) (G _gtv) (G _getv) (G _gfd) gfns (G  _ginst))
  (ClassInfo (GC _gccxt) (GC  gcnm)
    (GC _gctv) (GC (ftv,atv)) (GC gcfname) _gcfns (GC _leName))
    = do cpds <- genClassPattern
         fnds <- for (Map.keys ccfns) $ \ n ->
           case (,) <$> Map.lookup n ccfns <*> Map.lookup n gfns of
             Nothing -> panic "error"
             Just (cf, gf) -> genFuncPattern cf gf
         pure $ cpds <> (mconcat fnds)

  where

    genClassPattern :: REQ [Dec]
    genClassPattern = do
      pName <- ((\ f -> f $ nameBase cnm) . nameClassPattern <$> ask) >>= \case
        Nothing -> throwInvalidClassNameForGetClass cnm
        Just a  -> pure $ mkName a
      pVar <- liftQ $ newName "p"
      xVar <- liftQ $ newName "x"
      let leType = AppT (ConT ''TypedError) (VarT pVar)
          repetv :: Type -> Type
          repetv (VarT e)
             | e == tyVarName cetv = leType
             | otherwise = (VarT e)
          repetv e = e
          nccxt = everywhere (liftSYB repetv) ccxt
          ctvType =  (map (VarT . tyVarName) ctv)
          clsCns = appTypes (ConT cnm) ctvType
          gCns = appTypes (ConT gnm) ctvType
          hasErr = AppT (AppT (ConT ''HasError) clsCns) (VarT pVar)
          -- iTyp = appTypes (ConT cnm) (ctvType <> [leType, VarT atv])
          synDirClause = Clause [VarP xVar]
            (NormalB $ AppE (VarE 'toError) (VarE xVar)) []
          synDir = ExplBidir [synDirClause]
          synArgs = PrefixPatSyn [xVar]
          patPat = ViewP (AppTypeE (VarE 'fromError) clsCns)
                         (ConP 'Just [VarP xVar])
          patSynTyp = ForallT (ctv <> [PlainTV pVar]) (hasErr : nccxt) $ ForallT [] nccxt $
            AppT (AppT ArrowT (AppT gCns leType)) leType
      pure [ PatSynSigD pName patSynTyp
           , PatSynD pName synArgs synDir patPat]


    genFuncPattern :: FuncInfo Class -> FuncInfo GADT -> REQ [Dec]
    genFuncPattern
      (FuncInfo (C  cfcxt) (C cfnm) (C  cftv) (map getC ->  cfps))
      (FuncInfo (G _gfcxt) (G gfnm) (G _gftv) (map getG -> _gfps))
        = do
          fName <- ((\ f -> f (nameBase cnm) $ nameBase cfnm) . nameFuncPattern <$> ask) >>= \case
             Nothing -> throwInvalidClassNameForGetClass cnm
             Just a  -> pure $ mkName a
          params <- traverse
             (liftQ . newName)
             (zipWith const varNameList (initDef [] cfps))
          let utv = ctv <> [PlainTV ftv,PlainTV atv]
              ctvType =  (map (VarT . tyVarName) ctv)
              ftyp = VarT ftv
              atyp = VarT atv
              clsCns  = appTypes (ConT cnm) ctvType
              gclsCns = appTypes (ConT gcnm) ctvType
              -- isMember = any (== atyp) cfps
              -- extraCnst True = [AppT (AppT EqualityT ftyp) atyp]
              -- extraCnst False = []
              ucxt = [ AppT clsCns ftyp
                     --, AppT clsCns atyp
                     , AppT (AppT gclsCns ftyp) atyp]
              etv = cftv
              ecxt = cfcxt
              appF (l : []) = l
              appF (l : ls) = AppT (AppT ArrowT l) (appF ls)
              appF _ = panic "unepected empty list"
              -- uptype :: Type -> Type
              -- uptype a
              --   | a == atyp = atyp
              --   | otherwise = a
              -- mcfps = map uptype $ initDef [] cfps
              mcfps = initDef [] cfps
              ptyp = appF (mcfps <> [ftyp])
              patTyp = ForallT utv ucxt $ ForallT etv ecxt $ ptyp
              patSynArgs = PrefixPatSyn params
              patPat = ViewP (foldl' AppTypeE (VarE gcfname)
                                              (ctvType <> [ftyp,atyp]))
                             (ConP 'Just [ConP gfnm (map VarP params)])
          pure [PatSynSigD fName patTyp
               ,PatSynD fName patSynArgs Unidir patPat]

genThrowFuncs :: ClassInfo Class -> REQ [Dec]
genThrowFuncs
  (ClassInfo (C  _ccxt) (C  cnm) (C  ctv) (C  cetv) (C _cfd) cfns (C _cinst))
    = whileBuildingClassInst (mkName "ThrowFuncs") $ do
        mconcat <$> traverse genThrowFunc (Map.elems cfns)

  where

    genThrowFunc :: FuncInfo Class -> REQ [Dec]
    genThrowFunc
      (FuncInfo (C cfcxt) (C cfnm) (C cftv) (map getC -> cfps))
        = do
          let mName f = f (nameBase cnm) (nameBase cfnm)
          fname <- mName . nameThrow <$> ask
          skip  <- skipExistingThrow <$> ask
          case fname of
            Nothing -> throwInvalidClassNameForGetClass cnm
            Just a  -> do
              exist <- liftQ $ isJust <$> lookupValueName a
              case skip && exist of
                True -> pure []
                False -> do
                   fName <- pure $ mkName a
                   mVar <- liftQ $ newName "m"
                   aVar <- liftQ $ newName "a"
                   pars <- initDef [] <$> (liftQ $ traverse newName
                                      $ zipWith const varNameList cfps)
                   let tvars = ctv <> cftv <> [cetv, PlainTV mVar, PlainTV aVar]
                 -- etcParams = map (VarT . tyVarName) ctv
                       evar =  (VarT $ tyVarName cetv)
                 -- ecxt = AppT (appTypes (ConT cnm) etcParams) evar
                       mecxt = AppT  (AppT (ConT ''MonadError) evar) (VarT mVar)
                       cxt' = mecxt : (cfcxt)
                       mtyp = AppT (VarT mVar) (VarT aVar)
                       fType = ForallT tvars cxt' $ appFuncTypes (initDef [] cfps <> [mtyp])
                       sig = SigD fName fType
                       cPat = map VarP pars
                       fExp = AppE (VarE 'throwError)
                          (foldl' AppE (VarE cfnm) $ map VarE pars)
                       func = FunD fName [Clause cPat (NormalB $ fExp) []]
                   pure [sig,func]

genWhileFuncs :: ClassInfo Class -> REQ [Dec]
genWhileFuncs
  (ClassInfo (C  _ccxt) (C  cnm) (C  ctv) (C  cetv) (C _cfd) cfns (C _cinst))
    = whileBuildingClassInst (mkName "ThrowFuncs") $ do
        mconcat <$> traverse genWhileFunc (Map.elems cfns)

  where

    genWhileFunc :: FuncInfo Class -> REQ [Dec]
    genWhileFunc
      (FuncInfo (C cfcxt) (C cfnm) (C cftv) (map getC -> cfps)) = do
          let mName f = f (nameBase cnm) (nameBase cfnm)
          fname <- mName . nameWhile <$> ask
          skip  <- skipExistingWhile <$> ask
          case fname of
            Nothing -> throwInvalidClassNameForGetClass cnm
            Just a  -> do
              exist <- liftQ $ isJust <$> lookupValueName a
              case skip && exist of
                True -> pure []
                False -> do
                  fName <- pure $ mkName a
                  mVar <- liftQ $ newName "m"
                  aVar <- liftQ $ newName "a"
                  ps <- pure $ initDef [] cfps
                  case (,) <$> initMay ps <*> lastMay ps of
                    Nothing -> pure []
                    Just (is, mv)
                       | mv /= (VarT $ tyVarName cetv) -> pure []
                       | otherwise -> do
                          pars <- (liftQ $ traverse newName
                                          $ zipWith const varNameList is)
                          let tvars = ctv <> cftv <> [cetv, PlainTV mVar, PlainTV aVar]
                              -- etcParams = map (VarT . tyVarName) ctv
                              evar =  (VarT $ tyVarName cetv)
                              -- ecxt = AppT (appTypes (ConT cnm) etcParams) evar
                              mecxt = AppT  (AppT (ConT ''MonadError) evar) (VarT mVar)
                              cxt' = mecxt : (cfcxt)
                              mtyp = AppT (VarT mVar) (VarT aVar)
                              fType = ForallT tvars cxt' $ appFuncTypes (is <> [mtyp, mtyp])
                              sig = SigD fName fType
                              cPat = map VarP pars <> [VarP mVar]
                              fExp = AppE (AppE (VarE 'catchError) (VarE mVar))
                                (AppE (AppE (VarE $ mkName ".") (VarE 'throwError))
                                   (foldl' AppE (VarE cfnm)
                                     $ map VarE pars))
                              func = FunD fName [Clause cPat (NormalB $ fExp) []]
                           in pure [sig,func]
