{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Data.Typed.Error.TH (testAnn) where

import Intro hiding (Type)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.PprLib hiding ((<>))
import Data.Data hiding (typeOf, typeRep,TypeRep)
import Data.Type.Equality
import Data.Constraint hiding (Class)
import Data.Typed.Error.Internal
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error.TH.Types
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Type.Reflection


testAnn :: Name -> Q [Dec]
testAnn n = do
  i <- reify n
  res <- runREQ defTER $ do
    ci <- genClassInfo i
    (gi, gds) <- genGADTDecs ci
    teids <- genTErrClassInst ci gi
    grids   <- genGADTRewriteInst ci gi
    (gci, gcds) <- genGetClass ci gi
    ggids <- genGADTGetInst ci gi gci
    pure $ gds <> [teids,grids,gcds,ggids]
  case res of
    Left e -> do
      reportError $ show e
      pure []
    Right ds -> do
      when (dryRun defTER) $ reportWarning . show . sep . map ppr $ ds
      pure ds

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

appFuncTypes :: Type -> [Type] -> Type
appFuncTypes n v = foldr (\ p t -> AppT (AppT ArrowT p) t) n v

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
              ftype  = appFuncTypes rType' ps
              con    = ForallC (tv <> ftv <> [etv]) fCtxt $ GadtC [cName] [] ftype
          pure (fi, con)

varNameList :: [String]
varNameList = map (:[]) letters <> [ p : r | p <- letters, r <- varNameList]
  where
    letters :: String
    letters = ['a'..'z']

genTErrClassInst :: ClassInfo Class -> ClassInfo GADT -> REQ Dec
genTErrClassInst
  (ClassInfo (C  ccxt) (C  cnm) (C  ctv) (C  cetv) (C _cfd) cfns (C _cinst))
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
           let classT = (ConT cnm)
               instT = appTypes classT $ map (VarT . tyVarName) ctv
               icxt = (AppT (AppT (ConT ''HasError) instT) tyVar) : ccxt
               typ = AppT instT (AppT (ConT ''TypedError) tyVar)
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
  (ClassInfo (C  ccxt) (C  cnm) (C  ctv) (C _cetv) (C _cfd) cfns (C _cinst))
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
               icxt =  AppT param tyVar : ccxt
               ityp = AppT (AppT (ConT ''RewriteError) tyVar) gtyp
           pure $ InstanceD Nothing icxt ityp [func]
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

genParamTupleTyp :: [Type] -> Type
genParamTupleTyp [] = ConT ''()
genParamTupleTyp (a:[]) = a
genParamTupleTyp l = appTypes (TupleT $ length l) l

genParamTupleExp :: [Exp] -> Exp
genParamTupleExp [] = ConE '()
genParamTupleExp (a:[]) = a
genParamTupleExp l = TupE l

genGetClass :: ClassInfo Class -> ClassInfo GADT -> REQ (ClassInfo GetClass, Dec)
genGetClass
  (ClassInfo (C  ccxt) (C  cnm) (C ctv) (C cetv) (C _cfd) cfns (C _cinst))
  (ClassInfo (G  gcxt) (G  gnm) (G gtv) (G getv) (G _gfd) gfns (G _ginst))
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
           (leName, leDec) <- genLiftErrDec (VarT ftv) (VarT atv)
           funs <- traverse (genMemberSig cns (VarT ftv) (VarT atv)) cfns
           let fis = map fst funs
               fnDecs = map snd $ Map.elems funs

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
                    (GC leName)
               dec = ClassD mempty cName (ctv <> tvs) [fd] [leDec,fnDec]
           pure (ci, dec)

  where

    genLiftErrDec :: Type -> Type -> REQ (Name, Dec)
    genLiftErrDec ftv atv = do
      fName <- ($ nameBase cnm) . nameGetLift <$> ask >>= \case
        Nothing -> do
          throwInvalidClassNameForGetClass cnm
        Just a -> pure $ mkName a
      pure . (fName,) $ SigD fName (AppT (AppT ArrowT ftv) atv)

    -- FIXME :: Clean this up so that you can use it w/o being awful
    genMemberSig :: [Type] -> Type -> Type
      -> FuncInfo Class -> REQ (FuncInfo GetClass, Dec)
    genMemberSig cns ftv _atv
      (FuncInfo (C cfcxt) (C cfnm) (C cftv) (map getC -> cfps))
        =  do fName <- (\ f -> (nameGetFunc f) (nameBase cnm))
                <$> ask >>= \case
                  Nothing -> do
                    throwInvalidClassNameForGetClass cnm
                  Just a -> pure $ mkName a
              whileWithinFunction fName $
                 let cfps' = initDef [] cfps
                     cxt' = ccxt <> cfcxt
                     cxt'' = genParamTupleTyp $ cxt'
                     dTyp = AppT (ConT ''Dict) cxt''
                     pTyp = genParamTupleTyp cfps'
                     -- mType = AppT (ConT ''Maybe) (AppT (AppT (TupleT 2) dTyp) pTyp)
                     mType = AppT (ConT ''Maybe) (appTypes (ConT gnm) cns)
                     tpType = AppT (AppT ArrowT ftv) mType
                     fnType = ForallT [] cns tpType
                     fi = FuncInfo (GC ccxt) (GC fName) (GC []) (map GC cfps')
                  in pure (fi, SigD fName tpType)

genGADTGetInst :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass -> REQ Dec
genGADTGetInst
  (ClassInfo (C  _ccxt)  (C  ccnm) (C  cctv) (C ccetv) (C ccfd) ccfns (C ccinst))
  (ClassInfo (G  _gcxt) (G   gnm) (G  _gtv) (G  _getv) (G  _gfd) gfns (G  ginst))
  (ClassInfo (GC _gccxt) (GC  cnm) (GC  ctv) (GC (ftv,atv)) (GC fname) cfns (GC cinst))
    = whileBuildingClassInst (mkName "Get GADT") $ do
       let fbod = NormalB $ ConE 'Just
           impl = FunD fname [Clause [] fbod []]
           decs = [genLiftErrLift, impl]
           ftv' = appTypes (ConT gnm) (ctv <> [VarT atv])
           iTyp = appTypes (ConT cnm) (ctv <> [ftv', VarT atv])
           cons = map (\ n -> appTypes (ConT ccnm) (ctv <> [n])) [ftv', VarT atv]
       pure $ InstanceD Nothing cons iTyp decs

  where

    genLiftErrLift :: Dec
    genLiftErrLift = FunD cinst [Clause [] (NormalB $ VarE 'rewriteError) []]

genTypErrGetInst :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass -> REQ Dec
genTypErrGetInst
  (ClassInfo (C  _ccxt)  (C  ccnm) (C  cctv) (C ccetv) (C ccfd) ccfns (C ccinst))
  (ClassInfo (G  _gcxt) (G   gnm) (G  _gtv) (G  _getv) (G  _gfd) gfns (G  ginst))
  (ClassInfo (GC _gccxt) (GC  cnm) (GC  ctv) (GC (ftv,atv)) (GC fname) cfns (GC cinst))
    = whileBuildingClassInst (mkName "Get GADT") $ do
       pVar <- liftQ $ newName "p"
       let leType = AppT (ConT 'TypedError) (VarT pVar)
           impl = FunD fname [Clause [] fbod []]
           decs = [genLiftErrLift, impl]
           fbod = NormalB $ AppTypeE (VarE 'fromError) (appTypes (ConT ccnm) ctv)
           iTyp = appTypes (ConT cnm) (ctv <> [leType, VarT atv])
           cons = map (\ n -> appTypes (ConT ccnm) (ctv <> [n])) [leType, VarT atv]
       pure $ InstanceD Nothing cons iTyp decs

  where

    genLiftErrLift :: Dec
    genLiftErrLift = FunD cinst [Clause [] (NormalB $ VarE 'id) []]

genErrPatterns :: ClassInfo Class -> ClassInfo GADT -> ClassInfo GetClass
  -> REQ [Dec]
genErrPatterns
  (ClassInfo (C  _ccxt)  (C  ccnm) (C  cctv) (C ccetv) (C ccfd) ccfns (C ccinst))
  (ClassInfo (G  _gcxt) (G   gnm) (G  _gtv) (G  _getv) (G  _gfd) gfns (G  ginst))
  (ClassInfo (GC _gccxt) (GC  cnm) (GC  ctv) (GC (ftv,atv)) (GC fname) cfns (GC cinst))
    = undefined

      -- Pattern for the general Type ...
      -- patterns for the nduvidual constructors.

-- repType :: forall d. (Eq d , Data d) => d -> d -> (forall b. Data b => b -> b)
-- repType a b = \ c -> case testEquality (typeOf a) (typeOf c) of
--                        Just Refl -> if c == a then b else c
--                        Nothing -> c

-- repTypeMap :: forall d. (Ord d , Data d) => Map d d -> (forall b. Data b => b -> b)
-- repTypeMap m = \ c -> case testEquality (typeRep @d) (typeOf c) of
--                        Just Refl -> fromMaybe c (Map.lookup c m)
                       -- Nothing -> c

{-

genErrPatterns :: (HasL '[GADT,GetClass] l)
  => ClassInfo' l -> REQ (ClassInfo' (Pattern ': l), [Dec])
genErrPatterns = undefined

genThrowFuncs ::  (HasL '[Class] l) => ClassInfo' l -> REQ [Dec]
genThrowFuncs = undefined

-}
