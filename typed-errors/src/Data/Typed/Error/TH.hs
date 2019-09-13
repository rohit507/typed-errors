{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Data.Typed.Error.TH where

import Intro hiding (Type)
import Language.Haskell.TH
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.Typed.Error.Internal
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error.TH.Types
import Data.Typed.Error.MonoidalErr
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Type.Reflection


genClassInfo :: Info -> REQ (ClassInfo Class)
genClassInfo (ClassI d i) = case d of
  ClassD _ name [] _ _ -> whileWithinClass name $ throwMissingErrorTyVar
  ClassD cxt name tyVars funDeps dec
    -> whileWithinClass name $ do
      (cTyVs, eTyV) <- splitTyVars tyVars
      ClassInfo
        <$> (pure $ C cxt)
        <*> (pure $ C name)
        <*> (pure $ C cTyVs)
        <*> (pure $ C eTyV)
        <*> (pure $ C funDeps)
        <*> (Map.fromList <$> traverse (genFuncInfo tyVars cxt) dec)
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
      = let (a,b,ps) = extrFromTyp t c typ in
          pure . (nm,) $
            FuncInfo
              (C $ fromMaybe [] a)
              (C nm)
              (C $ fromMaybe mempty b)
              (map C ps :: [Class 'Param])
    genFuncInfo _ _ n = throwInvalidClassDec n

    extrFromTyp :: C 'TyVars -> C 'Ctxt -> Type
        -> (Maybe (C 'Ctxt), Maybe (C 'TyVars), [C 'Param])
    extrFromTyp ctv ccxt (ForallT ftv fcxt typ)
      | ftv == ctv && ccxt == fcxt = extrFromTyp ctv ccxt typ
      | otherwise = extrFromTyp ftv fcxt typ
    extrFromTyp ctv ccxt (AppT p t)
      = let (a,b,ps) = extrFromTyp ctv ccxt t in (a,b,p : ps)
    extrFromTyp _ _ t = (Nothing, Nothing, [t])

genClassInfo i = throwNonClassInfo i

nameToStr :: Name -> String
nameToStr = undefined

tyVarName :: TyVarBndr -> Name
tyVarName = undefined

appTypes :: Type -> [Type] -> Type
appTypes n v = foldr AppT n v

genGADTDecs :: ClassInfo Class -> REQ (ClassInfo GADT, [Dec])
genGADTDecs (ClassInfo (C ctxt) (C nm) (C tv) (C etv) (C fd) fn (C inst))
  = whileBuildingGADT nm $ do
      (ci,gName,gDec) <- genGADTDef

      etDec <- errorTypeInst gName
      pure (ci,[gDec,etDec])

  where

    errorTypeInst :: Name -> REQ Dec
    errorTypeInst gnm = do
      vars <- traverse (map VarT . liftQ . newName . nameBase . tyVarName) tv
      pure . TySynInstD ''ErrorType . TySynEqn vars $ appTypes (ConT gnm) vars

    genGADTDef :: REQ (ClassInfo GADT, Name, Dec)
    genGADTDef = do
      gName <- (nameGADT <$> ask) <*> pure (nameToStr nm) >>= \case
        Nothing -> throwInvalidClassNameForGADT nm
        Just a  -> pure $ mkName a
      cons <- traverse genGADTConst fn

      let dec = DataD mempty
          ci = undefined
      pure (ci,gName, dec)

    genGADTConst :: FuncInfo Class -> REQ (FuncInfo GADT, Con)
    genGADTConst (FuncInfo (C fCxt) (C fn) (C fty) p) = do
     (nameGADTCons <$> ask) <$> (pure $ nameBase nm) <*> (pure $ nameBase fn) >>= \case
        Nothing -> throwInvalidFuncNameForGADT nm fn
        Just a  -> pure $ mkName

genTErrClassInst :: (HasL '[Class,GADT] l) => ClassInfo' l -> REQ Dec
genTErrClassInst = undefined

  where

    genMemberFunc :: Dec
    genMemberFunc = undefined

genGADTRewriteInst :: (HasL '[Class,GADT] l) => ClassInfo' l -> REQ Dec
genGADTRewriteInst = undefined

  where

    genRewriteClause :: FuncInfo' l -> REQ Clause
    genRewriteClause = undefined

genGetClass :: (HasL '[Class] l) => ClassInfo' l -> REQ (ClassInfo' (GetClass ': l), Dec)
genGetClass = undefined

genGADTGetInst :: (HasL '[GADT, GetClass] l ) => ClassInfo' l -> REQ Dec
genGADTGetInst = undefined

genTErrGetInst :: (HasL '[GetClass] l) => ClassInfo' l -> REQ Dec
genTErrGetInst = undefined

genErrPatterns :: (HasL '[GADT,GetClass] l)
  => ClassInfo' l -> REQ (ClassInfo' (Pattern ': l), [Dec])
genErrPatterns = undefined

genThrowFuncs ::  (HasL '[Class] l) => ClassInfo' l -> REQ [Dec]
genThrowFuncs = undefined



{-
convertClassInfo :: forall e. (TypedErrErr e
                             ) => Info -> Either e ErrorClass
convertClassInfo (ClassI d _) = convertClassDec d
convertClassInfo a = Left . notProvidedClass $ Left a

convertClassDec :: (TypedErrErr e) => Dec -> Either e ErrorClass
convertClassDec (ClassD ctxt name tyVars funDeps decs)
  = first (withinClass name) $ do
      (fTyVars, eTyVar) <- case (,) <$> initMay tyVars <*> lastMay tyVars of
        Nothing -> Left missingErrorTyVar
        Just  r -> pure r
      let ename = getTyVarName eTyVar
      traverse_ (validateFunDep ename) funDeps
      decs' <- traverse (convertSig ename) decs
      pure $ ErrorClass ctxt name fTyVars eTyVar funDeps decs'
convertClassDec d = Left . notProvidedClass $ Right d


validateFunDep :: (TypedErrErr e) => Name -> FunDep -> Either e ()
validateFunDep etv fd@(FunDep is ds)
  = case elem etv is || elem etv ds of
     False -> skip
     True -> Left $ invalidFundep etv fd

convertSig :: (TypedErrErr e) => Name -> Dec -> Either e ErrorFunc
convertSig etv (SigD name typ)
  = first (withinSig name) $ convertType etv name typ
convertSig _ s = Left $ notFunctionSig s

convertType :: (TypedErrErr e) => Name -> Name -> Type -> Either e ErrorFunc
convertType etv name (ForallT _ _ typ@ForallT{})
   -- Method sigs in classes can be wrapped in two layers of 'ForAllT.'
   -- We elide the layer that corresponds to class constraints, since that
   -- information is stored in `ErrorClass`.
  = convertType etv name typ
convertType etv name (ForallT tyVars ctxt typ)
  = do let params = convertParams typ
       case lastMay params of
         Nothing -> Left $ functionWithNoParams
         Just (VarT e) -> case e == etv of
           True -> skip
           False -> Left $ invalidFinalParam etv (VarT e)
         Just a -> Left $ invalidFinalParam etv a
       pure $ ErrorFunc name tyVars ctxt params
convertType _ _ a = Left $ invalidFuncType a

convertParams :: Type -> [Type]
convertParams (AppT (AppT ArrowT a) b) = a : convertParams b
convertParams a = [a]

getTyVarName :: TyVarBndr -> Name
getTyVarName (PlainTV a) = a
getTyVarName (KindedTV a _) = a

deriveErrorTypes :: Name -> Q [Dec]
deriveErrorTypes n = do
  classData <- reify n
  reportWarning . show @(Either TypedErrErrT ErrorClass)
    $ convertClassInfo classData
  pure []



-- TODO ::
--   - Write code for error class.
--   - Generate the functor version of the error type
--     - Generate the instance for that error type
--     - Generate the instance for when the functor is a member of Error\
--     - Generate Eq1, Ord1, Show1, Eq, Ord, Show, Generic, NFData, NFData1
--       Functor, Foldable, Traversable and Typeable instances for each type.
--   - Generate the pattern synonyms
--   - Generate the throw/while functions for the class.
-}
