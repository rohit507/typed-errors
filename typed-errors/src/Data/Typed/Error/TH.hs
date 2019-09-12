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

{-
data TyVars
data ErrTyVar
data FunDeps
data ClsFunc (bst :: TypeSet (* -> *))


data ClassInfo bst = ClassInfo {
    tyVars :: Anns bst TyVars
  , errTyVar :: Anns bst ErrTyVar
  , funDeps :: Anns bst FunDeps
  , clsFuncs :: Map Name (Anns bst ClsFunc)
  }



genClassInfo :: Info -> REQ (ClassInfo )
genClassInfo = undefined

genGADTDecs :: ClassInfo a -> REQ (ClassInfo (GADT ': a), [Dec])
genGADTDecs = undefined

  where

    genErrorTypeInst :: Dec
    genErrorTypeInst = undefined

    genGADTDef :: Dec
    genGADTDef = undefined

    genGADTConst :: Dec
    genGADTConst = undefined

genTErrClassInst :: (Has GADT e) => ClassInfo e -> REQ Dec
genTErrClassInst = undefined

  where

    genMemberFunc :: Dec
    genMemberFunc = undefined

genGADTRewriteInst :: Has GADT e => ClassInfo e -> Req Dec
genGADTRewriteInst = undefined

  where

    genRewriteClause :: Has GADT e => ConstInfo e -> REQ Clause
    genRewriteClause = undefined

genGetClass :: ClassInfo e -> REQ (ClassInfo (Insert GetClass e), Dec)
genGetClass = undefined

genGADTGetInst :: (Has GADT e, Has GetClass e) => ClassInfo e -> REQ Dec
genGADTGetInst = undefined

genTErrGetInst :: (Has GetClass e) => ClassInfo e -> Req Dec
genTErrGetInst = undefined

genErrPatterns :: (Has GADT e, Has GetClass e) => ClassInfo e -> REq  [Dec]
genErrPatterns = undefined

genThrowFuncs :: ClassInfo e -> REQ [Dec]
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
-}
