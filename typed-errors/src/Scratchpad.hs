{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Scratchpad where

import Intro hiding (Type)
import Language.Haskell.TH
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH
import Data.Either.Validation

type family FromList (l :: [k]) :: TypeSet k where
  FromList '[] = 'Empty
  FromList (a ': as) = Insert a (FromList as)

data ErrorRules = ErrorRules {
  } deriving (Eq, Ord, Show)

data ErrorClass = ErrorClass {
    _ctxt :: Cxt
  , _name :: Name
  , _fixedTyVars :: [TyVarBndr]
  , _errorTyVar  :: TyVarBndr
  , _funDeps :: [FunDep]
  , _decs :: [ErrorFunc]
  } deriving (Eq, Ord, Show)

data ErrorFunc = ErrorFunc {
    _name :: Name
  , _tyVars :: [TyVarBndr]
  , _ctxt :: Cxt
  , _params :: [Type]
  } deriving (Eq, Ord, Show)

makeFields ''ErrorRules
makeFields ''ErrorClass
makeFields ''ErrorFunc

class TypedErrErr e where
  notProvidedClass  :: Either Info Dec -> e
  missingErrorTyVar :: e
  invalidFundep     :: Name -> FunDep -> e
  notFunctionSig    :: Dec -> e
  invalidFuncType   :: Type -> e
  invalidFinalParam :: Name -> Type -> e
  functionWithNoParams :: e
  withinClass       :: Name -> e -> e
  withinSig         :: Name -> e -> e

data TypedErrErrT where
  NotProvidedClass    :: Either Info Dec -> TypedErrErrT
  MissingErrorTyVar   :: TypedErrErrT
  InvalidFundep       :: Name -> FunDep -> TypedErrErrT
  NotFunctionSig      :: Dec -> TypedErrErrT
  InvalidFinalParam   :: Name -> Type -> TypedErrErrT
  InvalidFuncType     :: Type -> TypedErrErrT
  FunctionWithNoParams :: TypedErrErrT
  WithinClass         :: Name -> TypedErrErrT -> TypedErrErrT
  WithinSig           :: Name -> TypedErrErrT -> TypedErrErrT
  Many                :: [TypedErrErrT] -> TypedErrErrT
  deriving (Eq, Ord, Show)

instance TypedErrErr TypedErrErrT where
  notProvidedClass  = NotProvidedClass
  missingErrorTyVar = MissingErrorTyVar
  invalidFundep     = InvalidFundep
  notFunctionSig    = NotFunctionSig
  invalidFinalParam = InvalidFinalParam
  invalidFuncType   = InvalidFuncType
  functionWithNoParams = FunctionWithNoParams
  withinClass       = WithinClass
  withinSig         = WithinSig

instance Semigroup TypedErrErrT where
  (Many es) <> (Many es') = Many $ es <> es'
  (Many es) <> a          = Many $ es <> [a]
  a         <> (Many es ) = Many $ a : es
  a         <> b          = Many [a,b]

instance Monoid TypedErrErrT where
  mempty = Many []

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
