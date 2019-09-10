{-# LANGUAGE UndecidableInstances #-}


module Data.Typed.Error.TH.InternalErr where

import Intro hiding (Type)
import Language.Haskell.TH
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.Typed.Error
-- import Lens.Micro
-- import Lens.Micro.Mtl
-- import Lens.Micro.TH


-- | Internal Error Type used when generating errors.
--   Also kinda a showcase of what a manual instance should look like
class InternalErr e where
  nonClassInfo         :: Info -> e
  nonClassDec          :: Dec -> e
  missingErrorTyVar    :: e
  invalidFundep        :: Name -> FunDep -> e
  notFunctionSig       :: Dec -> e
  invalidFuncType      :: Type -> e
  invalidFinalParam    :: Name -> Type -> e
  functionWithNoParams :: e
  withinClass          :: Name -> e -> e
  withinFunction       :: Name -> e -> e

data InternalErrT e where
  NonClassInfoT         :: Info -> InternalErrT e
  NonClassDecT          :: Dec -> InternalErrT e
  MissingErrorTyVarT    :: InternalErrT e
  InvalidFundepT        :: Name -> FunDep -> InternalErrT e
  NotFunctionSigT       :: Dec -> InternalErrT e
  InvalidFuncTypeT      :: Type -> InternalErrT e
  InvalidFinalParamT    :: Name -> Type -> InternalErrT e
  FunctionWithNoParamsT :: InternalErrT e
  WithinClassT          :: Name -> e -> InternalErrT e
  WithinFunctionT       :: Name -> e -> InternalErrT e

instance (HasError InternalErrT p) => InternalErr (TypedErrorV p) where
  nonClassInfo         a   = toError $ NonClassInfoT a
  nonClassDec          a   = toError $ NonClassDecT a
  missingErrorTyVar        = toError $ MissingErrorTyVarT
  invalidFundep        a b = toError $ InvalidFundepT a b
  notFunctionSig       a   = toError $ NotFunctionSigT a
  invalidFuncType      a   = toError $ InvalidFuncTypeT a
  invalidFinalParam    a b = toError $ InvalidFinalParamT a b
  functionWithNoParams     = toError $ FunctionWithNoParamsT
  withinClass          a b = toError $ WithinClassT a b
  withinFunction       a b = toError $ WithinFunctionT a b

instance (InternalErr e) => RewriteError e (InternalErrT (TypedErrorV p)) where
  rewriteErr (NonClassInfoT         a  ) = nonClassInfo a
  rewriteErr (NonClassDecT          a  ) = nonClassDec a
  rewriteErr (MissingErrorTyVarT       ) = missingErrorTyVar
  rewriteErr (InvalidFundepT        a b) = invalidFundep a b
  rewriteErr (NotFunctionSigT       a  ) = notFunctionSig a
  rewriteErr (InvalidFuncTypeT      a  ) = invalidFuncType a
  rewriteErr (InvalidFinalParamT    a b) = invalidFinalParam a b
  rewriteErr (FunctionWithNoParamsT    ) = functionWithNoParams
  rewriteErr (WithinClassT          a b) = withinClass a b
  rewriteErr (WithinFunctionT       a b) = withinFunction a b
