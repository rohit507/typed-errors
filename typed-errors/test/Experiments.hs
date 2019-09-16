{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Intro hiding (Type)
import Data.Typed.Error
import Language.Haskell.TH
import Type.Reflection

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
  missingFuncInfo      :: Name -> SomeTypeRep -> e
  extraFuncInfo        :: Name -> SomeTypeRep -> e
  withinClass          :: Name -> e -> e
  withinFunction       :: Name -> e -> e

class (Ord a, Monoid b) => CrazyErr a b c e where
  err1 :: (Show a, Eq b) => (a,b) -> [c a] -> e -> e
  err2 :: forall d. (Ord d) => a -> b -> c d -> e
  err3 :: forall m. (InternalErr e) => (c m -> Maybe m) -> c b -> c a -> e -> e

class ConversionErr i a e where
  invalidMsgOp     :: (Show msgOp ) => Text -> msgOp -> e
  invalidTermOp    :: (Show termOp) => Text -> termOp -> e
  invalidParamInit :: (Show pInit ) => Text -> pInit -> e

-- makeErrClassHelpers defaultTypedErrorRules ''CrazyErr
makeErrClassHelpers defaultTypedErrorRules ''ConversionErr
-- makeErrClassHelpers defaultTypedErrorRules ''InternalErr

main :: IO ()
main = print "It compiled!"
