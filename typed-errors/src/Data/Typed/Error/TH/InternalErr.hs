{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module Data.Typed.Error.TH.InternalErr where

import Intro hiding (Type)
import Language.Haskell.TH
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.Typed.Error
import Data.Constraint
-- import Lens.Micro
-- import Lens.Micro.Mtl
-- import Lens.Micro.TH

class CC

class FC

type ClassConstraints = (CC :: Constraint)
type FuncConstraints = (FC :: Constraint)

-- | Internal Error Type used when generating errors.
--   Also kinda a showcase of what a manual instance should look like
class (ClassConstraints) => InternalErr e where
  nonClassInfo         :: (FuncConstraints) => Info -> e
  nonClassDec          :: Dec -> e
  missingErrorTyVar    :: e
  invalidFundep        :: Name -> FunDep -> e
  notFunctionSig       :: Dec -> e
  invalidFuncType      :: Type -> e
  invalidFinalParam    :: Name -> Type -> e
  functionWithNoParams :: e
  withinClass          :: Name -> e -> e
  withinFunction       :: Name -> e -> e

-- * Associated GADT

data InternalErrT e where
  NonClassInfoT         :: (ClassConstraints, FuncConstraints) => Info -> InternalErrT e
  NonClassDecT          :: (ClassConstraints) => Dec -> InternalErrT e
  MissingErrorTyVarT    :: (ClassConstraints) => InternalErrT e
  InvalidFundepT        :: (ClassConstraints) => Name -> FunDep -> InternalErrT e
  NotFunctionSigT       :: (ClassConstraints) => Dec -> InternalErrT e
  InvalidFuncTypeT      :: (ClassConstraints) => Type -> InternalErrT e
  InvalidFinalParamT    :: (ClassConstraints) => Name -> Type -> InternalErrT e
  FunctionWithNoParamsT :: (ClassConstraints) => InternalErrT e
  WithinClassT          :: (ClassConstraints) => Name -> e -> InternalErrT e
  WithinFunctionT       :: (ClassConstraints) => Name -> e -> InternalErrT e

type instance ErrorType InternalErr = InternalErrT

-- * Instance for packing InternalErrors into TypedErrors

instance (ClassConstraints, HasError InternalErr p) => InternalErr (TypedErrorV p) where
  nonClassInfo         a   = toError $ NonClassInfoT      a
  nonClassDec          a   = toError $ NonClassDecT       a
  missingErrorTyVar        = toError $ MissingErrorTyVarT
  invalidFundep        a b = toError $ InvalidFundepT     a b
  notFunctionSig       a   = toError $ NotFunctionSigT    a
  invalidFuncType      a   = toError $ InvalidFuncTypeT   a
  invalidFinalParam    a b = toError $ InvalidFinalParamT a b
  functionWithNoParams     = toError $ FunctionWithNoParamsT
  withinClass          a b = toError $ WithinClassT       a b
  withinFunction       a b = toError $ WithinFunctionT    a b

-- * Instance to allow conversion of typed error to other form

instance (InternalErr e) => RewriteError e InternalErrT where
  rewriteError (NonClassInfoT         a  ) = nonClassInfo a
  rewriteError (NonClassDecT          a  ) = nonClassDec a
  rewriteError (MissingErrorTyVarT       ) = missingErrorTyVar
  rewriteError (InvalidFundepT        a b) = invalidFundep a b
  rewriteError (NotFunctionSigT       a  ) = notFunctionSig a
  rewriteError (InvalidFuncTypeT      a  ) = invalidFuncType a
  rewriteError (InvalidFinalParamT    a b) = invalidFinalParam a b
  rewriteError (FunctionWithNoParamsT    ) = functionWithNoParams
  rewriteError (WithinClassT          a b) = withinClass a b
  rewriteError (WithinFunctionT       a b) = withinFunction a b

-- * Pattern Synonym Supporting Class and Instances

class (ClassConstraints, InternalErr i, InternalErr e) => GetInternalErr e i | e -> i where

  liftInternalErr :: e -> i

  fromNonClassInfo         :: e -> Maybe (Dict (ClassConstraints, FuncConstraints), Info)
  fromNonClassDec          :: e -> Maybe (Dict (ClassConstraints), Dec)
  fromMissingErrorTyVar    :: e -> Maybe (Dict (ClassConstraints), ())
  fromInvalidFundep        :: e -> Maybe (Dict (ClassConstraints), (Name, FunDep))
  fromNotFunctionSig       :: e -> Maybe (Dict (ClassConstraints), Dec)
  fromInvalidFuncType      :: e -> Maybe (Dict (ClassConstraints), Type)
  fromInvalidFinalParam    :: e -> Maybe (Dict (ClassConstraints), (Name, Type))
  fromFunctionWithNoParams :: e -> Maybe (Dict (ClassConstraints), ())
  fromWithinClass          :: e -> Maybe (Dict (ClassConstraints), (Name, i))
  fromWithinFunction       :: e -> Maybe (Dict (ClassConstraints), (Name, i))

instance (ClassConstraints
         , InternalErr e
         , InternalErr (InternalErrT e)
         , RewriteError i InternalErrT) => GetInternalErr (InternalErrT e) e where

  liftInternalErr = rewriteError

  fromNonClassInfo         :: InternalErrT e -> Maybe (Dict (ClassConstraints, FuncConstraints), Info)
  fromNonClassInfo         (NonClassInfoT a) = Just (Dict,a)
  fromNonClassInfo         _ = Nothing

  fromNonClassDec          :: InternalErrT e -> Maybe (Dict (ClassConstraints), Dec)
  fromNonClassDec          (NonClassDecT a) = Just (Dict,a)
  fromNonClassDec          _ = Nothing

  fromFunctionWithNoParams :: InternalErrT e -> Maybe (Dict (ClassConstraints), ())
  fromFunctionWithNoParams (FunctionWithNoParamsT) = Just (Dict,())
  fromFunctionWithNoParams _ = Nothing

  fromMissingErrorTyVar    :: InternalErrT e -> Maybe (Dict (ClassConstraints), ())
  fromMissingErrorTyVar    (MissingErrorTyVarT) = Just (Dict,())
  fromMissingErrorTyVar    _ = Nothing

  fromInvalidFundep        :: InternalErrT e -> Maybe (Dict (ClassConstraints), (Name, FunDep))
  fromInvalidFundep        (InvalidFundepT a b) = Just (Dict,(a,b))
  fromInvalidFundep        _ = Nothing

  fromNotFunctionSig       :: InternalErrT e -> Maybe (Dict (ClassConstraints), Dec)
  fromNotFunctionSig       (NotFunctionSigT a) = Just (Dict,a)
  fromNotFunctionSig       _ = Nothing

  fromInvalidFuncType      :: InternalErrT e -> Maybe (Dict (ClassConstraints), Type)
  fromInvalidFuncType      (InvalidFuncTypeT a) = Just (Dict,a)
  fromInvalidFuncType      _ = Nothing

  fromInvalidFinalParam    :: InternalErrT e -> Maybe (Dict (ClassConstraints), (Name, Type))
  fromInvalidFinalParam    (InvalidFinalParamT a b) = Just (Dict,(a,b))
  fromInvalidFinalParam    _ = Nothing

  fromWithinClass          :: InternalErrT e -> Maybe (Dict (ClassConstraints), (Name, e))
  fromWithinClass          (WithinClassT a b) = Just (Dict,(a,b))
  fromWithinClass          _ = Nothing

  fromWithinFunction       :: InternalErrT e -> Maybe (Dict (ClassConstraints), (Name, e))
  fromWithinFunction       (WithinFunctionT a b) = Just (Dict,(a,b))
  fromWithinFunction       _ = Nothing

instance ( ClassConstraints
         , InternalErr (TypedErrorV p)
         , HasError InternalErrT p
         ) => GetInternalErr (TypedErrorV p) (TypedErrorV p) where

  liftInternalErr = id

  fromNonClassInfo         :: TypedErrorV p -> Maybe (Dict (ClassConstraints, FuncConstraints), Info)
  fromNonClassInfo         (fromError @InternalErrT -> Just (NonClassInfoT a)) = Just (Dict,a)
  fromNonClassInfo         _ = Nothing

  fromNonClassDec          :: TypedErrorV p -> Maybe (Dict (ClassConstraints), Dec)
  fromNonClassDec          (fromError @InternalErrT -> Just (NonClassDecT a)) = Just (Dict,a)
  fromNonClassDec          _ = Nothing

  fromFunctionWithNoParams :: TypedErrorV p -> Maybe (Dict (ClassConstraints), ())
  fromFunctionWithNoParams (fromError @InternalErrT -> Just (FunctionWithNoParamsT)) = Just (Dict,())
  fromFunctionWithNoParams _ = Nothing

  fromMissingErrorTyVar    :: TypedErrorV p -> Maybe (Dict (ClassConstraints), ())
  fromMissingErrorTyVar    (fromError @InternalErrT -> Just(MissingErrorTyVarT)) = Just (Dict,())
  fromMissingErrorTyVar    _ = Nothing

  fromInvalidFundep        :: TypedErrorV p -> Maybe (Dict (ClassConstraints), (Name, FunDep))
  fromInvalidFundep        (fromError @InternalErrT -> Just(InvalidFundepT a b)) = Just (Dict,(a,b))
  fromInvalidFundep        _ = Nothing

  fromNotFunctionSig       :: TypedErrorV p -> Maybe (Dict (ClassConstraints), Dec)
  fromNotFunctionSig       (fromError @InternalErrT -> Just(NotFunctionSigT a)) = Just (Dict,a)
  fromNotFunctionSig       _ = Nothing

  fromInvalidFuncType      :: TypedErrorV p -> Maybe (Dict (ClassConstraints), Type)
  fromInvalidFuncType      (fromError @InternalErrT -> Just(InvalidFuncTypeT a)) = Just (Dict,a)
  fromInvalidFuncType      _ = Nothing

  fromInvalidFinalParam    :: TypedErrorV p -> Maybe (Dict (ClassConstraints), (Name, Type))
  fromInvalidFinalParam    (fromError @InternalErrT -> Just(InvalidFinalParamT a b)) = Just (Dict,(a,b))
  fromInvalidFinalParam    _ = Nothing

  fromWithinClass          :: TypedErrorV p -> Maybe (Dict (ClassConstraints), (Name, TypedErrorV p))
  fromWithinClass          (fromError @InternalErrT -> Just(WithinClassT a b)) = Just (Dict,(a,b))
  fromWithinClass          _ = Nothing

  fromWithinFunction       :: TypedErrorV p -> Maybe (Dict (ClassConstraints), (Name, TypedErrorV p))
  fromWithinFunction       (fromError @InternalErrT -> Just (WithinFunctionT a b)) = Just (Dict,(a,b))
  fromWithinFunction       _ = Nothing

-- * Pattern Synonyms

pattern InternalErr :: (ClassConstraints, HasError InternalErrT p)
                    => (ClassConstraints)
                    => InternalErrT (TypedErrorV p) -> TypedErrorV p
pattern InternalErr x <- (fromError @InternalErrT -> Just x)
  where
    InternalErr x = toError x

pattern NonClassInfo :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints, FuncConstraints)
                    => Info -> e
pattern NonClassInfo x <- (fromNonClassInfo @e @i -> Just (Dict, x))
  where
    NonClassInfo x = nonClassInfo @e x

pattern NonClassDec :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => Dec -> e
pattern NonClassDec x <- (fromNonClassDec @e @i -> Just (Dict, x))
  where
    NonClassDec x = nonClassDec @e x

pattern MissingErrorTyVar :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => e
pattern MissingErrorTyVar <- (fromMissingErrorTyVar @e @i -> Just (Dict, ()))
  where
    MissingErrorTyVar = missingErrorTyVar @e

pattern InvalidFundep :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => Name -> FunDep -> e
pattern InvalidFundep a b <- (fromInvalidFundep @e @i -> Just (Dict, (a,b)))
  where
    InvalidFundep a b = invalidFundep @e a b

pattern NoFunctionSig :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => Dec -> e
pattern NoFunctionSig x <- (fromNotFunctionSig @e @i -> Just (Dict, x))
  where
    NoFunctionSig x = NoFunctionSig @e x

pattern InvalidFuncType :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => Type -> e
pattern InvalidFuncType a <- (fromInvalidFuncType @e @i -> Just (Dict, a))
  where
    InvalidFuncType a = invalidFuncType @e a

pattern InvalidFinalParam :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => Name -> Type -> e
pattern InvalidFinalParam a  b<- (fromInvalidFinalParam @e @i -> Just (Dict, (a,b)))
  where
    InvalidFinalParam a = invalidFinalParam @e a

pattern FunctionWithNoParams :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (ClassConstraints)
                    => e
pattern FunctionWithNoParams <- (fromFunctionWithNoParams @e @i -> Just (Dict, ()))
  where
    FunctionWithNoParams = functionWithNoParams @e

pattern WithinClass :: forall e i. ( InternalErr i
                                  , InternalErr e
                                  , GetInternalErr e i
                                  , GetInternalErr i e)
                    => (ClassConstraints)
                    => Name -> i -> e
pattern WithinClass a b <- (fromWithinClass @e @i -> Just (Dict, (a,b)))
  where
    WithinClass a b = withinClass @e a (liftInternalErr b)

pattern WithinFunction :: forall e i. ( InternalErr i
                                     , InternalErr e
                                     , GetInternalErr e i
                                     , GetInternalErr i e)
                    => (ClassConstraints)
                    => Name -> i -> e
pattern WithinFunction a b <- (fromWithinFunction @e @i -> Just (Dict, (a,b)))
  where
    WithinFunction a b = withinFunction @e a (liftInternalErr b)

foo :: (HasError InternalErr p)  => TypedErrorV p
foo = WithinClass _ MissingErrorTyVar
