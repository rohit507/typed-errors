{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass  #-}

module Data.Typed.Error.TH.InternalErr where

import Language.Haskell.TH
import Data.Typed.Error.Internal
import Data.Constraint
import Data.Functor.Classes
import Prelude
import Type.Reflection
import Control.Monad.Error.Class
import Text.Show

-- | These nullary typeclasses allow us to check whether we're propagating
--   constraints correct in this module.
--
--   When we end up using InternalErr we'll just make some empty instances.
class CCIntE
class FCIntE

instance CCIntE
instance FCIntE


-- | Internal Error Type used when generating errors.
--   Also kinda a showcase of what a manual instance should look like
class (CCIntE) => InternalErr e where
  nonClassInfo         :: (FCIntE) => Info -> e
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
  -- paramMismatch :: ([Type], Maybe Type, [Type]) ->  ([Type], Maybe Type, [Type]) -> e

-- * Associated GADT

data InternalErrT e where
  NonClassInfoT         :: (CCIntE, FCIntE) => Info -> InternalErrT e
  NonClassDecT          :: (CCIntE) => Dec -> InternalErrT e
  MissingErrorTyVarT    :: (CCIntE) => InternalErrT e
  InvalidFundepT        :: (CCIntE) => Name -> FunDep -> InternalErrT e
  NotFunctionSigT       :: (CCIntE) => Dec -> InternalErrT e
  InvalidFuncTypeT      :: (CCIntE) => Type -> InternalErrT e
  InvalidFinalParamT    :: (CCIntE) => Name -> Type -> InternalErrT e
  FunctionWithNoParamsT :: (CCIntE) => InternalErrT e
  MissingFuncInfoT      :: (CCIntE) => Name -> SomeTypeRep -> InternalErrT e
  ExtraFuncInfoT        :: (CCIntE) => Name -> SomeTypeRep -> InternalErrT e
  WithinClassT          :: (CCIntE) => Name -> e -> InternalErrT e
  WithinFunctionT       :: (CCIntE) => Name -> e -> InternalErrT e

type instance ErrorType InternalErr = InternalErrT

-- * important instances

instance (Eq Info, Eq Dec, Eq Name, Eq Type) => Eq1 InternalErrT where
 liftEq _  (NonClassInfoT         a  ) (NonClassInfoT         a'   ) = a == a'
 liftEq _  (NonClassDecT          a  ) (NonClassDecT          a'   ) = a == a'
 liftEq _  (MissingErrorTyVarT       ) (MissingErrorTyVarT         ) = True
 liftEq _  (InvalidFundepT        a b) (InvalidFundepT        a' b') = a == a' && b == b'
 liftEq _  (NotFunctionSigT       a  ) (NotFunctionSigT       a'   ) = a == a'
 liftEq _  (InvalidFuncTypeT      a  ) (InvalidFuncTypeT      a'   ) = a == a'
 liftEq _  (InvalidFinalParamT    a b) (InvalidFinalParamT    a' b') = a == a' && b == b'
 liftEq _  (FunctionWithNoParamsT    ) (FunctionWithNoParamsT      ) = True
 liftEq _  (MissingFuncInfoT      a b) (MissingFuncInfoT      a' b') = a == a' && b == b'
 liftEq _  (ExtraFuncInfoT        a b) (ExtraFuncInfoT        a' b') = a == a' && b == b'
 liftEq eq (WithinClassT          a b) (WithinClassT          a' b') = a == a' && eq b b'
 liftEq eq (WithinFunctionT       a b) (WithinFunctionT       a' b') = a == a' && eq b b'
 liftEq _ _ _ = False

instance (Eq Info, Eq Dec, Eq Name, Eq Type, Eq e) => Eq (InternalErrT e) where
  (==) = eq1

instance (Ord Info, Ord Dec, Ord Name, Ord Type) => Ord1 InternalErrT where
  liftCompare cmp a b = (<>) (compare (constructorOrd a) (constructorOrd b)) $ case (a,b) of
    (NonClassInfoT         a  , NonClassInfoT         a'   ) -> compare a a'
    (NonClassDecT          a  , NonClassDecT          a'   ) -> compare a a'
    (MissingErrorTyVarT       , MissingErrorTyVarT         ) -> EQ
    (InvalidFundepT        a b, InvalidFundepT        a' b') -> compare a a' <> compare b b'
    (NotFunctionSigT       a  , NotFunctionSigT       a'   ) -> compare a a'
    (InvalidFuncTypeT      a  , InvalidFuncTypeT      a'   ) -> compare a a'
    (InvalidFinalParamT    a b, InvalidFinalParamT    a' b') -> compare a a' <> compare b b'
    (FunctionWithNoParamsT    , FunctionWithNoParamsT      ) -> EQ
    (MissingFuncInfoT      a b, MissingFuncInfoT      a' b') -> compare a a' <> compare b b'
    (ExtraFuncInfoT        a b, ExtraFuncInfoT        a' b') -> compare a a' <> compare b b'
    (WithinClassT          a b, WithinClassT          a' b') -> compare a a' <> cmp b b'
    (WithinFunctionT       a b, WithinFunctionT       a' b') -> compare a a' <> cmp b b'
    _ -> error "unreachable"

    where

      constructorOrd :: InternalErrT e -> Int
      constructorOrd (NonClassInfoT         _  ) = 0
      constructorOrd (NonClassDecT          _  ) = 1
      constructorOrd (MissingErrorTyVarT       ) = 2
      constructorOrd (InvalidFundepT        _ _) = 3
      constructorOrd (NotFunctionSigT       _  ) = 4
      constructorOrd (InvalidFuncTypeT      _  ) = 5
      constructorOrd (InvalidFinalParamT    _ _) = 6
      constructorOrd (FunctionWithNoParamsT    ) = 7
      constructorOrd (WithinClassT          _ _) = 8
      constructorOrd (WithinFunctionT       _ _) = 9
      constructorOrd (MissingFuncInfoT      _ _) = 10
      constructorOrd (ExtraFuncInfoT        _ _) = 11


instance (Ord Info, Ord Dec, Ord Name, Ord Type, Ord e) => Ord (InternalErrT e) where
  compare = compare1

-- Right, I don't want to have to handle fixity myself I'd rather just generate
-- the Show and Read instances
--
-- canonical instances for deriving these are in the deriving-compat package
--
instance (Show Info, Show Dec, Show Name, Show Type) => Show1 InternalErrT where
  liftShowsPrec sPrec sList p (NonClassInfoT         a  )
   = showParen (p > app_prec) $ showString "NonClassInfo " . showsPrec (app_prec + 1) a
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (NonClassDecT          a  )
   = showParen (p > app_prec) $ showString "NonClassDec " . showsPrec (app_prec + 1) a
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (MissingErrorTyVarT       )
   = showParen (p > app_prec) $ showString "MissErrTyVar"
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (InvalidFundepT        a b)
   = showParen (p > app_prec) $ showString "InvalFunDep "
       . showsPrec (app_prec + 1) a
       . showsPrec (app_prec + 1) b
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (NotFunctionSigT       a  )
   = showParen (p > app_prec) $ showString "NotFunc " . showsPrec (app_prec + 1) a
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (InvalidFuncTypeT      a  )
   = showParen (p > app_prec) $ showString "InvalFType " . showsPrec (app_prec + 1) a
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (InvalidFinalParamT    a b)
   = showParen (p > app_prec) $ showString "InvaFinPar "
       . showsPrec (app_prec + 1) a
       . showsPrec (app_prec + 1) b
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (FunctionWithNoParamsT    )
   = showParen (p > app_prec) $ showString "Fw/noparams"
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (WithinClassT          a b)
   = showParen (p > app_prec) $ showString "withinClass"
       . showsPrec (app_prec + 1) a
       . sPrec (app_prec + 1) b
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (WithinFunctionT a b)
   = showParen (p > app_prec) $ showString "WithinFunc "
       . showsPrec (app_prec + 1) a
       . sPrec (app_prec + 1) b
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (MissingFuncInfoT a b)
   = showParen (p > app_prec) $ showString "WithinFunc "
       . showsPrec (app_prec + 1) a
       . showsPrec (app_prec + 1) b
     where
       app_prec = 10

  liftShowsPrec sPrec sList p (ExtraFuncInfoT a b)
   = showParen (p > app_prec) $ showString "WithinFunc "
       . showsPrec (app_prec + 1) a
       . showsPrec (app_prec + 1) b
     where
       app_prec = 10

instance Functor InternalErrT where
 fmap _ (NonClassInfoT         a  ) = NonClassInfoT         a
 fmap _ (NonClassDecT          a  ) = NonClassDecT          a
 fmap _ (MissingErrorTyVarT       ) = MissingErrorTyVarT
 fmap _ (InvalidFundepT        a b) = InvalidFundepT        a b
 fmap _ (NotFunctionSigT       a  ) = NotFunctionSigT       a
 fmap _ (InvalidFuncTypeT      a  ) = InvalidFuncTypeT      a
 fmap _ (InvalidFinalParamT    a b) = InvalidFinalParamT    a b
 fmap _ (FunctionWithNoParamsT    ) = FunctionWithNoParamsT
 fmap _ (MissingFuncInfoT      a b) = MissingFuncInfoT      a b
 fmap _ (ExtraFuncInfoT        a b) = ExtraFuncInfoT        a b
 fmap i (WithinClassT          a b) = WithinClassT          a (i b)
 fmap i (WithinFunctionT       a b) = WithinFunctionT       a (i b)

instance Foldable InternalErrT where
 foldMap i (WithinClassT          _ b) = i b
 foldMap i (WithinFunctionT       _ b) = i b
 foldMap _ _ = mempty

instance Traversable InternalErrT where
 traverse i (WithinClassT          a b) = WithinClassT a <$> i b
 traverse i (WithinFunctionT       a b) = WithinFunctionT a <$> i b
 traverse _ a = pure $ fmap (error "unreachable") a


-- Show
-- Show1
-- NFData
-- NFData1
-- Hashable
-- Hashable1


-- * Instance for packing InternalErrors into TypedErrors

instance (CCIntE, HasError InternalErr p) => InternalErr (TypedError p) where
  nonClassInfo         a   = toError $ NonClassInfoT      a
  nonClassDec          a   = toError $ NonClassDecT       a
  missingErrorTyVar        = toError $ MissingErrorTyVarT
  invalidFundep        a b = toError $ InvalidFundepT     a b
  notFunctionSig       a   = toError $ NotFunctionSigT    a
  invalidFuncType      a   = toError $ InvalidFuncTypeT   a
  invalidFinalParam    a b = toError $ InvalidFinalParamT a b
  functionWithNoParams     = toError $ FunctionWithNoParamsT
  missingFuncInfo      a b = toError $ MissingFuncInfoT   a b
  extraFuncInfo        a b = toError $ ExtraFuncInfoT     a b
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
  rewriteError (MissingFuncInfoT      a b) = missingFuncInfo a b
  rewriteError (ExtraFuncInfoT        a b) = extraFuncInfo a b
  rewriteError (WithinClassT          a b) = withinClass a b
  rewriteError (WithinFunctionT       a b) = withinFunction a b

-- * Pattern Synonym Supporting Class and Instances

class (CCIntE, InternalErr i, InternalErr e) => GetInternalErr e i | e -> i where

  liftInternalErr :: e -> i

  fromNonClassInfo         :: e -> Maybe (Dict (CCIntE, FCIntE), Info)
  fromNonClassDec          :: e -> Maybe (Dict (CCIntE), Dec)
  fromMissingErrorTyVar    :: e -> Maybe (Dict (CCIntE), ())
  fromInvalidFundep        :: e -> Maybe (Dict (CCIntE), (Name, FunDep))
  fromNotFunctionSig       :: e -> Maybe (Dict (CCIntE), Dec)
  fromInvalidFuncType      :: e -> Maybe (Dict (CCIntE), Type)
  fromInvalidFinalParam    :: e -> Maybe (Dict (CCIntE), (Name, Type))
  fromFunctionWithNoParams :: e -> Maybe (Dict (CCIntE), ())
  fromWithinClass          :: e -> Maybe (Dict (CCIntE), (Name, i))
  fromWithinFunction       :: e -> Maybe (Dict (CCIntE), (Name, i))

instance ( CCIntE
         , InternalErr e
         , InternalErr (InternalErrT e)
         , RewriteError e InternalErrT) => GetInternalErr (InternalErrT e) e where

  liftInternalErr = rewriteError

  fromNonClassInfo         :: InternalErrT e -> Maybe (Dict (CCIntE, FCIntE), Info)
  fromNonClassInfo         (NonClassInfoT a) = Just (Dict,a)
  fromNonClassInfo         _ = Nothing

  fromNonClassDec          :: InternalErrT e -> Maybe (Dict (CCIntE), Dec)
  fromNonClassDec          (NonClassDecT a) = Just (Dict,a)
  fromNonClassDec          _ = Nothing

  fromFunctionWithNoParams :: InternalErrT e -> Maybe (Dict (CCIntE), ())
  fromFunctionWithNoParams (FunctionWithNoParamsT) = Just (Dict,())
  fromFunctionWithNoParams _ = Nothing

  fromMissingErrorTyVar    :: InternalErrT e -> Maybe (Dict (CCIntE), ())
  fromMissingErrorTyVar    (MissingErrorTyVarT) = Just (Dict,())
  fromMissingErrorTyVar    _ = Nothing

  fromInvalidFundep        :: InternalErrT e -> Maybe (Dict (CCIntE), (Name, FunDep))
  fromInvalidFundep        (InvalidFundepT a b) = Just (Dict,(a,b))
  fromInvalidFundep        _ = Nothing

  fromNotFunctionSig       :: InternalErrT e -> Maybe (Dict (CCIntE), Dec)
  fromNotFunctionSig       (NotFunctionSigT a) = Just (Dict,a)
  fromNotFunctionSig       _ = Nothing

  fromInvalidFuncType      :: InternalErrT e -> Maybe (Dict (CCIntE), Type)
  fromInvalidFuncType      (InvalidFuncTypeT a) = Just (Dict,a)
  fromInvalidFuncType      _ = Nothing

  fromInvalidFinalParam    :: InternalErrT e -> Maybe (Dict (CCIntE), (Name, Type))
  fromInvalidFinalParam    (InvalidFinalParamT a b) = Just (Dict,(a,b))
  fromInvalidFinalParam    _ = Nothing

  fromWithinClass          :: InternalErrT e -> Maybe (Dict (CCIntE), (Name, e))
  fromWithinClass          (WithinClassT a b) = Just (Dict,(a,b))
  fromWithinClass          _ = Nothing

  fromWithinFunction       :: InternalErrT e -> Maybe (Dict (CCIntE), (Name, e))
  fromWithinFunction       (WithinFunctionT a b) = Just (Dict,(a,b))
  fromWithinFunction       _ = Nothing

instance ( CCIntE
         , InternalErr (TypedError p)
         , HasError InternalErr p
         ) => GetInternalErr (TypedError p) (TypedError p) where

  liftInternalErr = id

  fromNonClassInfo         :: TypedError p -> Maybe (Dict (CCIntE, FCIntE), Info)
  fromNonClassInfo         (fromError @InternalErr -> Just (NonClassInfoT a)) = Just (Dict,a)
  fromNonClassInfo         _ = Nothing

  fromNonClassDec          :: TypedError p -> Maybe (Dict (CCIntE), Dec)
  fromNonClassDec          (fromError @InternalErr -> Just (NonClassDecT a)) = Just (Dict,a)
  fromNonClassDec          _ = Nothing

  fromFunctionWithNoParams :: TypedError p -> Maybe (Dict (CCIntE), ())
  fromFunctionWithNoParams (fromError @InternalErr -> Just (FunctionWithNoParamsT)) = Just (Dict,())
  fromFunctionWithNoParams _ = Nothing

  fromMissingErrorTyVar    :: TypedError p -> Maybe (Dict (CCIntE), ())
  fromMissingErrorTyVar    (fromError @InternalErr -> Just(MissingErrorTyVarT)) = Just (Dict,())
  fromMissingErrorTyVar    _ = Nothing

  fromInvalidFundep        :: TypedError p -> Maybe (Dict (CCIntE), (Name, FunDep))
  fromInvalidFundep        (fromError @InternalErr -> Just(InvalidFundepT a b)) = Just (Dict,(a,b))
  fromInvalidFundep        _ = Nothing

  fromNotFunctionSig       :: TypedError p -> Maybe (Dict (CCIntE), Dec)
  fromNotFunctionSig       (fromError @InternalErr -> Just(NotFunctionSigT a)) = Just (Dict,a)
  fromNotFunctionSig       _ = Nothing

  fromInvalidFuncType      :: TypedError p -> Maybe (Dict (CCIntE), Type)
  fromInvalidFuncType      (fromError @InternalErr -> Just(InvalidFuncTypeT a)) = Just (Dict,a)
  fromInvalidFuncType      _ = Nothing

  fromInvalidFinalParam    :: TypedError p -> Maybe (Dict (CCIntE), (Name, Type))
  fromInvalidFinalParam    (fromError @InternalErr -> Just(InvalidFinalParamT a b)) = Just (Dict,(a,b))
  fromInvalidFinalParam    _ = Nothing

  fromWithinClass          :: TypedError p -> Maybe (Dict (CCIntE), (Name, TypedError p))
  fromWithinClass          (fromError @InternalErr -> Just(WithinClassT a b)) = Just (Dict,(a,b))
  fromWithinClass          _ = Nothing

  fromWithinFunction       :: TypedError p -> Maybe (Dict (CCIntE), (Name, TypedError p))
  fromWithinFunction       (fromError @InternalErr -> Just (WithinFunctionT a b)) = Just (Dict,(a,b))
  fromWithinFunction       _ = Nothing

-- * Pattern Synonyms

pattern InternalErr :: (CCIntE, HasError InternalErr p)
                    => (CCIntE)
                    => InternalErrT (TypedError p) -> TypedError p
pattern InternalErr x <- (fromError @InternalErr -> Just x)
  where
    InternalErr x = toError x

pattern NonClassInfo :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE, FCIntE)
                    => Info -> e
pattern NonClassInfo x <- (fromNonClassInfo @e @i -> Just (Dict, x))
  where
    NonClassInfo x = nonClassInfo @e x

pattern NonClassDec :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => Dec -> e
pattern NonClassDec x <- (fromNonClassDec @e @i -> Just (Dict, x))
  where
    NonClassDec x = nonClassDec @e x

pattern MissingErrorTyVar :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => e
pattern MissingErrorTyVar <- (fromMissingErrorTyVar @e @i -> Just (Dict, ()))
  where
    MissingErrorTyVar = missingErrorTyVar @e

pattern InvalidFundep :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => Name -> FunDep -> e
pattern InvalidFundep a b <- (fromInvalidFundep @e @i -> Just (Dict, (a,b)))
  where
    InvalidFundep a b = invalidFundep @e a b

pattern NoFunctionSig :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => Dec -> e
pattern NoFunctionSig x <- (fromNotFunctionSig @e @i -> Just (Dict, x))
  where
    NoFunctionSig x = NoFunctionSig @e @i x

pattern InvalidFuncType :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => Type -> e
pattern InvalidFuncType a <- (fromInvalidFuncType @e @i -> Just (Dict, a))
  where
    InvalidFuncType a = invalidFuncType @e a

pattern InvalidFinalParam :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => Name -> Type -> e
pattern InvalidFinalParam a  b<- (fromInvalidFinalParam @e @i -> Just (Dict, (a,b)))
  where
    InvalidFinalParam a = invalidFinalParam @e a

pattern FunctionWithNoParams :: forall e i. (InternalErr e, GetInternalErr e i)
                    => (CCIntE)
                    => e
pattern FunctionWithNoParams <- (fromFunctionWithNoParams @e @i -> Just (Dict, ()))
  where
    FunctionWithNoParams = functionWithNoParams @e

pattern WithinClass :: forall e i. ( InternalErr i
                                   , InternalErr e
                                   , GetInternalErr e i
                                   , GetInternalErr i e)
                    => (CCIntE)
                    => Name -> i -> e
pattern WithinClass a b <- (fromWithinClass @e @i -> Just (Dict, (a,b)))
  where
    WithinClass a b = withinClass @e a (liftInternalErr b)

pattern WithinFunction :: forall e i. ( InternalErr i
                                     , InternalErr e
                                     , GetInternalErr e i
                                     , GetInternalErr i e)
                    => (CCIntE)
                    => Name -> i -> e
pattern WithinFunction a b <- (fromWithinFunction @e @i -> Just (Dict, (a,b)))
  where
    WithinFunction a b = withinFunction @e a (liftInternalErr b)

-- * Convenience Functions for working with MonadError instances

throwNonClassInfo :: ( FCIntE
                     , InternalErr e
                     , MonadError e m
                     ) => Info -> m a
throwNonClassInfo i = throwError $ nonClassInfo i

throwNonClassDec :: ( InternalErr e
                    , MonadError e m
                    ) => Dec -> m a
throwNonClassDec i = throwError $ nonClassDec i

throwMissingErrorTyVar :: ( InternalErr e
                          , MonadError e m
                          ) => m a
throwMissingErrorTyVar = throwError missingErrorTyVar


throwInvalidFundep ::  ( InternalErr e
                       , MonadError e m
                       ) => Name -> FunDep -> m a
throwInvalidFundep a b = throwError $ invalidFundep a b

throwNotFunctionSig :: ( InternalErr e
                       , MonadError e m
                       ) => Dec -> m a
throwNotFunctionSig a = throwError $ notFunctionSig a

throwInvalidFuncType :: ( InternalErr e
                        , MonadError e m
                        ) => Type -> m a
throwInvalidFuncType a = throwError $ invalidFuncType a

throwInvalidFinalParam :: (InternalErr e
                          , MonadError e m
                          ) => Name -> Type -> m a
throwInvalidFinalParam a b = throwError $ invalidFinalParam a b

throwFunctionWithNoParams :: ( InternalErr e
                             , MonadError e m
                             ) => m a
throwFunctionWithNoParams = throwError functionWithNoParams

throwMissingFuncInfo :: ( InternalErr e
                       , MonadError e m
                       ) => Name -> SomeTypeRep -> m a
throwMissingFuncInfo a b = throwError $ missingFuncInfo a b

throwExtraFuncInfo :: ( InternalErr e
                      , MonadError e m
                      ) => Name -> SomeTypeRep -> m a
throwExtraFuncInfo a b = throwError $ extraFuncInfo a b


whileWithinClass :: ( InternalErr e
                    , MonadError e m
                    ) => Name -> m a -> m a
whileWithinClass a m = catchError m (throwError . withinClass a)

whileWithinFunction :: ( InternalErr e
                      , MonadError e m
                      ) => Name -> m a -> m a
whileWithinFunction a m = catchError m (throwError . withinFunction a)

throwInvalidClassDec :: ( InternalErr e
        , MonadError e m
        ) => Dec -> m a
throwInvalidClassDec a = error . show $ ppr a  -- undefined -- throwError $ extraFuncInfo a b

throwInvalidClassNameForGADT :: ( InternalErr e
        , MonadError e m
        ) => Name -> m a
throwInvalidClassNameForGADT a = error . show $ ppr a -- throwError $ extraFuncInfo a b

throwInvalidClassNameForGetClass :: ( InternalErr e
        , MonadError e m
        ) => Name -> m a
throwInvalidClassNameForGetClass a = error . show $ ppr a -- throwError $ extraFuncInfo a b

throwInvalidFuncNameForGetClass :: ( InternalErr e
        , MonadError e m
        ) => Name -> Name -> m a
throwInvalidFuncNameForGetClass a b = error . show $ (ppr a, ppr b)-- throwError $ extraFuncInfo a b

throwInvalidFuncNameForGADT :: ( InternalErr e
        , MonadError e m
        ) => Name -> Name -> m a
throwInvalidFuncNameForGADT a b = error . show $ (ppr a, ppr b)  -- throwError $ extraFuncInfo a b

whileBuildingGADT :: ( InternalErr e
                      , MonadError e m
                      ) => Name -> m a -> m a
whileBuildingGADT a m = m  -- catchError m (throwError . withinFunction a)

whileBuildingClassInst :: ( InternalErr e
                      , MonadError e m
                      ) => Name -> m a -> m a
whileBuildingClassInst a m = m  -- catchError m (throwError . withinFunction a)
