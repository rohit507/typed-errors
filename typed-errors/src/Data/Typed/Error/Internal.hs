

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Typed.Error.Internal where

import Intro hiding (Type)
import Data.Constraint
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

-- | An open type family which matches an error constraint with the
--   corresponding generated GADT
type family ErrorType (c :: * -> Constraint) = (r :: * -> *) | r -> c

-- | Converts a list of error constraints that we should satisfy into a
--   a TypeSet of GADTs that can store those errors.
type family ErrorList (l :: [* -> Constraint]) = (r :: TypeSet (* -> *)) where
  ErrorList '[] = 'Empty
  ErrorList (a ': as) = Insert (ErrorType a) (ErrorList as)

-- | Synonym for a typed error that uses a list of constraints.
--   exported
type TypedError p = TypedErrorV (ErrorList p)

-- | A variant type that can store a number of the Generated error classes.
newtype TypedErrorV (p :: TypeSet (* -> *)) where
  TypedErrorV :: { getError :: VariantF p (TypedErrorV p) } -> TypedErrorV p

-- | Extract or insert rules into Errors.
class HasError (f :: * -> Constraint) (p :: [* -> Constraint]) where

  fromError :: TypedError p -> Maybe ((ErrorType f) (TypedError p))

  toError :: (ErrorType f) (TypedError p) -> TypedError p

instance (HasF (ErrorType f) (ErrorList p)) => HasError f p where

  fromError (TypedErrorV a) = fromVariantF a

  toError f = TypedErrorV $ toVariantF f

-- | Intermediate class we use in order to implement ConvertError
class RewriteError (e :: *) (p :: * -> *)  where
  rewriteError :: p e -> e

convertError :: forall e p. (ForAllIn (RewriteError e) (ErrorList p)
               , ForAllIn Functor (ErrorList p)
               ) => TypedError p -> e
convertError (TypedErrorV (VariantF s b))
    = case forMember @_ @(RewriteError e) @(ErrorList p) s of
        Dict -> case forMember @_ @Functor @(ErrorList p) s of
          Dict -> rewriteError $ convertError @e @p <$> b
-- TODO ::
--     - Write Eq, Ord, Show, Generic, NFData, Hashable
--       Functor, Foldable, Traversable and Typeable instances for Error
