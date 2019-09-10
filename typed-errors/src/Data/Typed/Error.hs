
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Typed.Error where

import Intro hiding (Type)
import Language.Haskell.TH
import Data.Constraint
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH

-- | An open type family which matches an error constraint with the
--   corresponding generated GADT
--
--   to be exported
type family ErrorType (c :: * -> Constraint) = (r :: * -> *) | r -> c

-- | Converts a list of error constraints that we should satisfy into a
--   a TypeSet of GADTs that can store those errors.
--
--   to be hidden
type family ErrorList (l :: [* -> Constraint]) :: TypeSet (* -> *) where
  ErrorList '[] = 'Empty
  ErrorList (a ': as) = Insert (ErrorType a) (ErrorList as)

-- | Synonym for a typed error that uses a list of constraints.
--   exported
type TypedError p = TypedErrorV (ErrorList p)

-- | A variant type that can store a number of the Generated error classes.
--   hidden
newtype TypedErrorV (p :: TypeSet (* -> *)) where
  TypedErrorV :: { getError :: VariantF p (TypedErrorV p) } -> TypedErrorV p

-- | Extract or insert rules into Errors.
--   exported
class HasError (f :: * -> Constraint) (p :: [* -> Constraint]) where

  fromError :: TypedError p -> Maybe ((ErrorType f) (TypedError p))

  toError :: (ErrorType f) (TypedError p) -> TypedError p

instance (HasF (ErrorType f) (ErrorList p)) => HasError f p where

  fromError (TypedErrorV a) = fromVariantF a

  toError f = TypedErrorV $ toVariantF f

-- | Intermediate class we use in order to
--   hidden
class RewriteError (e :: *) (p :: * -> *)  where
  rewriteError :: p e -> e

-- | exported
class ConvertError (e :: *) (p :: [* -> Constraint]) where
  convertError :: TypedError p -> e

instance ( ForAllIn (RewriteError e) (ErrorList p)
         , ForAllIn Functor (ErrorList p)
         ) => ConvertError e p where
  convertError (TypedErrorV (VariantF s b))
    = case forMember @_ @(RewriteError e) @(ErrorList p) s of
        Dict -> case forMember @_ @Functor @(ErrorList p) s of
          Dict -> rewriteError $ convertError <$> b

-- TODO ::
--     - Write Eq, Ord, Show, Generic, NFData, Hashable
--       Functor, Foldable, Traversable and Typeable instances for Error
