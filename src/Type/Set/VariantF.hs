{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Type.Set.VariantF where

import Intro
import Prelude (fmap)
import Data.Kind
import Type.Set
import Type.Set.Variant
import Data.Type.Equality
import Unsafe.Coerce
import Data.Constraint
import Data.Functor.Classes
import Data.Typeable
import Text.Show
import GHC.TypeLits
import Exinst


------------------------------------------------------------------------------
-- | A 'VariantF' is a higher-order version of 'Variant' which can contain
--   any of the 'Functor's within its 'TypeSet'. You can use 'toVariantF' to
--   construct one, and 'fromVariantF' to pattern match it out.
data VariantF (bst :: TypeSet (Type -> Type)) (a :: Type) where
  VariantF :: SSide ss -> Follow ss bst a -> VariantF bst a
type role VariantF nominal nominal

------------------------------------------------------------------------------
-- | A proof that the set @bst@ contains functor @f@.
class HasF f bst where

  -- | Inject a @t@ into a 'VariantF'.
  toVariantF :: f a -> VariantF bst a

  -- | Attempt to project a 'VariantF' into @f a@. This might fail, because there
  -- is no guarantee that the 'VariantF' /actually contains/ @f a@.
  fromVariantF :: VariantF bst a -> Maybe (f a)

instance ( Follow (Locate f bst) bst ~ f
         -- , Locate (Follow (Locate f bst) bst) bst ~ Locate f bst
         , FromSides (Locate f bst)
         ) => HasF f bst where
  toVariantF = VariantF (fromSides @(Locate f bst))
  fromVariantF (VariantF tag res) =
    case testEquality tag (fromSides @(Locate f bst)) of
      Just Refl -> Just res
      Nothing -> Nothing

data SplitF f lbst rbst a
  = RootF (f a)
  | LSplitF (VariantF lbst a)
  | RSplitF (VariantF rbst a)

decompRootF :: VariantF ('Branch f lbst rbst) a -> SplitF f lbst rbst a
decompRootF (VariantF SNil   t) = RootF t
decompRootF (VariantF (SL s) t) = LSplitF (VariantF s t)
decompRootF (VariantF (SR s) t) = RSplitF (VariantF s t)

------------------------------------------------------------------------------
-- | A proof that inserting into a @bst@ doesn't affect the position of
-- anything already in the tree.
proveFollowInsertF :: Follow ss (Insert f bst) :~~: Follow ss bst
proveFollowInsertF = unsafeCoerce HRefl

------------------------------------------------------------------------------
-- | Weaken a 'VariantF' so that it can contain something else.
weakenF :: forall f bst a. VariantF bst a -> VariantF (Insert f bst) a
weakenF (VariantF (tag :: SSide ss) res) = VariantF (tag :: SSide ss) $
  case proveFollowInsertF @ss @f @bst of
    HRefl -> (res :: Follow ss bst a)





-- some1 :: forall (f1 :: k1 -> *) (a1 :: k1). SingI a1 => f1 a1 -> Some1 f1
--foo :: SingI [Side] => (Flip Follow bst) [Side] -> Some1 (Flip Follow bst)
-- foo = some1

-- The Exinst.Dict1 class
-- class Dict1 (c :: k0 -> Constraint) (f1 :: k1 -> k0) where
--  dict1 :: Sing (a1 :: k1) -> Dict (c (f1 a1))


type family ForAllIn (bst :: TypeSet k) (c :: k -> Constraint) :: Constraint where
  ForAllIn 'Empty c = ()
  ForAllIn ('Branch a l r) c = (c a, ForAllIn l c, ForAllIn r c)

{-

-- | Ensure that some constraint applies for all members of a 'TypeSet'
type family ForAllMembers (c :: k -> Constraint) (bst :: TypeSet k) :: Constraint where
  ForAllMembers c 'Empty = ()
  ForAllMembers c ('Branch a l r)
    = (c a, ForAllMembers c l, ForAllMembers c r)



instance (ForAllMembers Functor bst) => Functor (VariantF bst) where
  fmap f (VariantF s r) = undefined

instance ( ForAllMembers Functor bst
         , ForAllMembers Foldable bst
         ) => Foldable (VariantF bst) where
  foldMap f (VariantF s r)
    = case proveForAllMembers @Foldable @bst s of
      Sub Dict -> foldMap f r

instance ( ForAllMembers Functor bst
         , ForAllMembers Foldable bst
         , ForAllMembers Traversable bst
         ) => Traversable (VariantF bst) where
  traverse f (VariantF s r)
    = case proveForAllMembers @Traversable @bst s of
        Sub Dict -> VariantF s <$> traverse f r

instance ( ForAllMembers Show1 bst
         , ForAllMembers Typeable bst) => Show1 (VariantF bst) where

  liftShowsPrec :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS) -> Int -> VariantF bst a -> ShowS
  liftShowsPrec prec lPrec d (VariantF s r)
    = case proveForAllMembers @Show1    @bst s of
        Sub Dict -> case proveForAllMembers @Typeable @bst s of
          Sub Dict -> showParen (d > 5) $
            (showString "toVariantF @(" :: ShowS) .
            showsTypeRep (getSSTypeRep s) .
            showString ") " .
            liftShowsPrec prec lPrec 5 r
    where

       getSSTypeRep :: forall ss. SSide ss -> TypeRep
       getSSTypeRep (proveForAllMembers @Typeable @bst -> Sub Dict)
         = typeRep (Proxy @(Follow ss bst))

instance ( ForAllMembers Show1 bst
         , ForAllMembers Typeable bst
         , Show a) => Show (VariantF bst a) where
  showsPrec = showsPrec1

-}
