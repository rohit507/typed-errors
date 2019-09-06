{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Type.Set.VariantF where

import Type.Compare
import Type.Reflection
import Type.Set (TypeSet(..),Side(..),Insert(..))
import Data.Ord (Ordering(..))
import Data.Bool (Bool(..))
import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality


-- $ Fundamental goal here is to have a type level set with two properties
--    1 ) A Canonical form such that `~` is set equality
--    2 ) The ability for GHC to understand that
--         forall c m t. (ForAll c t, Member m t) => c m
--
--    The former should be doable by enforcing that a tree is always
--    left full and balanced.

type family Depth (t :: TypeSet k) :: Nat where
  Depth 'Empty = 0
  Depth ('Branch _ l r) = Max (Depth l) (Depth r) + 1

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = AppMax (CmpNat a b) a b

type family Full (t :: TypeSet k) :: Bool where
  Full 'Empty = 'True
  Full ('Branch _ l r) = Full l && Full r

type family AppMax (o :: Ordering) (a :: Nat) (b :: Nat) :: Nat where
  AppMax 'LT _ b = b
  AppMax  _  a _ = a

type family Size (t :: TypeSet k) :: Nat where
  Size 'Empty = 0
  Size ('Branch _ l r) = 1 + Size l + Size r

-- | Verifies that the tree is in its canonically balanced form, ie. it's
--   balanced and no right node has a deeper subtree than the left node
type family IsCanonical (t :: TypeSet k) :: Bool where
  IsCanonical 'Empty = 'True
  IsCanonical ('Branch a l r)
    = {- IsCanonical l && IsCanonical r && -}
      (ShouldRotate ('Branch a l r) == 'NoRotation)

data Rotate = RotateLeft | RotateRight | NoRotation

type family ShouldRotate (t :: TypeSet k) :: Rotate where
  ShouldRotate 'Empty = 'NoRotation
  ShouldRotate ('Branch a l r)
    = AppShouldRotate (Depth r <=? Depth l) (Depth l <=? (Depth r + 1))

type family AppShouldRotate (rightSmall :: Bool) (leftBig :: Bool) :: Rotate where
  AppShouldRotate 'True  'True  = 'NoRotation
  AppShouldRotate _      'False = 'RotateRight
  AppShouldRotate 'False _      = 'RotateLeft

type family AppRotate (r :: Rotate) (t :: TypeSet k) :: TypeSet k where
  AppRotate 'NoRotation t = t
  AppRotate 'RotateLeft  ('Branch q ('Branch p a b) c) = ('Branch p a ('Branch q b c))
  AppRotate 'RotateRight ('Branch p a ('Branch q b c)) = ('Branch q ('Branch p a b) c)
  AppRotate 'RotateLeft  t = TypeError ('Text "Left Rotation not possible for :" ':<>: 'ShowType t)
  AppRotate 'RotateRight t = TypeError ('Text "Right Rotation not possible for :" ':<>: 'ShowType t)

type family AppCanonical (c :: Bool) (t :: TypeSet k) :: TypeSet k where
  AppCanonical 'True t = t
  AppCanonical 'False 'Empty = 'Empty
  AppCanonical 'False t = AppRotate (ShouldRotate (Canonical t)) (Canonical t)

type family Canonical (t :: TypeSet k) :: TypeSet k where
  Canonical 'Empty = 'Empty
  Canonical ('Branch a l r)
    = AppCanonical (IsCanonical ('Branch a (Canonical l) (Canonical r)))
                                ('Branch a (Canonical l) (Canonical r))
