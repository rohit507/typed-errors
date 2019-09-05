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
import Data.Constraint.Unsafe
import Data.Functor.Classes
import Data.Typeable
import Text.Show
