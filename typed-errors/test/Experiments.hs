
module Main where

import Intro
import Scratchpad
import Type.Set.VariantF
import Type.Set.Variant
import Type.Set


class EqualityErr a e where

  valuesNotEqual :: a -> e
  equalityContext :: a -> e -> e

class TypeMismatchErr e where
  typesNotEqual :: (Typeable a, Typeable b) => a -> b -> e
  withinParentMatch :: (Typeable a, Typeable b) => a -> b -> e -> e

deriveErrorTypes ''EqualityErr

deriveErrorTypes ''TypeMismatchErr

main :: IO ()
main = print 2
