
module Main where

import Intro hiding (Type)
import Data.Typed.Error.TH
import Data.Typed.Error
import Language.Haskell.TH
import Type.Reflection

-- | Internal Error Type used when generating errors.
--   Also kinda a showcase of what a manual instance should look like
class InternalErrr e where
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


testAnn ''CrazyErr
testAnn ''InternalErrr


main :: IO ()
main = do
  let a = putAnns (Just 13) ANil
      b = putAnns @[] [1,2,3] a
  print $ getAnns @[] b
  print $ getAnns @Maybe b
