

module Data.Typed.Error.TH.Rules where

import Intro hiding (Type)

type ClassName = String
type GADTName = String
type FuncName = String
type GADTConsName = String
type PatternName = String

-- | Options and Rules for generating typed errors.
data TypedErrorRules = TypedErrorRules {
    nameAssociatedGADT          :: ClassName -> GADTName
  , nameGADTConstructors        :: ClassName -> FuncName -> GADTConsName
  , nameGADTInfixCons           :: ClassName -> FuncName -> GADTConsName
  , nameClassPattern            :: ClassName -> PatternName
  , nameConstructorPatterns     :: ClassName -> FuncName -> PatternName
  , nameThrowFunction           :: ClassName -> FuncName -> FuncName
  , nameWhileFunction           :: ClassName -> FuncName -> FuncName
  , makeEq1Instance             :: Bool
  , makeOrd1Instance            :: Bool
  -- , makeShow1Instance           :: Bool
  -- , makeRead1Instance           :: Bool
  -- , makeNFData1Instance         :: Bool
  -- , makeHashable1Instance       :: Bool
  , makeFunctorInstance         :: Bool
  , makeFoldableInstance        :: Bool
  , makeTraversableInstance     :: Bool
  , makeTypedErrorClassInstance :: Bool
  , makePatterns                :: Bool
  , makeMonadErrorFuncs         :: Bool
  }
