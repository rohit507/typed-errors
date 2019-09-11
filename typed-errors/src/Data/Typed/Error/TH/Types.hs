

module Data.Typed.Error.TH.Types where

import Intro
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error
import Data.Typed.Error.MonoidalErr
import Control.Monad.Chronicle


instance CCIntE
instance FCIntE

type ClassName = String
type GADTName = String
type FuncName = String
type GADTConsName = String
type PatternName = String

-- | Options and Rules for generating typed errors.
data TypedErrorRules = TypedErrorRules {
    nameAssociatedGADT          :: ClassName -> GADTName
  , nameGADTConstructors        :: ClassName -> FuncName -> GADTConsName
  --, nameGADTInfixCons           :: ClassName -> FuncName -> GADTConsName
  , nameClassPattern            :: ClassName -> PatternName
  , nameConstructorPatterns     :: ClassName -> FuncName -> PatternName
  , nameThrowFunction           :: ClassName -> FuncName -> FuncName
  , nameWhileFunction           :: ClassName -> FuncName -> FuncName
  --, makeEq1Instance             :: Bool
  --, makeOrd1Instance            :: Bool
  -- , makeShow1Instance           :: Bool
  -- , forceInvalidShowInstance    :: Bool
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

type REQErr = TypedError '[InternalErr, MonoidalErr]

newtype REQ a where
  REQ :: (ChronicleT REQErr (ReaderT TypedErrorRules Q)) a -> REQ a

liftQ :: Q a -> REQ a
liftQ = REQ . lift . lift

deriving newtype instance Functor REQ
deriving newtype instance Applicative REQ
deriving newtype instance Monad REQ
deriving newtype instance Alternative REQ
deriving newtype instance MonadPlus REQ
deriving newtype instance MonadChronicle REQErr REQ
