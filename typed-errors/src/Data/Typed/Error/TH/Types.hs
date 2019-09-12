
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module Data.Typed.Error.TH.Types where

import Intro
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error
import Type.Reflection
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

class TErr

type family MembL (a :: k) (ls :: [k]) :: Constraint where
  MembL a (a ': ls) = ()
  MembL a (b ': ls) = MembL a ls
  MembL a '[] = TErr

data Anns (bst :: [k -> *]) (a :: k) where
  ANil  :: Anns '[] a
  ACons :: Typeable f => f a -> Anns l a -> Anns (f ': l) a

putAnns :: Typeable f => f a -> Anns l a -> Anns (f ': l) a
putAnns = ACons

getAnns :: forall f l a. (Typeable f, MembL f l) => Anns l a -> f a
getAnns = get

  where

    get :: forall l. Anns l a -> f a
    get ANil = panic "unreachable"
    get (ACons (g :: g a) (ls :: Anns ls a))
      = case eqTypeRep (typeRep @f) (typeRep @g) of
        Just HRefl -> g
        Nothing -> (get ls :: f a)



-- mergeAnns :: forall small large a. Anns small a -> Anns large a -> Anns (Merge small large) a
-- mergeAnns AEmpty l = l
-- mergeAnns s AEmpty = s
-- mergeAnns s l = merge s l

--   where

--     merge :: Anns s a -> Anns l a -> Anns (Merge s l) a
--     merge AEmpty l = unsafeCoerce $ l
--     merge s AEmpty = unsafeCoerce $ s
--     merge (ABranch f l r) large
      -- = unsafeCoerce . merge r . merge l $ putAnn f large
