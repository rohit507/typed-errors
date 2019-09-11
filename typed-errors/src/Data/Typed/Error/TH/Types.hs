
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Typed.Error.TH.Types where

import Intro
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error
import Data.Constraint
import Type.Reflection
import Data.Typed.Error.MonoidalErr
import Control.Monad.Chronicle
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Unsafe.Coerce

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

data Anns (bst :: TypeSet (k -> *)) (a :: k) where
  AEmpty :: Anns 'Empty a
  ABranch :: f a -> Anns l a -> Anns r a -> Anns ('Branch f l r) a



putAnn :: forall f a bst. f a -> Anns bst a -> Anns (Insert f bst) a
putAnn v AEmpty = ABranch v AEmpty AEmpty
putAnn v (ABranch a l r)
  = case fromSides @(Locate f (Insert f bst)) of
        SNil   -> ABranch v l r
        (SL _) -> ABranch a (putAnn v l) r
        (SR _) -> ABranch a l (putAnn v r)



getAnn :: forall f a bst . (FromSides (Locate f bst)) => Anns bst a -> f a
getAnn AEmpty = panic "unreachable"
getAnn (ABranch v l r)
  = case fromSides @(Locate f bst) of
        SNil   -> unsafeCoerce v
        (SL _) -> getAnn @f (unsafeCoerce l)
        (SR _) -> getAnn @f r


-- mergeAnns> mall a -> Anns large a -> Anns (Merge small large) a
-- mergeAnns AEmpty b = b
-- mergeAnns s AEmpty = s
-- mergeAnns (ABranch a l r) b = mergeAnns r . mergeAnns l $ putAnn a b
