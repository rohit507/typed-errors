
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module Data.Typed.Error.TH.Types where

import Intro
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error
import Type.Reflection
import Data.Typed.Error.MonoidalErr
import Control.Monad.Chronicle
import Type.Set
import Type.Set.Variant
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
  AEmpty  :: Anns 'Empty a
  ABranch :: f a -> Anns l a -> Anns r a -> Anns ('Branch f l r) a

putAnn :: forall (f :: k -> *) (bst :: TypeSet (k -> *)) a.
  (FromSides (Locate f (Insert f bst)))
  => f a -> Anns bst a -> Anns (Insert f bst) a
putAnn = put (toSideList $ fromSides @(Locate f (Insert f bst)))

  where

    put :: forall f bst a. [Side] -> f a -> Anns bst a -> Anns (Insert f bst) a
    put _ f AEmpty = unsafeCoerce $ ABranch f AEmpty AEmpty
    put [] f (ABranch g l r) = unsafeCoerce $ ABranch f l r
    put (L : ss) f (ABranch g l r) = unsafeCoerce $ ABranch f (put ss f l) r
    put (R : ss) f (ABranch g l r) = unsafeCoerce $ ABranch f l (put ss f r)

getAnn :: forall (f :: k -> *) (bst :: TypeSet (k -> *)) a.
  (FromSides (Locate f bst)) => Anns bst a -> f a
getAnn = get (toSideList $ fromSides @(Locate f bst))
  where
    get :: forall f bst a. [Side] -> Anns bst a -> f a

    get _ AEmpty = panic "unreachable"
    get []  (ABranch g l r) = unsafeCoerce g
    get (L : ss) (ABranch g l r) = unsafeCoerce $ get ss l
    get (R : ss) (ABranch g l r) = unsafeCoerce $ get ss r

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
