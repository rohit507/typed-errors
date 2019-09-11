
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module Data.Typed.Error.TH.Types where

import Intro
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error
import Data.Constraint
import Data.Constraint.Unsafe
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

data Anns (bst :: TypeSet (* -> *)) (a :: *) where
  AEmpty :: Anns 'Empty a
  ABranch :: f a -> Anns l a -> Anns r a -> Anns ('Branch f l r) a

type IsMember f bst = (Follow (Locate f bst) bst ~ f)

memberProof :: forall (f :: * -> *) (bst :: TypeSet (* -> *)).
  IsMember f bst :- FromSides (Locate f bst)
memberProof = unsafeCoerceConstraint


putAnn :: forall f a bst. (IsMember f (Insert f bst))
  => f a -> Anns bst a -> Anns (Insert f bst) a
putAnn v AEmpty = ABranch v AEmpty AEmpty
putAnn v (ABranch a (l :: Anns l a) (r :: Anns r a))
  = case memberProof @f @(Insert f bst) of
      (Sub Dict) -> case fromSides @(Locate f (Insert f bst)) of
          SNil   -> unsafeCoerce $ ABranch v l r
          (SL _) -> case unsafeCoerce HRefl of
            (HRefl :: Follow (Locate f (Insert f l)) (Insert f l) :~~: f)
              -> unsafeCoerce $ ABranch a (putAnn v l) r
          (SR _) -> case unsafeCoerce HRefl of
            (HRefl :: Follow (Locate f (Insert f r)) (Insert f r) :~~: f)
              -> unsafeCoerce $ ABranch a l (putAnn v r)

getAnn :: forall f a bst . (IsMember f bst) => Anns bst a -> f a
getAnn AEmpty = panic "unreachable"
getAnn (ABranch (v :: g a) (l :: Anns l a) (r :: Anns r a))
  = case memberProof @f @bst of
      (Sub Dict) -> case fromSides @(Locate f bst) of
        SNil   -> unsafeCoerce v
        (SL _) -> case unsafeCoerce HRefl of
          (HRefl :: Follow (Locate f l) l :~~: f)
            -> getAnn @f l
        (SR _) -> case unsafeCoerce HRefl of
          (HRefl :: Follow (Locate f r) r :~~: f)
            -> getAnn @f r



mergeAnns :: forall small large a. Anns small a -> Anns large a -> Anns (Merge small large) a
mergeAnns AEmpty b = b
mergeAnns s AEmpty = s
mergeAnns s b = case s of
  (ABranch (fa :: f a) (l :: Anns l a) (r :: Anns r a)) ->
    case unsafeCoerce HRefl of
     (HRefl :: Merge r (Merge l (Insert f large)) :~~: Merge ('Branch f l r) large)
       -> case unsafeCoerce HRefl of
        (HRefl :: Follow (Locate f (Insert f large)) (Insert f large) :~~: f)
          -> mergeAnns @r r . mergeAnns @l l $ putAnn fa b
