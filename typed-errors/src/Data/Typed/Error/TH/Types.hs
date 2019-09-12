
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
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map


instance CCIntE
instance FCIntE


-- TODO :: Replace w/ an actual type error.
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


type ClassName = String
type GADTName = String
type FuncName = String
type GADTConsName = String
type PatternName = String

-- | Options and Rules for generating typed errors.
data TypedErrorRules = TypedErrorRules {
  }

type REQErr = TypedError '[InternalErr, MonoidalErr]

newtype REQ a where
  REQ :: (ExceptT REQErr (ReaderT TypedErrorRules Q)) a -> REQ a

liftQ :: Q a -> REQ a
liftQ = REQ . lift . lift

deriving newtype instance Functor REQ
deriving newtype instance Applicative REQ
deriving newtype instance Monad REQ
deriving newtype instance Alternative REQ
deriving newtype instance MonadPlus REQ
deriving newtype instance MonadError REQErr REQ

data Context
  = ClName
  | FnName
  | TyVars
  | ErrTyVar
  | FunDeps
  | InstDecs
  | Ctxt

data ClassInfo f = ClassInfo {
    ctxt      :: f 'Ctxt
  , name      :: f 'ClName
  , tyVars    :: f 'TyVars
  , errTyVar  :: f 'ErrTyVar
  , funDeps   :: f 'FunDeps
  , clsFuncs  :: Map Name (FuncInfo f)
  , instances :: f 'InstDecs
  }

data FuncInfo f = FuncInfo {
  }

type ClassInfo' l = ClassInfo (Anns l)
type FuncInfo' l = FuncInfo (Anns l)

class AddF m hkd where
  addF :: forall f l. (Typeable f)
    => hkd f -> hkd (Anns l) -> m (hkd (Anns (f ': l)))

instance (MonadError e m) => AddF m FuncInfo where

  addF :: forall f l. (Typeable f)
    => FuncInfo f -> FuncInfo (Anns l) -> m (FuncInfo (Anns (f ': l)))
  addF (FuncInfo) (FuncInfo) = pure FuncInfo

instance (Applicative m, InternalErr e, MonadError e m) => AddF m ClassInfo where

  addF :: forall f l. (Typeable f)
    => ClassInfo f -> ClassInfo (Anns l) -> m (ClassInfo (Anns (f ': l)))
  addF (ClassInfo ctxt  nm  tv  etv  fd  fn  is )
       (ClassInfo ctxt' nm' tv' etv' fd' fn' is')
    = ClassInfo
      <$> (pure $ putAnns ctxt ctxt')
      <*> (pure $ putAnns nm   nm'  )
      <*> (pure $ putAnns tv   tv'  )
      <*> (pure $ putAnns etv  etv' )
      <*> (pure $ putAnns fd   fd'  )
      <*> (Map.mergeA
            (Map.traverseMissing
               $ \ k _ -> throwMissingFuncInfo k (someTypeRep $ typeRep @f))
            (Map.traverseMissing
               $ \ k _ -> throwExtraFuncInfo   k (someTypeRep $ typeRep @f))
            (Map.zipWithAMatched
               $ \ _ -> addF)
            fn fn')
      <*> (pure $ putAnns is   is'  )


type family HasL (m :: [k]) (l :: [k]) :: Constraint where
  HasL '[] l = ()
  HasL (s ': ss) l = (MembL s l, HasL ss l)

type family Class (a :: Context) :: * where
  Class 'Ctxt     = Cxt
  Class 'ClName   = Name
  Class 'FnName   = ()
  Class 'TyVars   = [TyVarBndr]
  Class 'ErrTyVar = Name
  Class 'FunDeps  = [FunDep]
  Class 'InstDecs = [InstanceDec]

type family GADT (a :: Context) :: * where
  GADT 'Ctxt     = ()
  GADT 'ClName   = ()
  GADT 'FnName   = ()
  GADT 'TyVars   = ()
  GADT 'ErrTyVar = ()
  GADT 'FunDeps  = ()
  GADT 'InstDecs = ()

type family GetClass (a :: Context) :: * where
  GetClass 'Ctxt     = ()
  GetClass 'ClName   = ()
  GetClass 'FnName   = ()
  GetClass 'TyVars   = ()
  GetClass 'ErrTyVar = ()
  GetClass 'FunDeps  = ()
  GetClass 'InstDecs = ()

type family Pattern (a :: Context) :: * where
  Pattern 'Ctxt     = ()
  Pattern 'ClName   = ()
  Pattern 'FnName   = ()
  Pattern 'TyVars   = ()
  Pattern 'ErrTyVar = ()
  Pattern 'FunDeps  = ()
  Pattern 'InstDecs = ()
