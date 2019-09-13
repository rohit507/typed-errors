
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module Data.Typed.Error.TH.Types where

import Intro hiding (Type)
import Language.Haskell.TH
import Data.Typed.Error.TH.InternalErr
import Data.Typed.Error.MonoidalErr
import Data.Typed.Error
import Data.Char
import Type.Reflection
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


data TypedErrorRules = TypedErrorRules {
    nameGADT :: ClassName -> Maybe (GADTName)
    -- | constructors without a matching name will not be produced.
  , nameGADTCons :: ClassName -> FuncName -> Maybe GADTConsName
  }

defNameGADT :: ClassName -> Maybe GADTName
defNameGADT (s : ls) = Just $ toUpper s : (ls <> "ET")
defNameGADT [] = Nothing

defNameGADTCons :: ClassName -> FuncName -> Maybe GADTConsName
defNameGADTCons _ = defNameGADT

defTER :: TypedErrorRules
defTER = TypedErrorRules defNameGADT defNameGADTCons

type REQErr = TypedError '[InternalErr,MonoidalErr]

newtype REQ a where
  REQ :: (ExceptT REQErr (ReaderT TypedErrorRules Q)) a -> REQ a

runREQ :: TypedErrorRules -> REQ a -> Q (Either REQErr a)
runREQ ter (REQ m) = runReaderT (runExceptT m) ter

liftQ :: Q a -> REQ a
liftQ = REQ . lift . lift

deriving newtype instance Functor REQ
deriving newtype instance Applicative REQ
deriving newtype instance Monad REQ
deriving newtype instance Alternative REQ
deriving newtype instance MonadPlus REQ
deriving newtype instance MonadIO REQ
deriving newtype instance MonadError REQErr REQ
deriving newtype instance MonadReader TypedErrorRules REQ

data Context
  = ClName
  | FnName
  | TyVars
  | ErrTyVar
  | FunDeps
  | InstDecs
  | Ctxt
  | Knd
  | Param

data ClassInfo (f :: Context -> *) = ClassInfo {
    ctxt      :: f 'Ctxt
  , name      :: f 'ClName
  , tyVars    :: f 'TyVars
  , errTyVar  :: f 'ErrTyVar
  , funDeps   :: f 'FunDeps
  , clsFuncs  :: Map Name (FuncInfo f)
  , instances :: f 'InstDecs
  }

data FuncInfo (f :: Context -> *) = FuncInfo {
    cxt    :: f 'Ctxt
  , name   :: f 'FnName
  , tyVars :: f 'TyVars
  , params :: [f 'Param]
  }

type ClassInfo' l = ClassInfo (Anns l)
type FuncInfo' l = FuncInfo (Anns l)

class AddF m hkd where
  addF :: forall f l. (Typeable f)
    => hkd f -> hkd (Anns l) -> m (hkd (Anns (f ': l)))

instance (MonadError e m) => AddF m FuncInfo where

  addF :: forall f l. (Typeable f)
    => FuncInfo f -> FuncInfo (Anns l) -> m (FuncInfo (Anns (f ': l)))
  addF (FuncInfo ctxt  nm  tv  ps )
       (FuncInfo ctxt' nm' tv' ps')
    = pure $ FuncInfo
      (putAnns ctxt ctxt')
      (putAnns nm   nm'  )
      (putAnns tv   tv'  )
      (zipWith putAnns ps ps')

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

type family C (a :: Context) :: * where
  C 'Ctxt     = Cxt
  C 'ClName   = Name
  C 'FnName   = Name
  C 'TyVars   = [TyVarBndr]
  C 'ErrTyVar = TyVarBndr
  C 'FunDeps  = [FunDep]
  C 'InstDecs = [InstanceDec]
  C 'Knd      = ()
  C 'Param    = Type

data Class a where
  C :: { getC :: C a } -> Class a

deriving instance (Eq (C a)) => Eq (Class a)

type family G (a :: Context) :: * where
  G 'Ctxt     = Cxt
  G 'ClName   = Name
  G 'FnName   = Name
  G 'TyVars   = ()
  G 'ErrTyVar = Type
  G 'FunDeps  = ()
  G 'InstDecs = ()
  G 'Knd      = ()
  G 'Param    = Type

data GADT a where
  G :: { getG :: G a }-> GADT a

deriving instance (Eq (G a)) => Eq (GADT a)

type family GC (a :: Context) :: * where
  GC 'Ctxt     = ()
  GC 'ClName   = ()
  GC 'FnName   = ()
  GC 'TyVars   = ()
  GC 'ErrTyVar = ()
  GC 'FunDeps  = ()
  GC 'InstDecs = ()
  GC 'Knd      = ()
  GC 'Param    = ()

data GetClass a where
  GC :: { getGC :: GC a }-> GetClass a

deriving instance (Eq (GC a)) => Eq (GetClass a)

type family P (a :: Context) :: * where
  P 'Ctxt     = ()
  P 'ClName   = ()
  P 'FnName   = ()
  P 'TyVars   = ()
  P 'ErrTyVar = ()
  P 'FunDeps  = ()
  P 'InstDecs = ()
  P 'Knd      = ()
  P 'Param    = ()

data Pattern a where
  P :: { getP :: P a } -> Pattern a

deriving instance (Eq (P a)) => Eq (Pattern a)
