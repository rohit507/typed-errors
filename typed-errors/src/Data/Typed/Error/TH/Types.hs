
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

type ClassName = String
type GADTName = String
type FuncName = String
type GADTConsName = String
type PatternName = String

data TypedErrorRules = TypedErrorRules {
    nameGADT :: ClassName -> Maybe GADTName
    -- | constructors without a matching name will not be produced.
  , nameGADTCons :: ClassName -> FuncName -> Maybe GADTConsName
  , nameGetClass :: ClassName -> Maybe ClassName
  , nameGetLift :: ClassName -> Maybe FuncName
  , nameGetFunc :: ClassName -> Maybe FuncName
  , nameClassPattern :: ClassName -> Maybe PatternName
  , nameFuncPattern :: ClassName -> FuncName -> Maybe PatternName
  , nameThrow :: ClassName -> FuncName -> Maybe FuncName
  , nameWhile :: ClassName -> FuncName -> Maybe FuncName
  , dryRun :: Bool
  }

defTER :: TypedErrorRules
defTER = TypedErrorRules {
    nameGADT = defNameGADT
  , nameGADTCons = defNameGADTCons
  , nameGetClass = defNameGetClass
  , nameGetLift  = defNameGetLift
  , nameGetFunc  = defNameGetFunc
  , nameClassPattern = defNameClassPattern
  , nameFuncPattern = defNameFuncPattern
  , nameThrow = defNameThrow
  , nameWhile = defNamwWhile
  , dryRun = True
  }

defNameClassPattern :: ClassName -> Maybe PatternName
defNameClassPattern (s : ls) = Just $ toUpper s : ls
defNameClassPattern [] = Nothing

defNameFuncPattern :: ClassName -> FuncName -> Maybe PatternName
defNameFuncPattern _ = defNameClassPattern
defNameGADT :: ClassName -> Maybe GADTName
defNameGADT (s : ls) = Just $ toUpper s : (ls <> "ET")
defNameGADT [] = Nothing

defNameGADTCons :: ClassName -> FuncName -> Maybe GADTConsName
defNameGADTCons _ = defNameGADT

defNameGetClass :: ClassName -> Maybe ClassName
defNameGetClass n = ("Get" <>) <$> defNameGADT n

defNameGetLift :: ClassName -> Maybe FuncName
defNameGetLift (s : ls) = Just $ "lift" <> (toUpper s : ls)
defNameGetLift [] = Nothing

defNameGetFunc :: ClassName -> Maybe FuncName
defNameGetFunc (s : ls) = Just $ "from" <> (toUpper s : ls)
defNameGetFunc [] = Nothing

defNameThrow :: ClassName -> Maybe FuncName
defNameThrow (s : ls) = Just $ "throw" <> (toUpper s : ls)
defNameThrow [] = Nothing

defNameWhile :: ClassName -> Maybe FuncName
defNameWhile (s : ls) = Just $ "while" <> (toUpper s : ls)
defNameWhile [] = Nothing

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
  GC 'Ctxt     = Cxt
  GC 'ClName   = Name
  GC 'FnName   = Name
  GC 'TyVars   = [Type]
  GC 'ErrTyVar = (Name, Name)
  GC 'FunDeps  = Name
  GC 'InstDecs = Name
  GC 'Knd      = ()
  GC 'Param    = Type

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
