
{-# LANGUAGE UndecidableInstances #-}

module Data.Typed.Error.MonoidalErr where
import Intro hiding (Type)
import Language.Haskell.TH
import Data.Constraint
import Data.Typed.Error.Internal

type instance ErrorType Monoid = []

type MonoidalErr = Monoid

instance (HasError MonoidalErr p) => Semigroup (TypedError p) where
  a <> b
    | Just la <- fromError @Monoid a
    , Just lb <- fromError @Monoid b
    = toError $ la <> lb
  a <> b
    | Just la <- fromError @Monoid a
    = toError $ la <> [b]
  a <> b
    | Just lb <- fromError @Monoid b
    = toError $ a : lb
  a <> b
    = toError @Monoid [a,b]

instance (HasError MonoidalErr p, Semigroup (TypedError p)) => Monoid (TypedError p) where
  mempty = toError @MonoidalErr []

class (MonoidalErr i, MonoidalErr e) => GetMonoidalErr e i | e -> i where

  liftMonoidalErr :: e -> i
  fromMonoidalErr :: e -> Maybe (Dict (Monoid e, Monoid i), [i])

instance (MonoidalErr e, MonoidalErr [e], RewriteError e []
         ) => GetMonoidalErr [e] e where

  liftMonoidalErr = rewriteError
  fromMonoidalErr = Just . (Dict,)

instance (MonoidalErr (TypedError p)
         ,HasError MonoidalErr p
         ) => GetMonoidalErr (TypedError p) (TypedError p) where

  liftMonoidalErr = id

  fromMonoidalErr (fromError @MonoidalErr -> Just a) = Just (Dict,a)
  fromMonoidalErr _ = Nothing

pattern MonoidalErr :: (HasError MonoidalErr p)
                    => ()
                    => [TypedError p] -> TypedError p
pattern MonoidalErr x <- (fromError @MonoidalErr -> Just x)
  where
    MonoidalErr x = toError @MonoidalErr x

whileMonoidalErr :: ( MonoidalErr e
                  , MonadError e m
                  ) => e -> m a -> m a
whileMonoidalErr a m = catchError m (throwError . mappend a)
