
module Data.Typed.Error ( module P ) where

import Data.Typed.Error.Internal as P
  ( ErrorType()
  , TypedError
  , HasError(..)
  , convertError
  )

import Data.Typed.Error.TH as P
  ( makeErrClassHelpers
  )

import Data.Typed.Error.TH.Types as P
  ( defaultTypedErrorRules
  , TypedErrorRules(..)
  , defNameClassPattern
  , defNameFuncPattern
  , defNameGADTCons
  , defNameGetClass
  , defNameGADT
  , defNameGADTCons
  , defNameThrow
  , defNameWhile
  )
