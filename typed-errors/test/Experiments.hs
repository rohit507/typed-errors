
module Main where

import Intro
import Data.Typed.Error.TH.Types

main :: IO ()
main = do
  let a = putAnns (Just 13) ANil
      b = putAnns @[] [1,2,3] a
  print $ getAnns @[] b
  print $ getAnns @Maybe b
