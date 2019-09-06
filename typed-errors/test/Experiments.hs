
module Main where

import Intro
import Scratchpad
import Type.Set.VariantF
import Type.Set.Variant
import Type.Set


type VF = VariantF (Insert Maybe (Insert [] 'Empty))

a :: VF String
a = toVariantF (Just "foo")

b :: VF String
b = toVariantF (Nothing)

c :: VF String
c = toVariantF @[] ["a","b","c"]

l :: [VF String]
l = [a,b,c]

main :: IO ()
main = do
  print . fromVariantF @[] $ map ('s':) c
