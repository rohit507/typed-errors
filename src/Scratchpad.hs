module Scratchpad where

import Intro
import Language.Haskell.TH

showReify :: Name -> Q [Dec]
showReify n = pure [] <* (reportWarning =<< (show <$> reify n))
