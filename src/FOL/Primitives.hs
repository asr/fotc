-- Adapted from agdaLight (Plugins.FOL.Primitive).

module FOL.Primitives where

import FOL.Types ( TermFOL(FunFOL), Formula(Predicate) )

-- This is just an arbitrary constant which we hope doesn't
-- conflict with user constants.

app :: [TermFOL] -> TermFOL
app  = FunFOL kApp

kApp :: String
kApp = "kApp"

-- This refers to the predefined equality in the ATP.
equal :: [TermFOL] -> Formula
equal   = Predicate kEqual

kEqual :: String
kEqual = "equal"
