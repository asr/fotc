-- Adapted from agdaLight (Plugins.FOL.Primitive).

module FOL.Primitives where

import FOL.Types ( FOLTerm(FOLFun), Formula(Predicate) )

-- This is just an arbitrary constant which we hope doesn't
-- conflict with user constants.

app :: [FOLTerm] -> FOLTerm
app  = FOLFun kApp

kApp :: String
kApp = "kApp"

-- This refers to the predefined equality in the ATP.
equal :: [FOLTerm] -> Formula
equal   = Predicate kEqual

kEqual :: String
kEqual = "equal"
