------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------

-- Adapted from agdaLight (Plugins.FOL.Primitive).

module FOL.Primitives where

import FOL.Types ( TermFOL(FunFOL), FormulaFOL(Predicate) )

-- This is just an arbitrary constant which we hope doesn't
-- conflict with user constants.

app :: [TermFOL] -> TermFOL
app  = FunFOL kApp

kApp :: String
kApp = "kApp"

-- This will refer to the predefined equality in the ATP.
equal :: [TermFOL] -> FormulaFOL
equal   = Predicate kEqual

kEqual :: String
kEqual = "kEqual"
