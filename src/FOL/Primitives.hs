------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------
-- Adapted from agdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}

module FOL.Primitives where

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Types ( TermFOL(FunFOL), FormulaFOL(Predicate) )

#include "../undefined.h"

------------------------------------------------------------------------------

-- This is just an arbitrary constant which we hope doesn't
-- conflict with user constants.
kApp :: String
kApp = "kApp"

app :: [TermFOL] -> TermFOL
app (t1 : t2 : []) = FunFOL kApp [t1, t2]
app _              = __IMPOSSIBLE__


-- This will refer to the predefined equality in the ATP.
kEqual :: String
kEqual = "kEqual"

equal :: [TermFOL] -> FormulaFOL
equal (t1 : t2 : [])  = Predicate kEqual [t1, t2]
equal _               = __IMPOSSIBLE__
