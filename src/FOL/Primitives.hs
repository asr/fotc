------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------
-- Adapted from agdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Primitives ( app, equal ) where

-- Local imports
import FOL.Types ( FOLTerm(FOLFun), FOLFormula(Predicate) )

------------------------------------------------------------------------------
-- This is just an arbitrary constant which we hope doesn't
-- conflict with user constants.
kApp ∷ String
kApp = "kApp"

app ∷ FOLTerm → FOLTerm → FOLTerm
app t1 t2 = FOLFun kApp [t1, t2]

-- This will refer to the predefined equality in the ATP.
kEqual ∷ String
kEqual = "kEqual"

equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
