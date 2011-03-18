------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------

-- Adapted from AgdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Primitives ( appFn, equal ) where

-- Local imports
import FOL.Types ( FOLTerm(FOLFun), FOLFormula(Predicate) )

------------------------------------------------------------------------------
-- Constant binary function symbol used to translate the functions (we
-- hope it doesn't conflict with user constants).

-- The function 'foo x1 ... xn' will be translate to
-- 'kAppFn (... kAppFn (kAppFn(foo, x1), x2), ..., xn)'.

kAppFn ∷ String
kAppFn = "kAppFn"

appFn ∷ FOLTerm → FOLTerm → FOLTerm
appFn t1 t2 = FOLFun kAppFn [t1, t2]

-- This will refer to the predefined equality in the ATPs.
-- N.B. The name "kEqual" is ***hard-coded*** in the module TPTP.Pretty.
kEqual ∷ String
kEqual = "kEqual"

equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
