------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------

-- Adapted from AgdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Primitives
    ( appFn
    , appP1, appP2, appP3, appP4
    , equal
    ) where

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

-- Constant binary predicate symbol used to translate the monadic predicates.
-- The predicate 'P x' will be translate to 'kAppP1(p, x).
kAppP1 ∷ String
kAppP1 = "kAppP1"

appP1 ∷ FOLTerm → FOLTerm → FOLFormula
appP1 p t = Predicate kAppP1 [p, t]

-- Constant 3-ary predicate symbol used to translate the binary predicates.
-- The predicate 'P x y' will be translate to 'kAppP2(p, x, y).
kAppP2 ∷ String
kAppP2 = "kAppP2"

appP2 ∷ FOLTerm → FOLTerm → FOLTerm → FOLFormula
appP2 p t1 t2 = Predicate kAppP2 [p, t1, t2]

-- Constant 4-ary predicate symbol used to translate the 3-ary predicates.
-- The predicate 'P x y z' will be translate to 'kAppP3(p, x, y, z).
kAppP3 ∷ String
kAppP3 = "kAppP3"

appP3 ∷ FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLFormula
appP3 p t1 t2 t3 = Predicate kAppP3 [p, t1, t2, t3]

-- Constant 5-ary predicate symbol used to translate the 4-ary predicates.
-- The predicate 'P w x y z' will be translate to 'kAppP4(p, w, x, y, z).
kAppP4 ∷ String
kAppP4 = "kAppP4"

appP4 ∷ FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLFormula
appP4 p t1 t2 t3 t4 = Predicate kAppP4 [p, t1, t2, t3, t4]

-- This will refer to the predefined equality in the ATPs.
-- N.B. The name "kEqual" is ***hard-coded*** in the module TPTP.Pretty.
kEqual ∷ String
kEqual = "kEqual"

equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
