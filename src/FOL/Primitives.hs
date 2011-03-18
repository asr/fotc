------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------

-- Adapted from AgdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Primitives
    ( appFn
    , appPred1, appPred2, appPred3, appPred4
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
-- The predicate 'P x' will be translate to 'kAppPred1(p, x).
kAppPred1 ∷ String
kAppPred1 = "kAppPred1"

appPred1 ∷ FOLTerm → FOLTerm → FOLFormula
appPred1 p t = Predicate kAppPred1 [p, t]

-- Constant 3-ary predicate symbol used to translate the binary predicates.
-- The predicate 'P x y' will be translate to 'kAppPred2(p, x, y).
kAppPred2 ∷ String
kAppPred2 = "kAppPred2"

appPred2 ∷ FOLTerm → FOLTerm → FOLTerm → FOLFormula
appPred2 p t1 t2 = Predicate kAppPred2 [p, t1, t2]

-- Constant 4-ary predicate symbol used to translate the 3-ary predicates.
-- The predicate 'P x y z' will be translate to 'kAppPred3(p, x, y, z).
kAppPred3 ∷ String
kAppPred3 = "kAppPred3"

appPred3 ∷ FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLFormula
appPred3 p t1 t2 t3 = Predicate kAppPred3 [p, t1, t2, t3]

-- Constant 5-ary predicate symbol used to translate the 4-ary predicates.
-- The predicate 'P w x y z' will be translate to 'kAppPred4(p, w, x, y, z).
kAppPred4 ∷ String
kAppPred4 = "kAppPred4"

appPred4 ∷ FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLTerm → FOLFormula
appPred4 p t1 t2 t3 t4 = Predicate kAppPred4 [p, t1, t2, t3, t4]

-- This will refer to the predefined equality in the ATPs.
-- N.B. The name "kEqual" is ***hard-coded*** in the module TPTP.Pretty.
kEqual ∷ String
kEqual = "kEqual"

equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
