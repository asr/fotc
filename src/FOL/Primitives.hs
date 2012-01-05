------------------------------------------------------------------------------
-- |
-- Module      : FOL.Primitives
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- FOL names hard-coded in the translation from Agda types to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Adapted from AgdaLight (Plugins.FOL.Primitive).

module FOL.Primitives ( appFn, appP, equal ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( Impossible(Impossible) , throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types ( FOLTerm(FOLFun), FOLFormula(Predicate) )

#include "../undefined.h"

------------------------------------------------------------------------------

kAppFn ∷ String
kAppFn = "kAppFn"

-- | Translation to FOL functions. For example, the function @foo x1
-- ... xn@ will be translate to @kAppFn (... kAppFn (kAppFn(foo, x1),
-- x2), ..., xn)@, where @kAppFn@ is a hard-coded binary function
-- symbol.
appFn ∷ FOLTerm → FOLTerm → FOLTerm
appFn t1 t2 = FOLFun kAppFn [t1, t2]

-- | Translation to FOL predicates. For example, the predicate @P x1
-- x2 x3@ will be translate to @kAppP3 (P, x1, x2, x3)@, where
-- @kAppP3@ is a hard-coded constant 4-ary predicate symbol.
appP ∷ FOLTerm → [FOLTerm] → FOLFormula
appP _ [] = __IMPOSSIBLE__
appP p ts = Predicate name (p : ts)
  where name ∷ String
        name = "kAppP" ++ show (length ts)

-- The constant 'kEqual' refers to the predefined equality in the
-- ATPs.
-- N.B. The name "kEqual" is ***hard-coded*** in the module
-- TPTP.Pretty.
kEqual ∷ String
kEqual = "kEqual"

-- | Translation to FOL equality.
equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
