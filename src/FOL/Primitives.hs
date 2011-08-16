------------------------------------------------------------------------------
-- FOL names hard-coded in the translation from Agda types to FOL formulas
------------------------------------------------------------------------------

-- Adapted from AgdaLight (Plugins.FOL.Primitive).

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Primitives
  ( appFn
  , appP1, appP2, appP3, appP4 , appP5, appP6, appP7, appP8 , appP9, appP10
  , equal
  ) where

-- Agda library imports
import Agda.Utils.Impossible
  ( Impossible(Impossible)
  , throwImpossible
  )

-- Local imports
import FOL.Types ( FOLTerm(FOLFun), FOLFormula(Predicate) )

#include "../undefined.h"

------------------------------------------------------------------------------
-- Constant binary function symbol used to translate the functions (we
-- hope it doesn't conflict with user constants).

-- The function 'foo x1 ... xn' will be translate to
-- 'kAppFn (... kAppFn (kAppFn(foo, x1), x2), ..., xn)'.

kAppFn ∷ String
kAppFn = "kAppFn"

appFn ∷ FOLTerm → FOLTerm → FOLTerm
appFn t1 t2 = FOLFun kAppFn [t1, t2]

-- Constant n+1-ary predicate symbol used to translate n-ary
-- predicates. For example, the predicate P w x y z will be translate
-- to kAppP4(p, w, x, y, z).

kAppP1 , kAppP2 , kAppP3 , kAppP4 , kAppP5 ∷ String
kAppP6 , kAppP7 , kAppP8 , kAppP9 , kAppP10 ∷ String
kAppP1  = "kAppP1"
kAppP2  = "kAppP2"
kAppP3  = "kAppP3"
kAppP4  = "kAppP4"
kAppP5  = "kAppP5"
kAppP6  = "kAppP6"
kAppP7  = "kAppP7"
kAppP8  = "kAppP8"
kAppP9  = "kAppP9"
kAppP10 = "kAppP10"

appP1 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP1 p ts =
  case length ts of
    1 → Predicate kAppP1 (p : ts)
    _ → __IMPOSSIBLE__

appP2 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP2 p ts =
  case length ts of
    2 → Predicate kAppP2 (p : ts)
    _ → __IMPOSSIBLE__

appP3 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP3 p ts =
  case length ts of
    3 → Predicate kAppP3 (p : ts)
    _ → __IMPOSSIBLE__

appP4 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP4 p ts =
  case length ts of
    4 → Predicate kAppP4 (p : ts)

    _ → __IMPOSSIBLE__
appP5 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP5 p ts =
  case length ts of
    5 → Predicate kAppP5 (p : ts)
    _ → __IMPOSSIBLE__

appP6 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP6 p ts =
  case length ts of
    6 → Predicate kAppP6 (p : ts)
    _ → __IMPOSSIBLE__

appP7 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP7 p ts =
  case length ts of
    7 → Predicate kAppP7 (p : ts)
    _ → __IMPOSSIBLE__

appP8 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP8 p ts =
  case length ts of
    8 → Predicate kAppP8 (p : ts)
    _ → __IMPOSSIBLE__

appP9 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP9 p ts =
  case length ts of
    9 → Predicate kAppP9 (p : ts)
    _ → __IMPOSSIBLE__

appP10 ∷ FOLTerm → [FOLTerm] → FOLFormula
appP10 p ts =
  case length ts of
    10 → Predicate kAppP10 (p : ts)
    _ → __IMPOSSIBLE__

-- This will refer to the predefined equality in the ATPs.
-- N.B. The name "kEqual" is ***hard-coded*** in the module TPTP.Pretty.
kEqual ∷ String
kEqual = "kEqual"

equal ∷ FOLTerm → FOLTerm → FOLFormula
equal t1 t2 = Predicate kEqual [t1, t2]
