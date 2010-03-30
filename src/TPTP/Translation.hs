------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module TPTP.Translation where

-- Haskell imports
import Data.Char ( isAlphaNum, toLower )

-- Agda library imports
import Agda.Syntax.Common ( RoleATP )
import Agda.Syntax.Internal ( QName )
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

-- Local imports
import Common.Types
import FOL.Types
import Names
import TPTP.Monad
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------

-- A QName (see Agda.Syntax.Abstract.Name) a qualify name
-- (e.g. A.B.x). A valid TPTP name is compose of letters, numbers, and
-- underscores, begging with a lower case letter or with a digit. We
-- removed all non-valid TPTP symbols, we convert the first letter to
-- uppercase, and we add a fresh part to avoid name clashing.

nameTPTP :: QName -> N String
nameTPTP qName = do
  partName <- freshName

  case filter isAlphaNum (show qName) of
    []       -> __IMPOSSIBLE__
    (x : xs) -> return $ (toLower x : xs) ++ "_" ++ partName

postulateToTPTP :: PostulateName -> RoleATP -> Formula -> N AnnotatedFormula
postulateToTPTP pName role f = do
  name <- nameTPTP pName

  let roleTPTP :: RoleTPTP
      roleTPTP = case role of
                   "axiom"      -> AxiomTPTP
                   "conjecture" -> ConjectureTPTP
                   "theorem"    -> TheoremTPTP
                   _            -> __IMPOSSIBLE__

  return $ AF name roleTPTP f
