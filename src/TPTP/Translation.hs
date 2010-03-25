------------------------------------------------------------------------------
-- Translation of Agda EXTERNAL pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module TPTP.Translation where

-- Haskell imports
import Data.Char ( isAlphaNum, toLower )

-- Agda library imports
import Agda.Syntax.Internal ( QName )
import Agda.TypeChecking.Monad.Base ( ExternalRole )
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

-- Local imports
import FOL.Types
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------

-- A QName is a qualify name (e.g. A.B.x). A valid TPTP name is
-- compose of letters, numbers, and underscores, begging with a lower
-- case letter or with a digit. We removed all non-valid TPTP symbols
-- and we convert the first letter to uppercase.

nameTPTP :: QName -> String
nameTPTP qName = case filter isAlphaNum $ show qName of
                   []       -> __IMPOSSIBLE__
                   (x : xs) -> toLower x : xs

externalToTPTP :: QName -> ExternalRole -> Formula -> AnnotatedFormula
externalToTPTP qName externalRole f = AF (nameTPTP qName) roleTPTP f
    where roleTPTP :: RoleTPTP
          roleTPTP = case externalRole of
                       "axiom"   -> AxiomTPTP
                       "theorem" -> ConjectureTPTP
                       _         -> __IMPOSSIBLE__
