------------------------------------------------------------------------------
-- Translation from FOL formulas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module TPTP.Translation where

-- Haskell imports
import Data.Char ( toLower )
import Data.List.HT ( replace )

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

-- A QName is a qualify name (e.g. A.B.x). We replace the dots by
-- underscores and we convert the first letter of the name to lower
-- case which is a valid TPTP syntax.
-- N.B. Agda adds an underscore to the names inside a where clause.
nameTPTP :: QName -> String
nameTPTP qName = case (replace "." "_" $ show qName) of
                   []       -> __IMPOSSIBLE__
                   (x : xs) -> toLower x : xs

externalToTPTP :: QName -> ExternalRole -> Formula -> AnnotatedFormula
externalToTPTP qName externalRole f = AF (nameTPTP qName) roleTPTP f
    where roleTPTP :: RoleTPTP
          roleTPTP = case externalRole of
                       "axiom"   -> AxiomTPTP
                       "theorem" -> ConjectureTPTP
                       _         -> __IMPOSSIBLE__
