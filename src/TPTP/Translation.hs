------------------------------------------------------------------------------
-- Translation of Agda EXTERNAL pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module TPTP.Translation where

-- Haskell imports
import Data.Char ( isAlphaNum, toLower )

-- Agda library imports
import Agda.Syntax.Common ( ExternalRole )
import Agda.Syntax.Internal ( QName )
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

-- Local imports
import FOL.Types
import Names
import TPTP.Monad
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------

-- A QName is a qualify name (e.g. A.B.x). A valid TPTP name is
-- compose of letters, numbers, and underscores, begging with a lower
-- case letter or with a digit. We removed all non-valid TPTP symbols,
-- we convert the first letter to uppercase, and we add a fresh
-- part to avoid name clashing.

nameTPTP :: QName -> N String
nameTPTP qName = do
  partName <- freshName

  case filter isAlphaNum (show qName) of
    []       -> __IMPOSSIBLE__
    (x : xs) -> return $ (toLower x : xs) ++ "_" ++ partName

externalToTPTP :: QName -> ExternalRole -> Formula ->
                  N AnnotatedFormula
externalToTPTP qName externalRole f = do
  name <- nameTPTP qName

  let roleTPTP :: RoleTPTP
      roleTPTP = case externalRole of
                   "axiom"   -> AxiomTPTP
                   "theorem" -> ConjectureTPTP
                   _         -> __IMPOSSIBLE__

  return $ AF name roleTPTP f
