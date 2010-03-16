------------------------------------------------------------------------------
-- Translation from FOL formulas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module TPTP.Translation where

-- Agda library imports
import Agda.Syntax.Internal ( QName )
import Agda.TypeChecking.Monad.Base ( ExternalRole )
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

#include "../undefined.h"

-- Local imports
import FOL.Types
import TPTP.Types

------------------------------------------------------------------------------

externalToTPTP :: QName -> ExternalRole -> Formula -> LineTPTP
externalToTPTP qName "axiom"   for = AFormula (show qName) AxiomTPTP for
externalToTPTP qName "theorem" for = AFormula (show qName) ConjectureTPTP for
externalToTPTP _     _         _   = __IMPOSSIBLE__