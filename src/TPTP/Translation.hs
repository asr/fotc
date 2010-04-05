------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

module TPTP.Translation where

-- Agda library imports
import Agda.Syntax.Common ( RoleATP )
import Agda.Syntax.Internal ( QName )

-- Local imports
import FOL.Types ( FormulaFOL )
import TPTP.Types ( AnnotatedFormula(AF) )

------------------------------------------------------------------------------

toAF :: QName -> RoleATP -> FormulaFOL -> AnnotatedFormula
toAF qName role f = AF qName role f
