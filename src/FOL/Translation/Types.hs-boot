------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Types
------------------------------------------------------------------------------

module FOL.Translation.Types where

-- Agda library imports
import Agda.Syntax.Common ( Arg )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Common ( AgdaType )
import FOL.Types ( FormulaFOL )

------------------------------------------------------------------------------

argTypeToFormula :: Arg AgdaType -> T FormulaFOL
typeToFormula    :: AgdaType -> T FormulaFOL

