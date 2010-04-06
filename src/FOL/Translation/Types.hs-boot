------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Types
------------------------------------------------------------------------------

module FOL.Translation.Types where

-- Agda library imports
import Agda.Syntax.Common ( Arg )
import Agda.Syntax.Internal ( Type )

-- Local imports
import FOL.Monad ( T )
import FOL.Types ( FormulaFOL )

------------------------------------------------------------------------------

type AgdaType = Type

argTypeToFormula :: Arg AgdaType -> T FormulaFOL
typeToFormula    :: AgdaType -> T FormulaFOL

