------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types
------------------------------------------------------------------------------

module FOL.Translation.Internal.Types where

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Common ( AgdaType )
import FOL.Types ( FormulaFOL )

------------------------------------------------------------------------------

typeToFormula    :: AgdaType -> T FormulaFOL
