------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types
------------------------------------------------------------------------------

module FOL.Translation.Internal.Types where

-- Agda library imports
import Agda.Syntax.Internal ( Type )

-- Local imports
import FOL.Monad ( T )
import FOL.Types ( FOLFormula )

------------------------------------------------------------------------------

typeToFormula :: Type -> T FOLFormula
