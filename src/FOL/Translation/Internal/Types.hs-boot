------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal.Types ( typeToFormula ) where

-- Agda library imports
import Agda.Syntax.Internal ( Type )

-- Local imports
import FOL.Types  ( FOLFormula )
import Monad.Base ( T )

------------------------------------------------------------------------------

typeToFormula :: Type → T FOLFormula
