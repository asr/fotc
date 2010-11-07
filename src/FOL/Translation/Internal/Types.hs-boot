------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal.Types where

-- Agda library imports
import Agda.Syntax.Internal ( Type )

-- Local imports
import Common ( T )
import FOL.Types ( FOLFormula )

------------------------------------------------------------------------------

typeToFormula :: Type → T FOLFormula
