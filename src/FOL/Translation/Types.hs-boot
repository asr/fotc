------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Types
  ( argTypeToFormula
  , typeToFormula
  ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common   ( Arg )
import Agda.Syntax.Internal ( Type )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types  ( FOLFormula )
import Monad.Base ( T )

------------------------------------------------------------------------------

argTypeToFormula ∷ Arg Type → T FOLFormula
typeToFormula    ∷ Type → T FOLFormula
