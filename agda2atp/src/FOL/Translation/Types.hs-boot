------------------------------------------------------------------------------
-- hs-boot file for FOL.Translation.Syntax.Internal.Types.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Types
  ( domTypeToFormula
  , typeToFormula
  )
  where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common   ( Dom )
import Agda.Syntax.Internal ( Type )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types  ( FOLFormula )
import Monad.Base ( T )

------------------------------------------------------------------------------

domTypeToFormula ∷ Dom Type → T FOLFormula
typeToFormula    ∷ Type → T FOLFormula
