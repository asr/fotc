------------------------------------------------------------------------------
-- TPTP types
------------------------------------------------------------------------------

module TPTP.Types
    ( AF(MkAF)
    , ConjectureAFs(MkConjectureAFs
                   , definitionsAF
                   , localHintsAF
                   , theConjectureAF
                   )
    , GeneralRolesAF(MkGeneralRolesAF
                    , axiomsAF
                    , hintsAF
                    , requiredDefsbyAxiomsAF
                    , requiredDefsbyHintsAF
                    )
    )
    where

-- Agda library imports
import Agda.Syntax.Abstract ( QName )
import Agda.Syntax.Common   ( RoleATP )
-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types ( FOLFormula )

------------------------------------------------------------------------------
-- TODO: Why Haddock 2.8 does not create a link for TPTP.Pretty.PrettyTPTP?
-- | The TPTP annotated formulas.
-- The annotated formulas are not in TPTP syntax. We get this syntax via
-- 'TPTP.Pretty.PrettyTPTP'.
data AF = MkAF QName RoleATP FOLFormula

data GeneralRolesAF = MkGeneralRolesAF
    { axiomsAF               :: [AF]  -- ^ The axioms.
    , requiredDefsbyAxiomsAF :: [AF]  -- ^ Required ATP definitions by the axioms.
    , hintsAF                :: [AF]  -- ^ The genereal hints.
    , requiredDefsbyHintsAF  :: [AF]  -- ^ Required ATP definitions by the hints.
    }

data ConjectureAFs = MkConjectureAFs
    { theConjectureAF :: AF    -- ^ The conjecture.
    , localHintsAF    :: [AF]  -- ^ The conjecture local hints.
    , definitionsAF   :: [AF]  -- ^ The conjecture requeried definitions.
    }
