------------------------------------------------------------------------------
-- TPTP types and common functions on them
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Types
    ( AF(MkAF)
    , allRequiredDefsAF
    , commonRequiredDefsAF
    , ConjectureAFs(MkConjectureAFs
                   , localHintsAF
                   , requiredDefsByConjectureAF
                   , requiredDefsByLocalHintsAF
                   , theConjectureAF
                   )
    , GeneralRolesAF(MkGeneralRolesAF
                    , axiomsAF
                    , hintsAF
                    , requiredDefsByAxiomsAF
                    , requiredDefsByHintsAF
                    )
    , removeCommonRequiredDefsAF
    )
    where

-- Haskell import
import Data.List ( (\\), sort )

-- Agda library imports
import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common   ( ATPRole )
-- import qualified Agda.Utils.IO.Locale as LocIO

-- Local imports
import FOL.Types ( FOLFormula )
import Utils.List ( duplicatesElements, nonDuplicate )

------------------------------------------------------------------------------
-- Note: We don't import the module TPTP.Pretty to avoid a circular
-- importation, therefore Haddock does not create a link for
-- TPTP.Pretty.PrettyTPTP.

-- | The TPTP annotated formulas.
-- The annotated formulas are not in TPTP syntax. We get this syntax via
-- 'TPTP.Pretty.PrettyTPTP'.
data AF = MkAF QName ATPRole FOLFormula
        deriving Show

instance Eq AF where
    (MkAF qName1 _ _) == (MkAF qName2 _ _) = qName1 == qName2

instance Ord AF where
    compare (MkAF qName1 _ _) (MkAF qName2 _ _) = compare qName1 qName2

data GeneralRolesAF = MkGeneralRolesAF
    { axiomsAF               ∷ [AF]  -- ^ The axioms.
    , requiredDefsByAxiomsAF ∷ [AF]  -- ^ Required ATP definitions by the axioms.
    , hintsAF                ∷ [AF]  -- ^ The general hints.
    , requiredDefsByHintsAF  ∷ [AF]  -- ^ Required ATP definitions by the hints.
    }

data ConjectureAFs = MkConjectureAFs
    { theConjectureAF            ∷ AF    -- ^ The conjecture.
    , requiredDefsByConjectureAF ∷ [AF]  -- ^ The conjecture requeried definitions.
    , localHintsAF               ∷ [AF]  -- ^ The conjecture local hints.
    , requiredDefsByLocalHintsAF ∷ [AF]  -- ^ The local hints requeried definitions.
    }

allRequiredDefsAF ∷ GeneralRolesAF → ConjectureAFs → [AF]
allRequiredDefsAF generalRolesAF conjectureAFs =
    requiredDefsByAxiomsAF generalRolesAF ++
    requiredDefsByHintsAF generalRolesAF ++
    requiredDefsByLocalHintsAF conjectureAFs ++
    requiredDefsByConjectureAF conjectureAFs

commonRequiredDefsAF ∷ GeneralRolesAF → ConjectureAFs → [AF]
commonRequiredDefsAF grlRolesAF conjecturesAFs =
    if nonDuplicate allDefs
       then []
       else duplicatesElements $ sort allDefs

    where
      allDefs ∷ [AF]
      allDefs = allRequiredDefsAF grlRolesAF conjecturesAFs

removeCommonRequiredDefsAF ∷ GeneralRolesAF → ConjectureAFs →
                             (GeneralRolesAF, ConjectureAFs)
removeCommonRequiredDefsAF generalRolesAF conjectureAFs =
    if null commonDefs
       then (generalRolesAF, conjectureAFs)
       else
           ( generalRolesAF { requiredDefsByAxiomsAF = w
                            , requiredDefsByHintsAF  = x
                            }
           , conjectureAFs { requiredDefsByLocalHintsAF = y
                           , requiredDefsByConjectureAF  = z
                           }
           )

    where
      commonDefs, w, x, y, z ∷ [AF]
      commonDefs = commonRequiredDefsAF generalRolesAF conjectureAFs
      w          = requiredDefsByAxiomsAF generalRolesAF \\ commonDefs
      x          = requiredDefsByHintsAF generalRolesAF \\ commonDefs
      y          = requiredDefsByLocalHintsAF conjectureAFs \\ commonDefs
      z          = requiredDefsByConjectureAF conjectureAFs \\ commonDefs
