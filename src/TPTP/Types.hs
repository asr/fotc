------------------------------------------------------------------------------
-- |
-- Module      : TPTP.Types
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- TPTP types and common functions on them.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Types
  ( AF(MkAF)
  , allRequiredDefs
  , commonRequiredDefs
  , ConjectureSet(MkConjectureSet
                 , conjectureLocalHints
                 , requiredDefsByConjecture
                 , requiredDefsByLocalHints
                 , theConjecture
                 )
  , dropCommonRequiredDefs
  , GeneralRoles(MkGeneralRoles
                , axioms
                , hints
                , requiredDefsByAxioms
                , requiredDefsByHints
                )
  ) where

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

data GeneralRoles = MkGeneralRoles
  { axioms               ∷ [AF]  -- ^ The axioms.
  , requiredDefsByAxioms ∷ [AF]  -- ^ Required ATP definitions by the axioms.
  , hints                ∷ [AF]  -- ^ The general hints.
  , requiredDefsByHints  ∷ [AF]  -- ^ Required ATP definitions by the hints.
  }

data ConjectureSet = MkConjectureSet
  { theConjecture            ∷ AF    -- ^ The conjecture.
  , requiredDefsByConjecture ∷ [AF]  -- ^ The conjecture requeried definitions.
  , conjectureLocalHints     ∷ [AF]  -- ^ The conjecture local hints.
  , requiredDefsByLocalHints ∷ [AF]  -- ^ The local hints requeried definitions.
  }

allRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
allRequiredDefs generalRoles conjectureSet =
  requiredDefsByAxioms generalRoles
  ++ requiredDefsByHints generalRoles
  ++ requiredDefsByLocalHints conjectureSet
  ++ requiredDefsByConjecture conjectureSet

commonRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
commonRequiredDefs generalRoles conjectureSet =
  if nonDuplicate allDefs
    then []
    else duplicatesElements $ sort allDefs

  where
    allDefs ∷ [AF]
    allDefs = allRequiredDefs generalRoles conjectureSet

dropCommonRequiredDefs ∷ GeneralRoles → ConjectureSet →
                         (GeneralRoles, ConjectureSet)
dropCommonRequiredDefs generalRoles conjectureSet =
  if null commonDefs
    then (generalRoles, conjectureSet)
    else
      ( generalRoles { requiredDefsByAxioms = w
                     , requiredDefsByHints  = x
                     }
      , conjectureSet { requiredDefsByLocalHints = y
                      , requiredDefsByConjecture = z
                      }
      )

  where
    commonDefs, w, x, y, z ∷ [AF]
    commonDefs = commonRequiredDefs generalRoles conjectureSet
    w          = requiredDefsByAxioms     generalRoles  \\ commonDefs
    x          = requiredDefsByHints      generalRoles  \\ commonDefs
    y          = requiredDefsByLocalHints conjectureSet \\ commonDefs
    z          = requiredDefsByConjecture conjectureSet \\ commonDefs
