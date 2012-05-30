------------------------------------------------------------------------------
-- |
-- Module      : TPTP.Types
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- TPTP types and common functions on them.
------------------------------------------------------------------------------

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Types
  ( AF(MkAF)
  , allRequiredDefs
  , commonRequiredDefs
  , ConjectureSet(defsConjecture
                 , defsLocalHints
                 , localHintsConjecture
                 , MkConjectureSet
                 , theConjecture
                 )
  , dropCommonRequiredDefs
  , GeneralRoles(axioms, defsAxioms, defsHints, hints, MkGeneralRoles)
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Eq       ( Eq((==)) )
import Data.Function ( ($) )
import Data.List     ( (++), (\\), null, sort )
import Data.Ord      ( Ord(compare) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common        ( ATPRole )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types  ( FOLFormula )
import Utils.List ( duplicatesElements, nonDuplicate )

------------------------------------------------------------------------------
-- Note: We don't import the module TPTP.ConcreteSyntax to avoid a circular
-- importation, therefore Haddock does not create a link for
-- 'TPTP.ConcreteSyntax.ToTPTP'.

-- | The TPTP annotated formulae.
-- The annotated formulae are not in TPTP concrete syntax. We get this
-- syntax via 'TPTP.TPTP.ConcreteSyntax.ToTPTP'.
data AF = MkAF QName ATPRole FOLFormula

instance Eq AF where
  (MkAF qName1 _ _) == (MkAF qName2 _ _) = qName1 == qName2

instance Ord AF where
  compare (MkAF qName1 _ _) (MkAF qName2 _ _) = compare qName1 qName2

-- | The 'ATPRole's share by all the conjetures in an Agda module.
data GeneralRoles = MkGeneralRoles
  { axioms     ∷ [AF]  -- ^ The axioms.
  , defsAxioms ∷ [AF]  -- ^ ATP definitions used by the axioms.
  , hints      ∷ [AF]  -- ^ The general hints.
  , defsHints  ∷ [AF]  -- ^ ATP definitions used by the general hints.
  }

-- | The 'ATPRole's associated with a conjecture.
data ConjectureSet = MkConjectureSet
  { theConjecture        ∷ AF    -- ^ The conjecture.
  , defsConjecture       ∷ [AF]  -- ^ ATP definitions used by the conjecture.
  , localHintsConjecture ∷ [AF]  -- ^ The conjecture local hints.
  , defsLocalHints       ∷ [AF]  -- ^ ATP definitions used by the local hints.
  }

-- | All required definitions by a conjecture.
allRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
allRequiredDefs generalRoles conjectureSet =
  defsAxioms generalRoles
  ++ defsHints generalRoles
  ++ defsLocalHints conjectureSet
  ++ defsConjecture conjectureSet

-- | Common required definitions by a conjecture.
commonRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
commonRequiredDefs generalRoles conjectureSet =
  if nonDuplicate allDefs then [] else duplicatesElements $ sort allDefs
  where
  allDefs ∷ [AF]
  allDefs = allRequiredDefs generalRoles conjectureSet

-- | Drop the common required definitions by a conjecture.
dropCommonRequiredDefs ∷ GeneralRoles → ConjectureSet →
                         (GeneralRoles, ConjectureSet)
dropCommonRequiredDefs generalRoles conjectureSet =
  if null commonDefs
  then (generalRoles, conjectureSet)
  else
    ( generalRoles { defsAxioms = w
                   , defsHints  = x
                   }
    , conjectureSet { defsLocalHints = y
                    , defsConjecture = z
                    }
    )
  where
  commonDefs ∷ [AF]
  commonDefs = commonRequiredDefs generalRoles conjectureSet

  w, x, y, z ∷ [AF]
  w          = defsAxioms     generalRoles  \\ commonDefs
  x          = defsHints      generalRoles  \\ commonDefs
  y          = defsLocalHints conjectureSet \\ commonDefs
  z          = defsConjecture conjectureSet \\ commonDefs
