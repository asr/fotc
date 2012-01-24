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

{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Types
  ( AF(MkAF)
  , allRequiredDefs
  , commonRequiredDefs
  , ConjectureSet(conjectureDefs
                 , conjectureLocalHints
                 , localHintsDefs
                 , MkConjectureSet
                 , theConjecture
                 )
  , dropCommonRequiredDefs
  , GeneralRoles(axioms, axiomsDefs, hints, hintsDefs, MkGeneralRoles)
  ) where

------------------------------------------------------------------------------
-- Haskell import

import Data.List ( (\\), sort )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common        ( ATPRole )

------------------------------------------------------------------------------
-- Local imports

import FOL.Types  ( FOLFormula )
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
  { axioms     ∷ [AF]  -- ^ The axioms.
  , axiomsDefs ∷ [AF]  -- ^ ATP definitions used by the axioms.
  , hints      ∷ [AF]  -- ^ The general hints.
  , hintsDefs  ∷ [AF]  -- ^ ATP definitions used by the general hints.
  }

data ConjectureSet = MkConjectureSet
  { theConjecture        ∷ AF    -- ^ The conjecture.
  , conjectureDefs       ∷ [AF]  -- ^ ATP definitions used by the conjecture.
  , conjectureLocalHints ∷ [AF]  -- ^ The conjecture local hints.
  , localHintsDefs       ∷ [AF]  -- ^ ATP definitions used by the local hints.
  }

allRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
allRequiredDefs generalRoles conjectureSet =
  axiomsDefs generalRoles
  ++ hintsDefs generalRoles
  ++ localHintsDefs conjectureSet
  ++ conjectureDefs conjectureSet

commonRequiredDefs ∷ GeneralRoles → ConjectureSet → [AF]
commonRequiredDefs generalRoles conjectureSet =
  if nonDuplicate allDefs then [] else duplicatesElements $ sort allDefs
  where
    allDefs ∷ [AF]
    allDefs = allRequiredDefs generalRoles conjectureSet

dropCommonRequiredDefs ∷ GeneralRoles → ConjectureSet →
                         (GeneralRoles, ConjectureSet)
dropCommonRequiredDefs generalRoles conjectureSet =
  if null commonDefs
  then (generalRoles, conjectureSet)
  else
    ( generalRoles { axiomsDefs = w
                   , hintsDefs  = x
                   }
    , conjectureSet { localHintsDefs = y
                    , conjectureDefs = z
                    }
    )
  where
    commonDefs, w, x, y, z ∷ [AF]
    commonDefs = commonRequiredDefs generalRoles conjectureSet
    w          = axiomsDefs     generalRoles  \\ commonDefs
    x          = hintsDefs      generalRoles  \\ commonDefs
    y          = localHintsDefs conjectureSet \\ commonDefs
    z          = conjectureDefs conjectureSet \\ commonDefs
