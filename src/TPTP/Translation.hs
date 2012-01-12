------------------------------------------------------------------------------
-- |
-- Module      : TPTP.Translation
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of ATP pragmas to TPTP formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Translation
  ( conjecturesToAFs
  , generalRolesToAFs
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad             ( foldM, liftM2, liftM4, zipWithM )
import Data.Functor              ( (<$>) )
import Data.List                 ( nub )
import qualified Data.Map as Map ( elems, keys )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( Name
  , nameBindingSite
  , QName
  , qnameName
  )
import Agda.Syntax.Common
  ( ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint) )
import Agda.Syntax.Internal ( Clause, Type )
import Agda.TypeChecking.Monad.Base
  ( Definition(defName, defType)
  , Definitions
  )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( ifM )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.EtaExpansion ( EtaExpandible(etaExpand) )
import AgdaLib.Interface
  ( getATPAxioms
  , getATPConjectures
  , getATPHints
  , getClauses
  , getLocalHints
  , isATPDefinition
  , qNameDefinition
  , QNamesIn(qNamesIn)
  )
import AgdaLib.Syntax.DeBruijn
  ( dropProofTerm
  , TypesOfVars(typesOfVars)
  )
import FOL.Translation.Functions      ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Monad.Base                     ( getTAllDefs, isTVarsEmpty, T)
import Monad.Reports                  ( reportSLn )
import TPTP.Types
  ( AF(MkAF)
  , ConjectureSet(MkConjectureSet)
  , GeneralRoles(MkGeneralRoles)
  )
import Utils.Show ( showListLn, showLn )

#include "../undefined.h"

------------------------------------------------------------------------------

toAF ∷ ATPRole → QName → Definition → T AF
toAF role qName def = do
  let ty ∷ Type
      ty = defType def
  reportSLn "toAF" 20 $
     "Translating QName: " ++ showLn qName
     ++ "Position: " ++ showLn (nameBindingSite $ qnameName qName)
     ++ "Role: " ++ showLn role
     ++ "Type:\n" ++ show ty

  -- We eta-expand the type before the translation.
  tyEtaExpanded ← ifM isTVarsEmpty (etaExpand ty) (__IMPOSSIBLE__)

  reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++ show tyEtaExpanded

  if ty == tyEtaExpanded
     then reportSLn "toAF" 20 "The type and the eta-expanded type are equals"
     else reportSLn "toAF" 20 "The type and the eta-expanded type are different"

  -- We drop the variables which are proof terms from the types.
  reportSLn "toAF" 20 $
            "The typesOfVars are:\n" ++ showListLn (typesOfVars tyEtaExpanded)

  tyReady ← foldM dropProofTerm
                  tyEtaExpanded
                  (reverse $ typesOfVars tyEtaExpanded)

  reportSLn "toAF" 20 $ "tyReady:\n" ++ show tyReady

  -- We run the translation from Agda types to FOL.
  for ← ifM isTVarsEmpty (typeToFormula tyReady) (__IMPOSSIBLE__)

  reportSLn "toAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  ifM isTVarsEmpty (return $ MkAF qName role for) (__IMPOSSIBLE__)

-- Translation of an Agda internal function to an AF definition.
fnToAF ∷ QName → Definition → T AF
fnToAF qName def = do
  let ty ∷ Type
      ty = defType def
  reportSLn "symbolToAF" 10 $
    "Symbol: " ++ showLn qName ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol (all the symbols must
  -- be functions).
  let cls ∷ [Clause]
      cls = getClauses def

  reportSLn "symbolToAF" 10 $
    "Symbol: " ++ showLn qName ++ "Clauses: " ++ show cls

  for ← ifM isTVarsEmpty (fnToFormula qName ty cls) (__IMPOSSIBLE__)
  reportSLn "symbolToAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  return $ MkAF qName ATPDefinition for

-- We translate a local hint to an AF.
localHintToAF ∷ QName → T AF
localHintToAF qName = qNameDefinition qName >>= toAF ATPHint qName

-- We translate the local hints of an ATP conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP conjecture.
localHintsToAFs ∷ Definition → T [AF]
localHintsToAFs def = do
  let hints ∷ [QName]
      hints = getLocalHints def
  reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def)
    ++ " are:\n" ++ show hints

  mapM localHintToAF hints

-- If a QName is an ATP definition then we required it.
requiredQName ∷ QName → T [AF]
requiredQName qName = do
  qNameDef ← qNameDefinition qName

  -- We don't have recursive ATP definitions, therefore we don't get
  -- duplicates ones from this function.
  if isATPDefinition qNameDef
    then liftM2 (:)
                (fnToAF qName qNameDef)
                (requiredATPDefsByATPDefinition qNameDef)
    else return []

-- If we required an ATP definition, we also required the ATP
-- definitions used in its definition.
requiredATPDefsByATPDefinition ∷ Definition → T [AF]
requiredATPDefsByATPDefinition def = do
  -- We get all the QNames in the definition's clauses.
  let cls ∷ [Clause]
      cls = getClauses def

  -- The cls must be unitary, but it was checked elsewhere.
  let qNamesInClause ∷ [QName]
      qNamesInClause = qNamesIn cls

  fmap (nub . concat) (mapM requiredQName qNamesInClause)

requiredATPDefsByLocalHints ∷ Definition → T [AF]
requiredATPDefsByLocalHints def = do
  let hints ∷ [QName]
      hints = getLocalHints def

  hintsDefs ← mapM qNameDefinition hints

  fmap (nub . concat) (mapM requiredATPDefsByDefinition hintsDefs)

conjectureToAF ∷ QName → Definition → T ConjectureSet
conjectureToAF qName def = liftM4 MkConjectureSet
                                  (toAF ATPConjecture qName def)
                                  (requiredATPDefsByDefinition def)
                                  (localHintsToAFs def)
                                  (requiredATPDefsByLocalHints def)

-- | Translate the ATP conjectures and their local hints in the top
-- level module to TPTP formulas.
conjecturesToAFs ∷ Definitions → T [ConjectureSet]
conjecturesToAFs topLevelDefs = do
  let conjecturesDefs ∷ Definitions
      conjecturesDefs = getATPConjectures topLevelDefs

  reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM conjectureToAF
           (Map.keys conjecturesDefs)
           (Map.elems conjecturesDefs)

-- We translate the ATP axioms to FOL formulas.
axiomsToAFs ∷ T [AF]
axiomsToAFs = do
  axDefs ∷ Definitions ← getATPAxioms <$> getTAllDefs

  zipWithM (toAF ATPAxiom) (Map.keys axDefs) (Map.elems axDefs)

requiredATPDefsByDefinition ∷ Definition → T [AF]
requiredATPDefsByDefinition def = do
  -- We get all the QNames in the definition.
  let qNamesInDef ∷ [QName]
      qNamesInDef = qNamesIn def

  fmap (nub . concat) (mapM requiredQName qNamesInDef)

requiredATPDefsByAxioms ∷ T [AF]
requiredATPDefsByAxioms = do
  axDefs ∷ Definitions ← getATPAxioms <$> getTAllDefs

  fmap (nub . concat) (mapM requiredATPDefsByDefinition (Map.elems axDefs))

-- We translate the ATP general hints to FOL formulas.
generalHintsToAFs ∷ T [AF]
generalHintsToAFs = do
  ghDefs ∷ Definitions ← getATPHints <$> getTAllDefs

  zipWithM (toAF ATPHint) (Map.keys ghDefs) (Map.elems ghDefs)

requiredATPDefsByHints ∷ T [AF]
requiredATPDefsByHints = do
  ghDefs ∷ Definitions ← getATPHints <$> getTAllDefs

  fmap (nub . concat) (mapM requiredATPDefsByDefinition (Map.elems ghDefs))

-- | Translate the ATP axioms, the ATP general hints, and the ATP
-- definitions in the top level module and its imported modules to
-- TPTP formulas.
generalRolesToAFs ∷ T GeneralRoles
generalRolesToAFs = liftM4 MkGeneralRoles
                           axiomsToAFs
                           requiredATPDefsByAxioms
                           generalHintsToAFs
                           requiredATPDefsByHints
