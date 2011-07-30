------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
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

import Control.Monad        ( foldM, liftM2, liftM4, zipWithM )
import Control.Monad.State  ( get )

import Data.List                 ( nub )
-- import Data.Map ( Map )
import qualified Data.Map as Map ( elems, keys )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common
  ( ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint) )
import Agda.Syntax.Internal ( Clause, Type )
import Agda.TypeChecking.Monad.Base
  ( Definition
  , Definitions
  , defName
  , defType
  )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( ifM )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.EtaExpansion ( etaExpand )
import AgdaLib.Interface
  ( getClauses
  , getLocalHints
  , getATPRole
  , isATPDefinition
  , qNameDefinition
  , QNamesIn(qNamesIn)
  )
import AgdaLib.Syntax.DeBruijn        ( removeReferenceToProofTerm, typesOfVars )
import FOL.Translation.Functions      ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Monad.Base                     ( isTVarsEmpty, T, TState(tAllDefs))
import Monad.Reports                  ( reportSLn )
import TPTP.Types
  ( AF(MkAF)
  , ConjectureSet(MkConjectureSet)
  , GeneralRoles(MkGeneralRoles)
  )
import Utils.Show ( myShow )

#include "../undefined.h"

------------------------------------------------------------------------------

toAF ∷ ATPRole → QName → Definition → T AF
toAF role qName def = do

  let ty ∷ Type
      ty = defType def
  reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We eta-expand the type before the translation.
  tyEtaExpanded ← ifM isTVarsEmpty (etaExpand ty) (__IMPOSSIBLE__)

  reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++ show tyEtaExpanded

  if ty == tyEtaExpanded
     then reportSLn "toAF" 20 "The type and the eta-expanded type are equals"
     else reportSLn "toAF" 20 "The type and the eta-expanded type are different"

  -- We remove the references to variables which are proof terms from
  -- the type.
  reportSLn "toAF" 20 $
            "The typesOfVars are:\n" ++ myShow (typesOfVars tyEtaExpanded)

  tyReady ← foldM removeReferenceToProofTerm
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
    "Symbol: " ++ show qName ++ "\n" ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol (all the symbols must
  -- be functions).
  let cls ∷ [Clause]
      cls = getClauses def

  reportSLn "symbolToAF" 10 $
    "Symbol: " ++ show qName ++ "\n" ++ "Clauses: " ++ show cls

  for ← ifM isTVarsEmpty (fnToFormula qName ty cls) (__IMPOSSIBLE__)
  reportSLn "symbolToAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  return $ MkAF qName ATPDefinition for

-- We translate an local hint to an AF.
localHintToAF ∷ QName → T AF
localHintToAF qName = qNameDefinition qName >>= toAF ATPHint qName

-- We translate the local hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
localHintsToAFs ∷ Definition → T [AF]
localHintsToAFs def = do

  let hints ∷ [QName]
      hints = getLocalHints def
  reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def) ++
    " are:\n" ++ show hints

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

  -- TODO: To add test case. See
  -- LTC.Data.Nat.Inequalities.PropertiesATP.Sx≤Sy→x≤y

  -- We get all the QNames in the definition's clauses.
  let cls ∷ [Clause]
      cls = getClauses def

  -- The cls must be unitary, but it was checked elsewhere.
  let qNamesInClause ∷ [QName]
      qNamesInClause = qNamesIn cls

  fmap (nub . concat) (mapM requiredQName qNamesInClause)

requiredATPDefsByLocalHints ∷ Definition → T [AF]
requiredATPDefsByLocalHints def = do

  -- TODO: Add a test case. See {-# ATP prove prf S≰0 #-} from
  -- LTC.Data.Bool.PropertiesATP.≤-Bool.

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

-- We translate the ATP pragma conjectures and their local hints in
-- the top level module. For each conjecture we return its translation
-- and a list of the translation of its local hints, i.e. we return a
-- pair (AF, [AF]).
conjecturesToAFs ∷ Definitions → T [ConjectureSet]
conjecturesToAFs topLevelDefs = do

  let conjecturesDefs ∷ Definitions
      conjecturesDefs = getATPRole ATPConjecture topLevelDefs
  reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM conjectureToAF
           (Map.keys conjecturesDefs)
           (Map.elems conjecturesDefs)

-- We translate the ATP pragma axioms to FOL formulas.
axiomsToAFs ∷ T [AF]
axiomsToAFs = do
  state ← get

  let axDefs ∷ Definitions
      axDefs = getATPRole ATPAxiom $ tAllDefs state

  zipWithM (toAF ATPAxiom) (Map.keys axDefs) (Map.elems axDefs)

-- We translate the functions marked out by an ATP pragma definition
-- to annotated formulas required by a definition:
requiredATPDefsByDefinition ∷ Definition → T [AF]
requiredATPDefsByDefinition def = do

  -- We get all the QNames in the definition.
  let qNamesInDef ∷ [QName]
      qNamesInDef = qNamesIn def

  fmap (nub . concat) (mapM requiredQName qNamesInDef)

requiredATPDefsByAxioms ∷ T [AF]
requiredATPDefsByAxioms = do
  state ← get

  let axDefs ∷ Definitions
      axDefs = getATPRole ATPAxiom $ tAllDefs state

  fmap (nub . concat) (mapM requiredATPDefsByDefinition (Map.elems axDefs))

-- We translate the ATP pragma general hints in an interface file to
-- FOL formulas.
generalHintsToAFs ∷ T [AF]
generalHintsToAFs = do
  state ← get

  let ghDefs ∷ Definitions
      ghDefs = getATPRole ATPHint $ tAllDefs state

  zipWithM (toAF ATPHint) (Map.keys ghDefs) (Map.elems ghDefs)

requiredATPDefsByHints ∷ T [AF]
requiredATPDefsByHints = do
  state ← get

  let ghDefs ∷ Definitions
      ghDefs = getATPRole ATPHint $ tAllDefs state

  fmap (nub . concat) (mapM requiredATPDefsByDefinition (Map.elems ghDefs))

-- We translate the ATP axioms and (general) hints from the top level
-- module and its imported modules. These TPTP roles are common to
-- every conjecture.
generalRolesToAFs ∷ T GeneralRoles
generalRolesToAFs = liftM4 MkGeneralRoles
                           axiomsToAFs
                           requiredATPDefsByAxioms
                           generalHintsToAFs
                           requiredATPDefsByHints
