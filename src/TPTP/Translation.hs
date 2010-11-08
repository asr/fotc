------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Translation
    ( conjecturesToAFs
    , generalRolesToAFs
    )
    where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( liftM2, liftM3, zipWithM )
import Control.Monad.Reader ( ask )
import Control.Monad.State ( put )

-- import Data.Map ( Map )
import qualified Data.Map as Map ( elems, keys )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common
    ( RoleATP(AxiomATP, ConjectureATP, DefinitionATP, HintATP) )
import Agda.Syntax.Internal ( Clause, Type )
import Agda.TypeChecking.Monad.Base
    ( Definition
    , Definitions
    , defName
    , defType
    )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.EtaExpansion ( etaExpand )
import AgdaLib.Interface
    ( getClauses
    , getLocalHints
    , getRoleATP
    , qNameDefinition
    )
import AgdaLib.Syntax.DeBruijn ( removeReferenceToProofTerms )
import Common ( iVarNames, T, TopLevelDefinitions )
import FOL.Translation.Functions ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Options ( Options(optDefAsAxiom) )
import Reports ( reportSLn )
import TPTP.Types ( AF(MkAF) )

-- #include "../undefined.h"

------------------------------------------------------------------------------

toAF :: RoleATP → QName → Definition → T AF
toAF role qName def = do

  let ty :: Type
      ty = defType def
  reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We need eta-expand the type before the translation.
  -- We run the eta-expansion with an empty state, i.e. iVarNames.

  put iVarNames
  tyEtaExpanded ← etaExpand ty

  reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++ show tyEtaExpanded

  -- We need to remove the references to variables which are proof
  -- terms from the type.
  let tyReady :: Type
      tyReady = removeReferenceToProofTerms tyEtaExpanded

  reportSLn "toAF" 20 $ "tyReady:\n" ++ show tyReady

  -- We run the translation from Agda types to FOL formulas with an
  -- empty state, i.e. iVarNames.
  put iVarNames
  for ← typeToFormula tyReady
  reportSLn "toAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  return $ MkAF qName role for

-- Translation of an Agda internal function to an AF definition.
fnToAF :: QName → Definition → T AF
fnToAF qName def = do

  (_, opts) ← ask

  let ty :: Type
      ty = defType def
  reportSLn "symbolToAF" 10 $
    "Symbol: " ++ show qName ++ "\n" ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol
  -- (All the symbols must be functions)
  let cls :: [Clause]
      cls = getClauses def

  reportSLn "symbolToAF" 10 $
    "Symbol: " ++ show qName ++ "\n" ++ "Clauses: " ++ show cls

  -- We run the translation from ATP definitions to FOL formulas with an
  -- empty state, i.e. iVarNames.
  put iVarNames
  for ← fnToFormula qName ty cls
  reportSLn "symbolToAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
  if optDefAsAxiom opts
    then return $ MkAF qName AxiomATP for
    else return $ MkAF qName DefinitionATP for

-- We translate the functions marked out by an ATP pragma definition
-- to AF definitions.
fnsToAFs :: T [AF]
fnsToAFs = do

  (allDefs, _ ) ← ask

  let fnDefs :: Definitions
      fnDefs = getRoleATP DefinitionATP allDefs

  zipWithM fnToAF (Map.keys fnDefs) (Map.elems fnDefs)

-- We translate an local hint to an AF.
localHintToAF :: QName → T AF
localHintToAF qName = do

  (allDefs, _ ) ← ask

  let def :: Definition
      def = qNameDefinition allDefs qName

  toAF HintATP qName def

-- We translate the local hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
localHintsToAFs :: Definition → T [AF]
localHintsToAFs def = do

  let hints :: [QName]
      hints = getLocalHints def
  reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def) ++
    " are:\n" ++ show hints

  mapM localHintToAF hints

conjectureToAF :: QName → Definition → T (AF, [AF])
conjectureToAF qName def =

  liftM2 (,) (toAF ConjectureATP qName def)
             (localHintsToAFs def)

-- We translate the ATP pragma conjectures and their local hints in
-- the top level module. For each conjecture we return its translation
-- and a list of the translation of its local hints, i.e. we return a
-- pair (AF, [AF]).
conjecturesToAFs :: TopLevelDefinitions → T [(AF, [AF])]
conjecturesToAFs tlDefs = do

  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP tlDefs
  reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM conjectureToAF
           (Map.keys conjecturesDefs)
           (Map.elems conjecturesDefs)

-- We translate the ATP pragma axioms to FOL formulas.
axiomsToAFs :: T [AF]
axiomsToAFs = do

  (allDefs, _ ) ← ask

  let axDefs :: Definitions
      axDefs = getRoleATP AxiomATP allDefs

  zipWithM (toAF AxiomATP) (Map.keys axDefs) (Map.elems axDefs)

-- We translate the ATP pragma general hints in an interface file to
-- FOL formulas.
generalHintsToAFs :: T [AF]
generalHintsToAFs = do

  (allDefs, _ ) ← ask

  let ghDefs :: Definitions
      ghDefs = getRoleATP HintATP allDefs

  zipWithM (toAF HintATP) (Map.keys ghDefs) (Map.elems ghDefs)

-- We translate the ATP axioms, (general) hints, and definitions of
-- the top level module and its imported modules. These TPTP roles are
-- common to every conjecture.
generalRolesToAFs :: T [AF]
generalRolesToAFs =
    liftM3 (\xs ys zs → xs ++ ys ++ zs) axiomsToAFs generalHintsToAFs fnsToAFs
