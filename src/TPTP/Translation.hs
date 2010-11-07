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
-- import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Reader ( ask )
import Control.Monad.Trans.State ( put )

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
import Common ( AllDefinitions, iVarNames, T, TopLevelDefinitions )
import FOL.Translation.Functions ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Options ( Options(optDefAsAxiom) )
import Reports ( reportSLn )
import TPTP.Types ( AF(MkAF) )

-- #include "../undefined.h"

------------------------------------------------------------------------------

toAF :: AllDefinitions → RoleATP → QName → Definition → T AF
toAF allDefs role qName def = do

  let ty :: Type
      ty = defType def
  lift $ lift $ reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We need eta-expand the type before the translation.
  -- We run the eta-expansion with an empty state, i.e. iVarNames.

  lift $ put iVarNames
  tyEtaExpanded ← etaExpand allDefs ty

  lift $ lift $ reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++
       show tyEtaExpanded

  -- We need to remove the references to variables which are proof
  -- terms from the type.
  let tyReady :: Type
      tyReady = removeReferenceToProofTerms tyEtaExpanded

  lift $ lift $ reportSLn "toAF" 20 $ "tyReady:\n" ++ show tyReady

  -- We run the translation from Agda types to FOL formulas with an
  -- empty state, i.e. iVarNames.
  lift $ put iVarNames
  for ← typeToFormula tyReady
  lift $ lift $ reportSLn "toAF" 20 $
           "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  return $ MkAF qName role for

-- Translation of an Agda internal function to an AF definition.
fnToAF :: QName → Definition → T AF
fnToAF qName def = do

  opts ← lift $ lift ask

  let ty :: Type
      ty = defType def
  lift $ lift $ reportSLn "symbolToAF" 10 $
           "Symbol: " ++ show qName ++ "\n" ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol
  -- (All the symbols must be functions)
  let cls :: [Clause]
      cls = getClauses def

  lift $ lift $ reportSLn "symbolToAF" 10 $
           "Symbol: " ++ show qName ++ "\n" ++ "Clauses: " ++ show cls

  -- We run the translation from ATP definitions to FOL formulas with an
  -- empty state, i.e. iVarNames.
  lift $ put iVarNames
  for ← fnToFormula qName ty cls
  lift $ lift $ reportSLn "symbolToAF" 20 $
           "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
  if optDefAsAxiom opts
    then return $ MkAF qName AxiomATP for
    else return $ MkAF qName DefinitionATP for

-- We translate the functions marked out by an ATP pragma definition
-- to AF definitions.
fnsToAFs :: AllDefinitions → T [AF]
fnsToAFs allDefs = do

  let fnDefs :: Definitions
      fnDefs = getRoleATP DefinitionATP allDefs

  zipWithM fnToAF (Map.keys fnDefs) (Map.elems fnDefs)

-- We translate an local hint to an AF.
localHintToAF :: AllDefinitions → QName → T AF
localHintToAF allDefs qName = do

  let def :: Definition
      def = qNameDefinition allDefs qName

  toAF allDefs HintATP qName def

-- We translate the local hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
localHintsToAFs :: AllDefinitions → Definition → T [AF]
localHintsToAFs allDefs def = do

  let hints :: [QName]
      hints = getLocalHints def
  lift $ lift $ reportSLn "hintsToFOLs" 20 $
           "The local hints for the conjecture " ++ show (defName def) ++
           " are:\n" ++ show hints

  mapM (localHintToAF allDefs) hints

conjectureToAF :: AllDefinitions → QName → Definition → T (AF, [AF])
conjectureToAF allDefs qName def =

  liftM2 (,) (toAF allDefs ConjectureATP qName def)
             (localHintsToAFs allDefs def)

-- We translate the ATP pragma conjectures and their local hints in
-- the top level module. For each conjecture we return its translation
-- and a list of the translation of its local hints, i.e. we return a
-- pair (AF, [AF]).
conjecturesToAFs :: AllDefinitions → TopLevelDefinitions → T [(AF, [AF])]
conjecturesToAFs allDefs tlDefs = do

  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP tlDefs
  lift $ lift $ reportSLn "conjecturesToFOLs" 20 $
           "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM (conjectureToAF allDefs)
           (Map.keys conjecturesDefs)
           (Map.elems conjecturesDefs)

-- We translate the ATP pragma axioms to FOL formulas.
axiomsToAFs :: AllDefinitions → T [AF]
axiomsToAFs allDefs = do

  let axDefs :: Definitions
      axDefs = getRoleATP AxiomATP allDefs

  zipWithM (toAF allDefs AxiomATP) (Map.keys axDefs) (Map.elems axDefs)

-- We translate the ATP pragma general hints in an interface file to
-- FOL formulas.
generalHintsToAFs :: AllDefinitions → T [AF]
generalHintsToAFs allDefs = do

  let ghDefs :: Definitions
      ghDefs = getRoleATP HintATP allDefs

  zipWithM (toAF allDefs HintATP) (Map.keys ghDefs) (Map.elems ghDefs)

-- We translate the ATP axioms, (general) hints, and definitions of
-- the top level module and its imported modules. These TPTP roles are
-- common to every conjecture.
generalRolesToAFs :: AllDefinitions → T [AF]
generalRolesToAFs allDefs =
    liftM3 (\xs ys zs → xs ++ ys ++ zs)
           (axiomsToAFs allDefs)
           (generalHintsToAFs allDefs)
           (fnsToAFs allDefs)
