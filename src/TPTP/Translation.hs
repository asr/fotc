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
import Control.Monad.Trans.Error ( runErrorT, throwError )
import Control.Monad.Trans.Reader ( ask )
import Control.Monad.Trans.State ( evalStateT )

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
import Common ( AllDefinitions, ER, iVarNames, TopLevelDefinitions )
import FOL.Translation.Functions ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Options ( Options(optDefAsAxiom) )
import Reports ( reportSLn )
import TPTP.Types ( AF(MkAF) )

-- #include "../undefined.h"

------------------------------------------------------------------------------

toAF :: AllDefinitions → RoleATP → QName → Definition → ER AF
toAF allDefs role qName def = do

  let ty :: Type
      ty = defType def
  lift $ reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We need eta-expand the type before the translation.
  tyEtaExpanded ← evalStateT (etaExpand allDefs ty) iVarNames

  lift $ reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++
                                show tyEtaExpanded

  -- We need to remove the references to variables which are proof
  -- terms from the type.
  let tyReady :: Type
      tyReady = removeReferenceToProofTerms tyEtaExpanded

  lift $ reportSLn "toAF" 20 $ "tyReady:\n" ++ show tyReady

  r ← lift $ evalStateT (runErrorT (typeToFormula tyReady)) iVarNames
  case r of
    Right for → do
           lift $ reportSLn "toAF" 20 $
                    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
           return $ MkAF qName role for
    Left err → throwError err

-- Translation of an Agda internal function to an AF definition.
fnToAF :: QName → Definition → ER AF
fnToAF qName def = do

  opts ← lift ask

  let ty :: Type
      ty = defType def
  lift $ reportSLn "symbolToAF" 10 $
           "Symbol: " ++ show qName ++ "\n" ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol
  -- (All the symbols must be functions)
  let cls :: [Clause]
      cls = getClauses def

  lift $ reportSLn "symbolToAF" 10 $
                "Symbol: " ++ show qName ++ "\n" ++ "Clauses: " ++ show cls

  r ← lift $ evalStateT (runErrorT (fnToFormula qName ty cls)) iVarNames
  case r of
    Right for → do
           lift $ reportSLn "symbolToAF" 20 $
                    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
           if optDefAsAxiom opts
               then return $ MkAF qName AxiomATP for
               else return $ MkAF qName DefinitionATP for
    Left err → throwError err

-- We translate the functions marked out by an ATP pragma definition
-- to AF definitions.
fnsToAFs :: AllDefinitions → ER [AF]
fnsToAFs allDefs = do

  let fnDefs :: Definitions
      fnDefs = getRoleATP DefinitionATP allDefs

  zipWithM fnToAF (Map.keys fnDefs) (Map.elems fnDefs)

-- We translate an local hint to an AF.
localHintToAF :: AllDefinitions → QName → ER AF
localHintToAF allDefs qName = do

  let def :: Definition
      def = qNameDefinition allDefs qName

  toAF allDefs HintATP qName def

-- We translate the local hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
localHintsToAFs :: AllDefinitions → Definition → ER [AF]
localHintsToAFs allDefs def = do

  let hints :: [QName]
      hints = getLocalHints def
  lift $ reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def) ++
    " are:\n" ++ show hints

  mapM (localHintToAF allDefs) hints

conjectureToAF :: AllDefinitions → QName → Definition → ER (AF, [AF])
conjectureToAF allDefs qName def =

  liftM2 (,) (toAF allDefs ConjectureATP qName def)
             (localHintsToAFs allDefs def)

-- We translate the ATP pragma conjectures and their local hints in
-- the top level module. For each conjecture we return its translation
-- and a list of the translation of its local hints, i.e. we return a
-- pair (AF, [AF]).
conjecturesToAFs :: AllDefinitions → TopLevelDefinitions → ER [(AF, [AF])]
conjecturesToAFs allDefs tlDefs = do

  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP tlDefs
  lift $ reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM (conjectureToAF allDefs)
           (Map.keys conjecturesDefs)
           (Map.elems conjecturesDefs)

-- We translate the ATP pragma axioms to FOL formulas.
axiomsToAFs :: AllDefinitions → ER [AF]
axiomsToAFs allDefs = do

  let axDefs :: Definitions
      axDefs = getRoleATP AxiomATP allDefs

  zipWithM (toAF allDefs AxiomATP) (Map.keys axDefs) (Map.elems axDefs)

-- We translate the ATP pragma general hints in an interface file to
-- FOL formulas.
generalHintsToAFs :: AllDefinitions → ER [AF]
generalHintsToAFs allDefs = do

  let ghDefs :: Definitions
      ghDefs = getRoleATP HintATP allDefs

  zipWithM (toAF allDefs HintATP) (Map.keys ghDefs) (Map.elems ghDefs)

-- We translate the ATP axioms, (general) hints, and definitions of
-- the top level module and its imported modules. These TPTP roles are
-- common to every conjecture.
generalRolesToAFs :: AllDefinitions → ER [AF]
generalRolesToAFs allDefs =
    liftM3 (\xs ys zs → xs ++ ys ++ zs)
           (axiomsToAFs allDefs)
           (generalHintsToAFs allDefs)
           (fnsToAFs allDefs)
