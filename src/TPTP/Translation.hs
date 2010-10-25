------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Translation
    ( axiomsToAFs
    , conjecturesToAFs
    , fnsToAFs
    , generalHintsToAFs
    ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( liftM2, zipWithM )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( runErrorT, throwError )
import Control.Monad.Trans.Reader ( ask )
import Control.Monad.Trans.State ( evalStateT )

-- import Data.Map ( Map )
import qualified Data.Map as Map ( elems, keys )
import MonadUtils ( zipWith3M )

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
    , Interface
    )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.EtaExpansion ( etaExpand )
import AgdaLib.Interface
    ( getClauses
    , getLocalHints
    , getQNameDefinition
    , getQNameInterface
    , getRoleATP
    )
import AgdaLib.Syntax.DeBruijn ( removeReferenceToProofTerms )
import Common ( ER, iVarNames )
import FOL.Translation.Functions ( fnToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import Options ( Options(optDefAsAxiom) )
import Reports ( reportSLn )
import TPTP.Types ( AF(MkAF) )

-- #include "../undefined.h"

------------------------------------------------------------------------------
toAF :: QName → RoleATP → Definition → ER AF
toAF qName role def = do

  let ty :: Type
      ty = defType def
  lift $ reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We need eta-expand the type before the translation.
  tyEtaExpanded ← evalStateT (etaExpand ty) iVarNames

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

-- We translate an local hint to an AF.
localHintToAF :: QName → ER AF
localHintToAF qName = do

  i ← getQNameInterface qName

  let def :: Definition
      def = getQNameDefinition i qName

  toAF qName HintATP def

-- We translate the local hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
localHintsToAFs :: Definition → ER [AF]
localHintsToAFs def = do

  let hints :: [QName]
      hints = getLocalHints def
  lift $ reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def) ++
    " are:\n" ++ show hints

  mapM localHintToAF hints

conjectureToAF :: QName → Definition → ER (AF, [AF])
conjectureToAF qName def =
    liftM2 (,) (toAF qName ConjectureATP def) (localHintsToAFs def)

-- We translate the ATP pragma axioms in an interface file to FOL
-- formulas.
axiomsToAFs :: Interface → ER [AF]
axiomsToAFs i = do

  -- We get the axioms from the interface file.
  let axDefs :: Definitions
      axDefs = getRoleATP AxiomATP i

  zipWith3M toAF (Map.keys axDefs) (repeat AxiomATP) (Map.elems axDefs)

-- We translate the ATP pragma general hints in an interface file to
-- FOL formulas.
generalHintsToAFs :: Interface → ER [AF]
generalHintsToAFs i = do

  -- We get the general hints from the interface file.
  let ghDefs :: Definitions
      ghDefs = getRoleATP HintATP i

  zipWith3M toAF (Map.keys ghDefs) (repeat HintATP) (Map.elems ghDefs)

-- We translate the ATP pragma conjectures and their local hints in an
-- interface file to AFs. For each conjecture we return its
-- translation and a list of the translation of its local hints, i.e. we
-- return a pair (AF, [AF]).
conjecturesToAFs :: Interface → ER [(AF, [AF])]
conjecturesToAFs i = do

  -- We get the conjectures from the interface file.
  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP i
  lift $ reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM conjectureToAF (Map.keys conjecturesDefs) (Map.elems conjecturesDefs)

-- We translate the functions marked out by an ATP pragma definition in
-- an interface file to AF definitions.
fnsToAFs :: Interface → ER [AF]
fnsToAFs i = do

  -- We get the definition's functions from the interface file.
  let fnDefs :: Definitions
      fnDefs = getRoleATP DefinitionATP i

  zipWithM fnToAF (Map.keys fnDefs) (Map.elems fnDefs)
