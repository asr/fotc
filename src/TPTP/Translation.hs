------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TPTP.Translation
    ( axiomsGeneralHintsToAFs
    , conjecturesToAFs
    , symbolsToAFs
    ) where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad ( zipWithM )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( runErrorT, throwError )
import Control.Monad.Trans.State ( evalStateT )

-- import Data.Map ( Map )
import qualified Data.Map as Map
import MonadUtils ( zipWith3M )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Abstract.Name ( QName(..) )
import Agda.Syntax.Common ( RoleATP(..) )
import Agda.Syntax.Internal ( Clause, Type )
import Agda.TypeChecking.Monad.Base
    ( Definition
    , Definitions
    , defName
    , defType
    , Interface
    )
-- import Agda.Utils.Impossible ( Impossible(..), throwImpossible )
-- import Agda.Utils.Monad ( ifM )

------------------------------------------------------------------------------
-- Local imports
import Common ( ER, iVarNames )
import FOL.Translation.Definitions ( defToFormula )
import FOL.Translation.Internal.Types ( typeToFormula )
import MyAgda.EtaExpansion ( etaExpandType )
import MyAgda.Interface
    ( getClauses
    , getConjectureHints
    , getQNameDefinition
    , getQNameInterface
    , getRoleATP
    )
import Reports ( reportSLn )
import TPTP.Types ( AF(AF) )

-- #include "../undefined.h"

------------------------------------------------------------------------------

toAF :: QName -> RoleATP -> Definition -> ER AF
toAF qName role def = do

  let ty :: Type
      ty = defType def
  lift $ reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  -- We need eta-expand the type before the translation.
  tyEtaExpanded <- liftIO $ evalStateT (etaExpandType ty) iVarNames

  lift $ reportSLn "toAF" 20 $ "The eta-expanded type is:\n" ++
                                show tyEtaExpanded

  r <- lift $ evalStateT (runErrorT (typeToFormula tyEtaExpanded)) iVarNames
  case r of
    Right for -> do
           lift $ reportSLn "toAF" 20 $
                    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
           return $ AF qName role for
    Left err -> throwError err

symbolToAF :: QName -> Definition -> ER AF
symbolToAF qName def = do

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

  r <- lift $ evalStateT (runErrorT (defToFormula qName ty cls)) iVarNames
  case r of
    Right for -> do
           lift $ reportSLn "symbolToAF" 20 $
                    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for
           return $ AF qName DefinitionATP for
    Left err -> throwError err

-- We translate an local hint to an AF.
conjectureHintToAF :: QName -> ER AF
conjectureHintToAF qName = do

  i <- liftIO $ getQNameInterface qName

  let def :: Definition
      def = getQNameDefinition i qName

  toAF qName AxiomATP def

-- We translate the hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
conjectureHintsToAFs :: Definition -> ER [AF]
conjectureHintsToAFs def = do

  let hints :: [QName]
      hints = getConjectureHints def
  lift $ reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ show (defName def) ++
    " are:\n" ++ show hints

  ( afs :: [AF] ) <- mapM conjectureHintToAF hints

  return afs

conjectureToAF :: QName -> Definition -> ER (AF, [AF])
conjectureToAF qName def = do

  conjectureAF <- toAF qName ConjectureATP def

  hintsAFs <- conjectureHintsToAFs def

  return (conjectureAF, hintsAFs)

-- We translate the ATP pragma axioms and general hints in an
-- interface file to FOL formulas.
axiomsGeneralHintsToAFs :: Interface -> ER [AF]
axiomsGeneralHintsToAFs i = do

  -- We get the axioms from the interface file.
  let axDefs :: Definitions
      axDefs = getRoleATP AxiomATP i

  axAFs <-
      zipWith3M toAF (Map.keys axDefs) (repeat AxiomATP) (Map.elems axDefs)

  -- We get the general hints from the interface file.
  let ghDefs :: Definitions
      ghDefs = getRoleATP HintATP i

  ghAFs <-
      zipWith3M toAF (Map.keys ghDefs) (repeat AxiomATP) (Map.elems ghDefs)

  return $ axAFs ++ ghAFs

-- We translate the ATP pragma conjectures and their hints in an
-- interface file to AFs. For each conjecture we return its
-- translation and a list of the translation of its hints, i.e. we
-- return a pair ( AF, [AF] ).
conjecturesToAFs :: Interface -> ER [ (AF, [AF]) ]
conjecturesToAFs i = do

  -- We get the conjectures from the interface file.
  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP i
  lift $ reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  zipWithM conjectureToAF (Map.keys conjecturesDefs) (Map.elems conjecturesDefs)

-- We translate the ATP pragma definitions in an interface file to FOL
-- formulas.
symbolsToAFs :: Interface -> ER [AF]
symbolsToAFs i = do

  -- We get the definitions from the interface file.
  let symDefs :: Definitions
      symDefs = getRoleATP DefinitionATP i

  zipWithM symbolToAF (Map.keys symDefs) (Map.elems symDefs)
