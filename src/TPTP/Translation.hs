------------------------------------------------------------------------------
-- Translation of Agda ATP pragmas to TPTP formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TPTP.Translation where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad ( zipWithM )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Reader ( ask, runReaderT )

-- import Data.Map ( Map )
import qualified Data.Map as Map
import MonadUtils ( zipWith3M )
import System.Directory ( doesFileExist )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Interaction.FindFile ( toIFile )
import Agda.Syntax.Abstract.Name ( QName(..) )
import Agda.Syntax.Common ( RoleATP(..) )
import Agda.Syntax.Internal ( Clause )
import Agda.TypeChecking.Monad.Base
    ( Definition
    , Definitions
    , defName
    , defType
    , Interface
    )
import Agda.Utils.FileName ( absolute , filePath )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )
-- import Agda.Utils.Monad ( ifM )

------------------------------------------------------------------------------
-- Local imports
import FOL.Monad ( iVarNames )
import FOL.Translation.Common ( AgdaType )
import FOL.Translation.Internal.Types ( typeToFormula )
import FOL.Translation.SymbolDefinitions ( symDefToFormula )
import MyAgda.Syntax.Abstract.Name
    ( moduleNameToFilePath
    , removeLastNameModuleName
    )
import MyAgda.Interface
    ( getClauses
    , getConjectureHints
    , myReadInterface
    , getQNameDefinition
    , getRoleATP
    )
import Reports ( R, reportSLn )
import TPTP.Types ( AF(AF) )

#include "../undefined.h"

------------------------------------------------------------------------------

toAF :: QName -> RoleATP -> Definition -> R AF
toAF qName role def = do

  opts <- ask

  let ty :: AgdaType
      ty = defType def
  reportSLn "toAF" 20 $
     "Translating QName: " ++ show qName ++ "\n" ++
     "Role: " ++ show role ++ "\n" ++
     "Type:\n" ++ show ty

  for <- liftIO $ runReaderT (runReaderT (typeToFormula ty) iVarNames) opts

  reportSLn "toAF" 20 $
    "The FOL formula for " ++ show qName ++ " is:\n" ++ show for

  return $ AF qName role for

symbolToAF :: QName -> Definition -> R AF
symbolToAF qName def = do

  opts <- ask

  let ty :: AgdaType
      ty = defType def
  reportSLn "symbolToAF" 10 $ "Symbol: " ++ show qName ++ "\n" ++ "Type: " ++ show ty

  -- We get the clauses that define the symbol
  -- (All the symbols must be functions)
  let cls :: [Clause]
      cls = getClauses def

  reportSLn "symbolToAF" 10 $
                "Symbol: " ++ show qName ++ "\n" ++ "Clauses: " ++ show cls

  for <- liftIO $
         runReaderT (runReaderT (symDefToFormula qName ty cls) iVarNames) opts

  return $ AF qName DefinitionATP for

-- We translate an local hint to an AF.
conjectureHintToAF :: QName -> R AF
conjectureHintToAF qName = do

  -- Hack: In the current version of Agda the datatypes and records
  -- also introduce modules, therefore we need to test if the module
  -- name in QName has the information about the datatypes/record and
  -- remove it.

  let file :: FilePath
      file = moduleNameToFilePath $ qnameModule qName

  -- The physical interface file.
  iFile <- liftIO $ fmap (filePath . toIFile) (absolute file)

  i <- liftIO $ do
         b <- doesFileExist iFile
         case b of
           True  -> myReadInterface file
           False -> do
                  -- The module name ends in a datatype/record name.
                  let file' :: FilePath
                      file' = moduleNameToFilePath $
                                removeLastNameModuleName $ qnameModule qName
                  myReadInterface file'

  let def :: Definition
      def = case getQNameDefinition i qName of
               Just hDef -> hDef
               Nothing   -> __IMPOSSIBLE__

  af <- toAF qName AxiomATP def

  return af

-- We translate the hints of an ATP pragma conjecture to AF's.
-- Invariant: The 'Definition' must be an ATP pragma conjecture
conjectureHintsToAFs :: Definition -> R [AF]
conjectureHintsToAFs def = do

  let hints :: [QName]
      hints = getConjectureHints def
  reportSLn "hintsToFOLs" 20 $
    "The local hints for the conjecture " ++ (show $ defName def) ++
    " are:\n" ++ show hints

  ( afs :: [AF] ) <- mapM conjectureHintToAF hints

  return afs

conjectureToAF :: QName -> Definition -> R (AF, [AF])
conjectureToAF qName def = do

  conjectureAF <- toAF qName ConjectureATP def

  hintsAFs <- conjectureHintsToAFs def

  return (conjectureAF, hintsAFs)

-- We translate the ATP pragma axioms and general hints in an
-- interface file to FOL formulas.
axiomsGeneralHintsToAFs :: Interface -> R [AF]
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
conjecturesToAFs :: Interface -> R [ (AF, [AF]) ]
conjecturesToAFs i = do

  -- We get the conjectures from the interface file.
  let conjecturesDefs :: Definitions
      conjecturesDefs = getRoleATP ConjectureATP i
  reportSLn "conjecturesToFOLs" 20 $
    "Conjectures:\n" ++ show (Map.keys conjecturesDefs)

  afs <- zipWithM conjectureToAF
                  (Map.keys conjecturesDefs)
                  (Map.elems conjecturesDefs)
  return afs

-- We translate the ATP pragma definitions in an interface file to FOL
-- formulas.
symbolsToAFs :: Interface -> R [AF]
symbolsToAFs i = do

  -- We get the definitions from the interface file.
  let symDefs :: Definitions
      symDefs = getRoleATP DefinitionATP i

  afs <- zipWithM symbolToAF (Map.keys symDefs) (Map.elems symDefs)

  return afs
