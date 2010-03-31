{-# LANGUAGE CPP, FlexibleInstances, ScopedTypeVariables #-}

module Main where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Reader ( ask, ReaderT, runReaderT )
import Control.Monad.Trans.State ( evalState )

-- import Control.Monad.Trans
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
-- import Data.Maybe

import Prelude hiding ( print, putStr, putStrLn )

import System.Environment
import System.Exit

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Abstract ( ModuleName, QName(..) )
import Agda.Syntax.Internal ( Type )

import Agda.TypeChecking.Monad.Base
    ( Definition
    , Definitions
    , defType
    , Interface
    )

import Agda.Utils.Impossible ( catchImpossible
                             , Impossible(..)
                             , throwImpossible
                             )
import qualified Agda.Utils.IO.Locale as LocIO

------------------------------------------------------------------------------
-- Local imports
-- import FOL.Pretty
import Common.Types ( HintName, PostulateName )
import FOL.Monad ( initialVars )
import FOL.Translation
import FOL.Types
import MyAgda.Interface
    ( getAxiomsATP
    , getImportedModules
    , getHints
    , getInterface
    , getQNameDefinition
    , getConjecturesATP
    )
import MyAgda.Syntax.Abstract.Name ( moduleNameToFilePath )
import Options ( parseOptions )
import Reports ( R, reportLn )
import TPTP.Files ( createAxiomsFile, createConjectureFile )
import TPTP.Monad
import TPTP.Translation
import TPTP.Types ( AnnotatedFormula )

#include "undefined.h"

------------------------------------------------------------------------------

-- We translate the ATP pragma axioms in an interface file to FOL formulas.
axiomsToFOLs :: Interface -> R (Map PostulateName AnnotatedFormula)
axiomsToFOLs i = do

  opts <- ask

  -- We get the ATP pragmas axioms
  let axiomsDefs :: Definitions
      axiomsDefs = getAxiomsATP i
  reportLn "axiomsToFOLs" 20 $ "Axioms:\n" ++ (show $ Map.keys axiomsDefs)

  -- We get the types of the axioms.
  let axiomsTypes :: Map PostulateName Type
      axiomsTypes = Map.map defType axiomsDefs
  reportLn "axiomsToFOLs" 20 $ "Axioms types:\n" ++ (show axiomsTypes)

  -- The axioms types are translated to FOL formulas.
  formulas <- liftIO $
              mapM (\ty -> runReaderT
                             (runReaderT (typeToFormula ty) initialVars) opts)
                   (Map.elems axiomsTypes)

  -- The axioms are associated with their FOL formulas.
  let axiomsFormulas :: Map PostulateName Formula
      axiomsFormulas = Map.fromList $ zip (Map.keys axiomsTypes) formulas
  reportLn "axiomsToFOLs" 20 $ "FOL formulas:\n" ++ (show axiomsFormulas)

  let afs :: [AnnotatedFormula]
      afs = evalState
              (mapM (\(aName, formula) ->
                       (postulateToTPTP aName "axiom" formula))
                    (zip (Map.keys axiomsFormulas)
                         (Map.elems axiomsFormulas)))
              initialNames
  reportLn "axiomsToFOLs" 20 $ "TPTP formulas:\n" ++ (show afs)

  -- The axioms are associated with their TPTP formulas.
  let axiomsFormulasTPTP :: Map PostulateName AnnotatedFormula
      axiomsFormulasTPTP = Map.fromList $ zip (Map.keys axiomsFormulas) afs

  return axiomsFormulasTPTP

-- We translate the ATP pragma conjectures and their hints in an
-- interface file to FOL formulas. For each conjecture we return its
-- tranlation and a list of the translatation of its hints, i.e. we
-- return a pair ( AnnotatedFormula, [AnnotatedFormula] ).
conjecturesToFOLs :: Interface -> R [ (AnnotatedFormula, [AnnotatedFormula]) ]
conjecturesToFOLs i = do

  opts <- ask

  -- We get the ATP pragmas conjectures
  let conjecturesDefs :: Definitions
      conjecturesDefs = getConjecturesATP i
  reportLn "conjecturesToFOLs" 20 $ "Conjectures:\n" ++ (show $ Map.keys conjecturesDefs)

  -- We get the types of the conjectures.
  let conjecturesTypes :: Map PostulateName Type
      conjecturesTypes = Map.map defType conjecturesDefs
  reportLn "conjecturesToFOLs" 20 $ "Conjectures types:\n" ++ (show conjecturesTypes)

  -- The conjectures types are translated to FOL formulas.
  formulas <- liftIO $
              mapM (\ty -> runReaderT
                             (runReaderT (typeToFormula ty) initialVars) opts)
                   (Map.elems conjecturesTypes)

  -- The conjectures are associated with their FOL formulas.
  let conjecturesFormulas :: Map PostulateName Formula
      conjecturesFormulas = Map.fromList $ zip (Map.keys conjecturesTypes) formulas
  reportLn "conjecturesToFOLs" 20 $ "FOL formulas:\n" ++ (show conjecturesFormulas)


  -- We translate the hints associated with each ATP pragma conjecture to
  -- TPTP formulas.
  ( hintsAFss :: [[AnnotatedFormula]] ) <-
      mapM hintsToFOLs $ Map.elems conjecturesDefs

  -- We translate the FOL formula associated with each ATP pragma
  -- conjecture to a TPTP formula.
  let afs :: [AnnotatedFormula]
      afs = evalState
              (mapM (\(tName, formula) ->
                       (postulateToTPTP tName "prove" formula))
                    (zip (Map.keys conjecturesFormulas)
                         (Map.elems conjecturesFormulas)))
              initialNames
  reportLn "conjecturesToFOLs" 20 $ "TPTP formulas:\n" ++ (show afs)

  return $ zip afs hintsAFss

-- We translate an hint to a FOL formula.
hintToFOL :: HintName -> R AnnotatedFormula
hintToFOL hName = do

  opts <- ask

  (i :: Interface) <- liftIO $
                      getInterface $ moduleNameToFilePath $ qnameModule hName

  let hDef :: Definition
      hDef = case getQNameDefinition i hName of
               Just _hDef -> _hDef
               Nothing   -> __IMPOSSIBLE__

  let hType :: Type
      hType =  defType hDef

  formula <- liftIO $ runReaderT
                        (runReaderT (typeToFormula hType) initialVars) opts

  let af :: AnnotatedFormula
      af = evalState (postulateToTPTP hName "axiom" formula) initialNames

  return af

-- We translate the hints of an ATP pragma conjecture to FOL formulas.
-- Invariant: The Definition should be an ATP pragma conjecture
hintsToFOLs :: Definition -> R [AnnotatedFormula]
hintsToFOLs conjectureDef = do

  let hints :: [HintName]
      hints = getHints conjectureDef
  reportLn "hintsToFOLs" 20 $ "The hints for the conjecture " ++ show conjectureDef ++
           " are " ++ show hints

  ( afs :: [AnnotatedFormula] ) <- mapM hintToFOL hints

  return afs

translation :: Interface -> R ()
translation i = do

  -- We translate the ATP pragma axioms of current module and of all
  -- the imported modules.
  let importedModules :: [ModuleName]
      importedModules = getImportedModules i

  ( is :: [Interface] ) <-
      liftIO $ mapM getInterface (map moduleNameToFilePath importedModules)

  ( axiomsAFss :: [Map PostulateName AnnotatedFormula] ) <-
      mapM axiomsToFOLs (i : is)

  -- We translate the ATP pragma conjectures and their associated hints
  -- of current module.
  conjecturesAFs <- conjecturesToFOLs i

  -- We create the TPTP files.
  liftIO $ createAxiomsFile $ Map.unions axiomsAFss
  liftIO $ mapM_ createConjectureFile conjecturesAFs -- ++ concat hintsAFss

runAgdaATP :: IO ()
runAgdaATP = do
  prgName <- getProgName
  argv <- getArgs --fmap head $ liftIO getArgs

  -- Reading the command line options.
  (opts, names) <- parseOptions argv prgName

  -- Gettting the interface.
  i <- getInterface $ head names

  -- runReaderT (postulatesToFOLs i) opts
  runReaderT (translation i) opts

main :: IO ()
main = catchImpossible runAgdaATP $
         \e -> do LocIO.putStr $ show e
                  exitFailure
