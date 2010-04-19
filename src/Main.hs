{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad ( when )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT )

-- import Control.Monad.Trans
-- import Data.Map ( Map )
-- import qualified Data.Map as Map
-- import Data.Maybe

import System.Environment
import System.Exit

------------------------------------------------------------------------------
-- Agda library imports
-- import Agda.Syntax.Abstract.Name ( ModuleName )
-- import Agda.TypeChecking.Monad.Base ( Interface(iModuleName) )
import Agda.Utils.Impossible ( catchImpossible
--                              , Impossible(..)
--                              , throwImpossible
                              )

------------------------------------------------------------------------------
-- Local imports
-- import FOL.Pretty
import MyAgda.Interface ( getImportedModules, myReadInterface )
import Options ( Options(optHelp, optVersion), parseOptions, usage )
import Reports ( R, reportS )
import TPTP.Files ( createAxiomsFile, createConjectureFile )
import TPTP.Translation
    ( axiomsGeneralHintsToAFs
    , conjecturesToAFs
    , symbolsToAFs
    )
import TPTP.Types ( AF )
import Utils.IO ( bye )
import Utils.Version ( version )

#include "undefined.h"

------------------------------------------------------------------------------

-- We translate the ATP axioms, general hints, and definitions for a file.
translationGeneralAxioms :: FilePath -> R [AF]
translationGeneralAxioms file = do

  -- Gettting the interface.
  i <- liftIO $ myReadInterface file

  -- Gettting the ATP axioms and general hints.
  axiomsGeneralHints <- axiomsGeneralHintsToAFs i

  -- Getting the ATP definitions.
  symbols <- symbolsToAFs i

  return (axiomsGeneralHints ++ symbols )


-- TODO: It is not clear if we should use the interface or the file
-- name as the principal argument. In the case of the function
-- getImportedModules is much better to use the file name because we
-- avoid read some interfaces files unnecessary.
translation :: FilePath -> R ()
translation file = do
  reportS "" 1 $ "Translating " ++ show file ++ " ..."

  iModulesPaths <- liftIO $ getImportedModules file

  generalAxiomsCurrentFile <- translationGeneralAxioms file
  generalAxiomsImportedFiles <- mapM translationGeneralAxioms iModulesPaths

  -- We create the general axioms TPTP file
  createAxiomsFile $
    concat generalAxiomsImportedFiles ++ generalAxiomsCurrentFile

  -- Gettting the interface.
  i <- liftIO $ myReadInterface file

  -- We translate the ATP pragma conjectures and their associated hints
  -- of current module.
  conjectures <- conjecturesToAFs i

  -- We create the conjectures TPTP files
  mapM_ createConjectureFile conjectures

runAgda2ATP :: IO ()
runAgda2ATP = do
  prgName <- getProgName
  argv <- getArgs --fmap head $ liftIO getArgs

  -- Reading the command line options.
  (opts, names) <- parseOptions argv prgName

  when (optVersion opts) $ bye $ prgName ++ " version " ++ version ++ "\n"

  when (optHelp opts) $ bye $ usage prgName

  runReaderT (translation $ head names) opts

main :: IO ()
main = catchImpossible runAgda2ATP $
         \e -> do putStr $ show e
                  exitFailure
