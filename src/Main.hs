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
import Agda.Syntax.Abstract.Name ( ModuleName )
import Agda.TypeChecking.Monad.Base
    ( Interface(iImportedModules, iModuleName)
    )

import Agda.Utils.Impossible ( catchImpossible
--                              , Impossible(..)
--                              , throwImpossible
                              )

------------------------------------------------------------------------------
-- Local imports
-- import FOL.Pretty
import MyAgda.Syntax.Abstract.Name ( moduleNameToFilePath )
import MyAgda.Interface ( getInterface )
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

translation :: Interface -> R ()
translation i = do
  reportS "" 1 $ "Translating " ++ show (iModuleName i)

  let importedModules :: [ModuleName]
      importedModules = iImportedModules i

  ( is :: [Interface] ) <-
      liftIO $ mapM (getInterface . moduleNameToFilePath) importedModules

  -- We translate the ATP axioms and general hints of current module
  -- and of all the imported modules.
  ( axiomsGeneralHintsAFss :: [[AF]] ) <-
      mapM axiomsGeneralHintsToAFs (i : is)

  ( symbolsAFss :: [[AF]] ) <- mapM symbolsToAFs (i : is)

  -- We translate the ATP pragma conjectures and their associated hints
  -- of current module.
  conjecturesAFs <- conjecturesToAFs i


  -- We create the TPTP files.
  liftIO $ createAxiomsFile $
         concat axiomsGeneralHintsAFss ++ concat symbolsAFss
  liftIO $ mapM_ createConjectureFile conjecturesAFs -- ++ concat hintsAFss

runAgda2ATP :: IO ()
runAgda2ATP = do
  prgName <- getProgName
  argv <- getArgs --fmap head $ liftIO getArgs

  -- Reading the command line options.
  (opts, names) <- parseOptions argv prgName

  when (optVersion opts) $ bye $ prgName ++ " version " ++ version ++ "\n"

  when (optHelp opts) $ bye $ usage prgName

  -- Gettting the interface.
  i <- getInterface $ head names

  runReaderT (translation i) opts

main :: IO ()
main = catchImpossible runAgda2ATP $
         \e -> do putStr $ show e
                  exitFailure
