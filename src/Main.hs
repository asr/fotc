{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( when )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error
    ( catchError
    , ErrorT
    , runErrorT
    , throwError
    )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT )

import System.Environment ( getArgs, getProgName)
import System.Exit ( exitFailure, exitSuccess )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( catchImpossible )

------------------------------------------------------------------------------
-- Local imports

-- import FOL.Pretty
import ATP.ATP ( callATP )
import Common ( ER )
import MyAgda.Interface ( getImportedModules, myReadInterface )
import Options
    ( Options(optHelp, optVersion)
    , processOptions
    , usage
    )
import Reports ( reportS )
import TPTP.Translation
    ( axiomsToAFs
    , generalHintsToAFs
    , conjecturesToAFs
    , fnsToAFs
    )
import TPTP.Types ( AF )
import Utils.IO ( bye )
import Utils.Version ( version )

#include "undefined.h"

------------------------------------------------------------------------------
-- We translate the ATP axioms, (general) hints, and definitions for a
-- file. These TPTP roles are common to every conjecture.
translationGeneralRoles :: FilePath → ER [AF]
translationGeneralRoles file = do

  -- Getting the interface.
  i ← liftIO $ myReadInterface file

  -- Getting the ATP axioms.
  axioms ← axiomsToAFs i

  -- Getting the ATP general hints.
  generalHints ← generalHintsToAFs i

  -- Getting the ATP definitions.
  fns ← fnsToAFs i

  return (axioms ++ generalHints ++ fns )

-- TODO: It is not clear if we should use the interface or the file
-- name as the principal argument. In the case of the function
-- getImportedModules is much better to use the file name because we
-- avoid read some interfaces files unnecessary.
translation :: FilePath → ER ([AF], [(AF, [AF])])
translation file = do
  lift $ reportS "" 1 $ "Translating " ++ file ++ " ..."

  iModulesPaths ← liftIO $ getImportedModules file

  generalRolesImportedFiles ← mapM translationGeneralRoles iModulesPaths
  generalRolesCurrentFile   ← translationGeneralRoles file

  -- Gettting the interface.
  i ← liftIO $ myReadInterface file

  -- We translate the ATP pragma conjectures and their local hints
  -- in the current module.
  conjectures ← conjecturesToAFs i

  return ( concat generalRolesImportedFiles ++ generalRolesCurrentFile
         , conjectures
         )

runAgda2ATP :: String → ErrorT String IO ()
runAgda2ATP prgName = do
  argv ← liftIO getArgs

  -- Reading the command line options.
  (opts, name) ← processOptions argv prgName

  when (optVersion opts) $ liftIO $
       bye $ prgName ++ " version " ++ version ++ "\n"

  when (optHelp opts) $ liftIO $ bye $ usage prgName

  r  ← liftIO $ runReaderT (runErrorT (translation name)) opts
  case r of
    Right (generalRoles , conjecturesCurrentModule) → do
        r' ← liftIO $
                runReaderT (runErrorT (callATP generalRoles
                                               conjecturesCurrentModule))
                           opts
        case r' of
          Right _   → return ()
          Left err' → throwError err'

    Left err → throwError err

main :: IO ()
main = do
  prgName ← liftIO getProgName

  r ← runErrorT $ runAgda2ATP prgName `catchError` \err → do
         liftIO $ putStrLn $ prgName ++ ": " ++ err
         throwError err
  case r of
    Right _ → exitSuccess
    Left _  → exitFailure
  `catchImpossible` \e → do
         putStr $ show e
         exitFailure
