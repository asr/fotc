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

import Agda.Syntax.Abstract.Name ( ModuleName )
import Agda.TypeChecking.Monad.Base ( Interface(iModuleName) )
import Agda.Utils.Impossible
    ( catchImpossible
    , Impossible(Impossible)
    , throwImpossible
    )

------------------------------------------------------------------------------
-- Local imports

-- import FOL.Pretty
import ATP.ATP ( callATP )
import Common ( ER )
import MyAgda.Interface ( getImportedModules, myGetInterface, myReadInterface )
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
translationGeneralRoles :: ModuleName → ER [AF]
translationGeneralRoles x = do

  -- Getting the interface.
  im ← myGetInterface x

  let i :: Interface
      i = case im of
            Just interface → interface
            Nothing        → __IMPOSSIBLE__

  -- Getting the ATP axioms.
  axioms ← axiomsToAFs i

  -- Getting the ATP general hints.
  generalHints ← generalHintsToAFs i

  -- Getting the ATP definitions.
  fns ← fnsToAFs i

  return (axioms ++ generalHints ++ fns )

-- We could use the interfaces as the return of getImportedModules and
-- as argument of translationGeneralRoles, but it seems is cheaper
-- getting the interface again that pass them aorund.
translation :: FilePath → ER ([AF], [(AF, [AF])])
translation file = do
  lift $ reportS "" 1 $ "Translating " ++ file ++ " ..."

  -- Gettting the interface.
  i ← myReadInterface file

  let x :: ModuleName
      x = iModuleName i

  iModules ← getImportedModules x

  generalRolesImportedFiles ← mapM translationGeneralRoles iModules
  generalRolesCurrentFile   ← translationGeneralRoles x

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
  (opts, file) ← processOptions argv prgName

  when (optVersion opts) $ liftIO $
       bye $ prgName ++ " version " ++ version ++ "\n"

  when (optHelp opts) $ liftIO $ bye $ usage prgName

  r  ← liftIO $ runReaderT (runErrorT (translation file)) opts
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
