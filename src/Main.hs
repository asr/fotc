{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( liftM2, when )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error
    ( catchError
    , ErrorT
    , runErrorT
    , throwError
    )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT )

import qualified Data.Map as Map ( unions )

import System.Environment ( getArgs, getProgName)
import System.Exit ( exitFailure, exitSuccess )
import System.IO ( hPutStrLn, stderr )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.TypeChecking.Monad.Base
    ( Definitions
    , Interface(iSignature)
    , Signature(sigDefinitions)
    )
import Agda.Utils.Impossible
    ( catchImpossible
--    , Impossible(Impossible)
--    , throwImpossible
    )

------------------------------------------------------------------------------
-- Local imports

-- import FOL.Pretty
import AgdaLib.Interface
    ( getImportedInterfaces
    , myReadInterface
    )
import ATP.ATP ( callATP )
import Common ( AllDefinitions, ER )
import Options
    ( Options(optHelp, optVersion)
    , processOptions
    , usage
    )
import Reports ( reportS )
import TPTP.Translation ( conjecturesToAFs, generalRolesToAFs )
import TPTP.Types ( AF )
import Utils.IO ( bye )
import Utils.Version ( version )

#include "undefined.h"

------------------------------------------------------------------------------

translation :: FilePath → ER ([AF], [(AF, [AF])])
translation file = do
  lift $ reportS "" 1 $ "Translating " ++ file ++ " ..."

  -- Gettting the interface.
  i ← myReadInterface file

  iInterfaces ← getImportedInterfaces i

  let topLevelDefs :: Definitions
      topLevelDefs = sigDefinitions $ iSignature i

  let importedDefs :: [Definitions]
      importedDefs = map (sigDefinitions . iSignature) iInterfaces

  let allDefs :: AllDefinitions
      allDefs = Map.unions (topLevelDefs : importedDefs)

  -- TODO: topLevelDefs ⊆ allDefs.
  liftM2 (,) (generalRolesToAFs allDefs)
             (conjecturesToAFs allDefs topLevelDefs)

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
         liftIO $ hPutStrLn stderr $ prgName ++ ": " ++ err
         throwError err
  case r of
    Right _ → exitSuccess
    Left  _ → exitFailure
  `catchImpossible` \e → do
         putStr $ show e
         exitFailure
