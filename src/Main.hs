{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad        ( liftM2 )
import Control.Monad.Error  ( catchError , throwError )
import Control.Monad.Reader ( ask, local )
import Control.Monad.Trans  ( liftIO )

import qualified Data.Map as Map ( unions )

import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import System.IO          ( hPutStrLn, stderr )

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
import AgdaLib.Interface ( getImportedInterfaces , myReadInterface )
import ATP.ATP           ( callATP )
import Common            ( AllDefinitions, runT, T, TEnv )
import Options           ( Options(optHelp, optVersion) , printUsage )
import Options.Process   ( processOptions )
import Reports           ( reportS )
import TPTP.Translation  ( conjecturesToAFs, generalRolesToAFs )
import TPTP.Types        ( AF )
import Utils.Version     ( printVersion )

#include "undefined.h"

------------------------------------------------------------------------------

translation :: T ([AF], [(AF, [AF])])
translation = do
  (_, _, file) ← ask
  reportS "" 1 $ "Translating " ++ file ++ " ..."

  -- Gettting the interface.
  i ← myReadInterface file

  iInterfaces ← getImportedInterfaces i

  let topLevelDefs :: Definitions
      topLevelDefs = sigDefinitions $ iSignature i

  let importedDefs :: [Definitions]
      importedDefs = map (sigDefinitions . iSignature) iInterfaces

  let allDefs :: AllDefinitions
      allDefs = Map.unions (topLevelDefs : importedDefs)

  -- We add allDefs to the environment.
  let changeTEnv :: TEnv → TEnv
      changeTEnv (_, opts, f) = (allDefs, opts, f)

  liftM2 (,)
         (local changeTEnv generalRolesToAFs)
         (local changeTEnv $ conjecturesToAFs topLevelDefs)

-- | The main function.
runAgda2ATP :: String → T ()
runAgda2ATP prgName = do
  argv ← liftIO getArgs

  clo ← processOptions argv
  case clo of
    (opts, file)
        | optHelp opts    → liftIO $ printUsage prgName
        | optVersion opts → liftIO $ printVersion prgName
        | otherwise       → do
            let changeTEnv :: TEnv → TEnv
                changeTEnv (defs, _, _) = (defs, opts, file)

            -- The ATP pragmas are translated to TPTP annotated formulas.
            allAFs ← local changeTEnv translation
            -- The ATPs systems are called on the TPTP annotated formulas.
            local changeTEnv $ uncurry callATP allAFs

main :: IO ()
main = do
  prgName ← getProgName

  -- Adapted from Agda.Main.main.
  r ← runT $ runAgda2ATP prgName `catchError` \err → do
             liftIO $ hPutStrLn stderr $ prgName ++ ": " ++ err
             throwError err

  case r of
    Right _ → exitSuccess
    Left  _ → exitFailure
  `catchImpossible` \e → do
    putStr $ show e
    exitFailure
