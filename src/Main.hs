{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( liftM2 )
import Control.Monad.Error ( catchError, throwError )
import Control.Monad.State ( modify )
import Control.Monad.Trans ( liftIO )

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
import AgdaLib.Interface ( getImportedInterfaces, myReadInterface )
import ATP               ( callATPs )
import Monad.Base
    ( AllDefinitions
    , runT
    , T
    , TState(tAllDefs, tOpts)
    )
import Monad.Options     ( processOptions )
import Monad.Reports     ( reportS )
import Options           ( Options(optHelp, optVersion) , printUsage )
import TPTP.Translation  ( conjecturesToAFs, generalRolesToAFs )
import TPTP.Types        ( ConjectureAFs, GeneralRolesAF )
import Utils.Version     ( printVersion )

#include "undefined.h"

------------------------------------------------------------------------------

translation ∷ FilePath → T (GeneralRolesAF, [ConjectureAFs])
translation file = do
  reportS "" 1 $ "Translating " ++ file ++ " ..."

  -- Gettting the interface.
  i ← myReadInterface file

  iInterfaces ← getImportedInterfaces i

  let topLevelDefs ∷ Definitions
      topLevelDefs = sigDefinitions $ iSignature i

  let importedDefs ∷ [Definitions]
      importedDefs = map (sigDefinitions . iSignature) iInterfaces

  let allDefs ∷ AllDefinitions
      allDefs = Map.unions (topLevelDefs : importedDefs)

  -- We add allDefs to the state
  modify $ \s → s { tAllDefs = allDefs }

  liftM2 (,) generalRolesToAFs (conjecturesToAFs topLevelDefs)

-- | The main function.
runAgda2ATP ∷ String → T ()
runAgda2ATP prgName = do
  argv ← liftIO getArgs

  clo ← processOptions argv
  case clo of
    (opts, file)
        | optHelp opts    → liftIO $ printUsage prgName
        | optVersion opts → liftIO $ printVersion prgName
        | otherwise       → do
            modify $ \s → s { tOpts = opts }

            -- The ATP pragmas are translated to TPTP annotated formulas.
            allAFs ← translation file
            -- The ATPs systems are called on the TPTP annotated formulas.
            mapM_ (callATPs (fst allAFs)) (snd allAFs)

main ∷ IO ()
main = do
  prgName ← getProgName

  -- Adapted from Agda.Main.main.
  (r ∷ Either String ()) ← runT $ runAgda2ATP prgName `catchError` \err →
    do liftIO $ hPutStrLn stderr $ prgName ++ ": " ++ err
       throwError err

  case r of
    Right _ → exitSuccess
    Left  _ → exitFailure
  `catchImpossible` \e → do
    putStr $ show e
    exitFailure
