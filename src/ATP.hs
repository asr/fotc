-----------------------------------------------------------------------------
-- |
-- Module      : ATP
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Call the ATPs.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP ( callATPs ) where

-- Haskell imports
import Control.Exception       ( evaluate )
import Control.Concurrent      ( forkIO, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad           ( when )
import Control.Monad.Error     ( throwError )
import Control.Monad.Trans     ( liftIO )
import Data.List               ( isInfixOf )
import Data.Maybe              ( fromMaybe )
import Data.Functor            ( (<$>) )
import System.Directory        ( findExecutable )
import System.IO               ( hGetContents )
import System.Process
  ( createProcess
  , proc
  , ProcessHandle
  , readProcess
  , StdStream(CreatePipe)
  , std_out
  , terminateProcess
  )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(Impossible) , throwImpossible )
import Agda.Utils.Monad      ( ifM )

-- Local imports
import Monad.Base    ( getTOpts, T )
import Monad.Reports ( reportS )

import Options ( Options(optATP, optTime, optUnprovedError, optVampireExec) )

#include "undefined.h"

------------------------------------------------------------------------------
-- The ATPs.
data ATP = E
         | Equinox
         | IleanCoP
         | Metis
         | SPASS
         | Vampire
           deriving (Eq, Show)

atpExec ∷ ATP → T String
atpExec E        = return "eprover"
atpExec Equinox  = return "equinox"
atpExec IleanCoP = return "ileancop.sh"
atpExec Metis    = return "metis"
atpExec SPASS    = return "SPASS"
atpExec Vampire  = optVampireExec <$> getTOpts

optATP2ATP ∷ String → T ATP
optATP2ATP "e"        = return E
optATP2ATP "equinox"  = return Equinox
optATP2ATP "ileancop" = return IleanCoP
optATP2ATP "metis"    = return Metis
optATP2ATP "spass"    = return SPASS
optATP2ATP "vampire"  = return Vampire
optATP2ATP nonATP     = throwError $ "ATP " ++ nonATP ++ " unknown"

atpOk ∷ ATP → String
atpOk E        = "Proof found!"                      -- E 1.4 Nanring
atpOk Equinox  = "+++ RESULT: Theorem"               -- Equinox 5.0alpha (2010-06-29)
atpOk IleanCoP = "Intuitionistic Theorem"            -- ileanCoP 1.3 beta1
atpOk Metis    = "SZS status Theorem"                -- Metis 2.3 (release 20110926)
atpOk SPASS    = "Proof found"                       -- SPASS 3.7
atpOk Vampire  = "Termination reason: Refutation\n"  -- Vampire 0.6 (revision 903)

atpVersion ∷ ATP → T String
atpVersion Equinox = return $ show Equinox -- Don't version option in Equinox.
atpVersion SPASS   = return $ show SPASS   -- Don't version option in SPASS.
-- Didn't tested with IleanCop.
atpVersion atp = do
  exec ← atpExec atp
  liftIO $ fmap init (readProcess exec ["--version"] "")

checkOutput ∷ ATP → String → Bool
checkOutput atp output = atpOk atp `isInfixOf` output

-- Equinox bug? The option --no-progress don't make any difference.
atpArgs ∷ ATP → Int → FilePath → [String]
atpArgs E        timeLimit file = [ "--cpu-limit=" ++ show timeLimit
                                  , "-m" ++ "Auto"
                                  , "-l" ++ "0"
                                  , "-x" ++ "Auto"
                                  , "-t" ++ "Auto"
                                  , "--tstp-format"
                                  , file
                                  ]
atpArgs Equinox  timeLimit file = [ "--no-progress"
                                  , "--time", show timeLimit
                                  , file
                                  ]
-- N.B. The order of the IleanCop arguments is fixed.
atpArgs IleanCoP timeLimit file = [ file
                                  , show timeLimit
                                  ]
atpArgs Metis    timeLimit file = [ "--time-limit", show timeLimit
                                  , file
                                  ]
atpArgs SPASS    timeLimit file = [ "-TPTP"
                                  , "-TimeLimit=" ++ show timeLimit
                                  , file
                                  ]

atpArgs Vampire  timeLimit file = [ "--input_file", file
                                  , "-t", show timeLimit
                                  ]

runATP ∷ ATP → MVar (Bool, ATP) → Int → FilePath → T ProcessHandle
runATP atp outputMVar timeLimit file = do

  let args ∷ [String]
      args = atpArgs atp timeLimit file

  exec ∷ String ← atpExec atp

  e ← liftIO $ findExecutable exec
  case e of
    Nothing → reportS "" 1 $ "Warning: We could not find the command " ++ exec
                             ++ " associated to the ATP " ++ show atp
    Just _  → return ()

  -- To create the ATPs process we follow the ideas used by
  -- System.Process.readProcess.

  (_, outputH, _, atpPH) ← liftIO $
    createProcess (proc exec args) { std_out = CreatePipe }

  output ← liftIO $ hGetContents $ fromMaybe (__IMPOSSIBLE__) outputH
  _      ← liftIO $ forkIO $
             evaluate (length output) >>
             putMVar outputMVar (checkOutput atp output, atp)

  return atpPH

atpsAnswer ∷ MVar (Bool, ATP) → [ProcessHandle] → FilePath → Int → T ()
atpsAnswer outputMVar atpsPH file n = do

  atps ∷ [String] ← optATP <$> getTOpts

  if n == length atps
    then do
      let msg ∷ String
          msg = "The ATP(s) did not prove the conjecture in " ++ file
      ifM (optUnprovedError <$> getTOpts)
          (throwError msg)
          (liftIO $ putStrLn msg)
    else do
      output ← liftIO $ takeMVar outputMVar
      atpWithVersion ← atpVersion (snd output)
      if fst output
        then do
          reportS "" 1 $ atpWithVersion ++ " proved the conjecture in " ++ file
          liftIO $ do
            -- It seems that terminateProcess is a nop if the process
            -- is finished, therefore we don't care on terminate all
            -- the ATPs processes.

            -- TODO: Ugly hack. Using the thread delay and repeating
            -- the terminateProcess instruction was the way to kill
            -- the Vampire process.
            mapM_ terminateProcess atpsPH
            threadDelay 500000
            mapM_ terminateProcess atpsPH
        else do
          reportS "" 1 $ atpWithVersion ++ " *did not* prove the conjecture"
          atpsAnswer outputMVar atpsPH file (n + 1)

-- | The function 'callATPs' calls the selected ATPs on a TPTP conjecture.
callATPs ∷ FilePath → T ()
callATPs file = do

  atps ∷ [String] ← optATP <$> getTOpts

  when (null atps) (__IMPOSSIBLE__)

  timeLimit ∷ Int ← optTime <$> getTOpts

  outputMVar ← liftIO (newEmptyMVar ∷ IO (MVar (Bool, ATP)))

  reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."
  reportS "" 20 $ "ATPs to be used: " ++ show atps

  atpsPH ∷ [ProcessHandle] ←
    mapM optATP2ATP atps >>= mapM (\atp → runATP atp outputMVar timeLimit file)

  atpsAnswer outputMVar atpsPH file 0
