
-----------------------------------------------------------------------------
-- Call the ATPs
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP ( callATPs ) where

-- Haskell imports
import Data.List               ( isInfixOf )
import Data.Maybe              ( fromMaybe )
import Control.Exception       ( evaluate )
import Control.Concurrent      ( forkIO, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad           ( when )
import Control.Monad.Error     ( throwError )
import Control.Monad.State     ( get )
import Control.Monad.Trans     ( liftIO )
import System.IO               ( hGetContents )
import System.Process
  ( createProcess
  , proc
  , ProcessHandle
  , StdStream(CreatePipe)
  , std_out
  , terminateProcess
  )
-- import System.Timeout ( timeout )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(Impossible) , throwImpossible )

-- Local imports
import Monad.Base    ( T, TState(tOpts) )
import Monad.Reports ( reportS )
import Options       ( Options(optATP, optTime, optUnprovedError) )

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

-- The vampire executables are vampire_lin32, vampire_lin64,
-- vampire_mac, and vampire_win.exe, therefore I use the generic
-- name "vampire".
atp2exec ∷ ATP → String
atp2exec E        = "eprover"
atp2exec Equinox  = "equinox"
atp2exec IleanCoP = "ileancop.sh"
atp2exec Metis    = "metis"
atp2exec SPASS    = "SPASS"
atp2exec Vampire  = "vampire"

optATP2ATP ∷ String → T ATP
optATP2ATP "e"        = return E
optATP2ATP "equinox"  = return Equinox
optATP2ATP "ileancop" = return IleanCoP
optATP2ATP "metis"    = return Metis
optATP2ATP "spass"    = return SPASS
optATP2ATP "vampire"  = return Vampire
optATP2ATP nonATP     = throwError $ "ATP " ++ nonATP ++ " unknown"

-- Tested with E 1.4 Nanring.
eOk ∷ String
eOk = "Proof found!"

-- Tested with Equinox 5.0alpha (2010-06-29).
equinoxOk ∷ String
equinoxOk = "+++ RESULT: Theorem"

-- Tested with Metis 2.3 (release 20110531).
metisOk ∷ String
metisOk = "SZS status Theorem"

-- Tested with ileanCoP 1.3 beta1.
ileancopOk ∷ String
ileancopOk = "Intuitionistic Theorem"

-- Tested with SPASS 3.7.
spassOk ∷ String
spassOk = "Proof found"

-- Tested with Vampire 0.6 (revision 903).
vampireOk ∷ String
vampireOk = "Termination reason: Refutation\n"

checkAtpOutput ∷ ATP → String → Bool
checkAtpOutput atp output = atpOk atp `isInfixOf` output
  where
    atpOk ∷ ATP → String
    atpOk E        = eOk
    atpOk Equinox  = equinoxOk
    atpOk IleanCoP = ileancopOk
    atpOk Metis    = metisOk
    atpOk SPASS    = spassOk
    atpOk Vampire  = vampireOk

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

  -- To create the ATPs process we follow the ideas used by
  -- System.Process.readProcess.

  (_, outputH, _, atpPH) ← liftIO $
    createProcess (proc (atp2exec atp) args) { std_out = CreatePipe }

  output ← liftIO $ hGetContents $ fromMaybe (__IMPOSSIBLE__) outputH
  _      ← liftIO $ forkIO $
             evaluate (length output) >>
             putMVar outputMVar (checkAtpOutput atp output, atp)

  return atpPH

atpsAnswer ∷ MVar (Bool, ATP) → [ProcessHandle] → FilePath → Int → T ()
atpsAnswer outputMVar atpsPH file n = do

  state ← get

  let opts ∷ Options
      opts = tOpts state

      atps ∷ [String]
      atps = optATP opts

  if n == length atps
    then do
      let msg ∷ String
          msg = "The ATP(s) " ++ show atps ++
                " did not prove the conjecture in " ++ file
      if optUnprovedError opts
        then throwError msg
        else liftIO $ putStrLn msg
    else do
      output ← liftIO $ takeMVar outputMVar
      case output of
        (True, atp) → do
          reportS "" 1 $ show atp ++ " proved the conjecture in " ++ file
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

        (False, atp) → do
          reportS "" 1 $ show atp ++ " *did not* prove the conjecture"
          atpsAnswer outputMVar atpsPH file (n + 1)

-- | The function 'callATPs' calls the selected ATPs on a TPTP conjecture.
callATPs ∷ FilePath → T ()
callATPs file = do

  state ← get

  let opts ∷ Options
      opts = tOpts state

      atps ∷ [String]
      atps = optATP opts

  when (null atps) (__IMPOSSIBLE__)

  let timeLimit ∷ Int
      timeLimit = optTime opts

  outputMVar ← liftIO (newEmptyMVar ∷ IO (MVar (Bool, ATP)))

  reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."
  reportS "" 20 $ "ATPs to be used: " ++ show atps

  (atpsPH ∷ [ProcessHandle]) ←
    mapM optATP2ATP atps >>= mapM (\atp → runATP atp outputMVar timeLimit file)

  atpsAnswer outputMVar atpsPH file 0
