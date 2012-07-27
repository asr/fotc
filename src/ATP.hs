-----------------------------------------------------------------------------
-- |
-- Module      : ATP
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Call the automatic theorem provers (ATPs).
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP
  ( ATP(..)  -- Required to avoid an Haddock warning.
  , callATPs
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Exception       ( evaluate )
import Control.Concurrent      ( forkIO, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad           ( when )
import Control.Monad.Error     ( MonadError(throwError) )
import Control.Monad.Trans     ( MonadIO(liftIO) )

import Data.List  ( isInfixOf )
import Data.Maybe ( fromMaybe, isNothing )

import System.Directory ( findExecutable )
import System.IO        ( hGetContents )

import System.Process
  ( createProcess
  , CreateProcess(std_out)
  , proc
  , ProcessHandle
  , readProcess
  , StdStream(CreatePipe)
  , terminateProcess
  )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( Impossible(Impossible) , throwImpossible )
import Agda.Utils.Monad      ( ifM )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base    ( askTOpt, T )
import Monad.Reports ( reportS )

import Options ( Options(optATP, optTime, optUnprovedNoError, optVampireExec) )

#include "undefined.h"

------------------------------------------------------------------------------
-- | The ATPs.
data ATP = E
         | Equinox
         | IleanCoP
         | Metis
         | SPASS
         | Vampire
           deriving Show

atpExec ∷ ATP → T String
atpExec E        = return "eprover"
atpExec Equinox  = return "equinox"
atpExec IleanCoP = return "ileancop.sh"
atpExec Metis    = return "metis"
atpExec SPASS    = return "SPASS"
atpExec Vampire  = askTOpt optVampireExec

optATP2ATP ∷ String → T ATP
optATP2ATP "e"        = return E
optATP2ATP "equinox"  = return Equinox
optATP2ATP "ileancop" = return IleanCoP
optATP2ATP "metis"    = return Metis
optATP2ATP "spass"    = return SPASS
optATP2ATP "vampire"  = return Vampire
optATP2ATP nonATP     = throwError $ "ATP " ++ nonATP ++ " unknown"

-- | Default ATPs.
defaultATPs ∷ [String]
defaultATPs = ["e", "equinox", "vampire"]

atpOk ∷ ATP → String
-- E 1.2, E 1.3, E 1.4, E 1.5, and E 1.6.
atpOk E = "Proof found!"
-- Equinox 5.0alpha (2010-06-29).
atpOk Equinox = "+++ RESULT: Theorem"
-- ileanCoP 1.3 beta1.
atpOk IleanCoP = "Intuitionistic Theorem"
-- Metis 2.3 (release 20110926).
atpOk Metis = "SZS status Theorem"
-- SPASS 3.7.
atpOk SPASS = "Proof found"
-- Vampire 0.6 (revision 903).
atpOk Vampire = "Termination reason: Refutation\n"

atpVersion ∷ ATP → T String
 -- Don't version option in Equinox.
atpVersion Equinox = do
  exec ← atpExec Equinox
  liftIO $ fmap (init . takeWhile (/= '\n')) (readProcess exec ["--help"] "")
-- Don't version option in SPASS.
atpVersion SPASS = return $ show SPASS
-- Didn't tested with IleanCop.
atpVersion atp = do
  exec ← atpExec atp
  liftIO $ fmap init (readProcess exec ["--version"] "")

checkOutput ∷ ATP → String → Bool
checkOutput atp output = atpOk atp `isInfixOf` output

atpArgs ∷ ATP → Int → FilePath → T [String]
atpArgs E timeLimit file = do
  eVersion ← atpVersion E
  if eVersion `elem` [ "E 1.2 Badamtam"
                     , "E 1.3 Ringtong"
                     , "E 1.4 Namring"
                     , "E 1.5 Pussimbing"
                     ]
    then return [ "--cpu-limit=" ++ show timeLimit
                , "--expert-heuristic=Auto"
                , "--memory-limit=Auto"
                , "--output-level=0"
                , "--term-ordering=Auto"
                , "--tstp-format"
                , file
                ]
    else
      if eVersion == "E 1.6 Tiger Hill"
        then return [ "--auto"
                    , "--cpu-limit=" ++ show timeLimit
                    , "--memory-limit=Auto"
                    , "--output-level=0"
                    , "--tstp-format"
                    , file
                    ]
        -- This message is not included in the error test.
        else throwError $ "The ATP " ++ eVersion ++ " is not supported"

-- Equinox bug. Neither the option @--no-progress@ nor the option
-- @--verbose 0@ reduce the output.
atpArgs Equinox timeLimit file = return [ "--time", show timeLimit
                                        , file
                                        ]

-- N.B. The order of the IleanCop arguments is fixed.
atpArgs IleanCoP timeLimit file = return [ file
                                         , show timeLimit
                                         ]

atpArgs Metis timeLimit file = return [ "--time-limit", show timeLimit
                                      , file
                                      ]

atpArgs SPASS timeLimit file = return [ "-PProblem=0"
                                      , "-PStatistic=0"
                                      , "-TimeLimit=" ++ show timeLimit
                                      , "-TPTP"
                                      , file
                                      ]

-- 25 July 2012. We don't know if vampire has an option to reduce the
-- output.
atpArgs Vampire timeLimit file = return [ "--input_file", file
                                        , "--mode", "casc"
                                        , "-t", show timeLimit
                                        ]

runATP ∷ ATP → MVar (Bool, ATP) → Int → FilePath → T ProcessHandle
runATP atp outputMVar timeLimit file = do
  args ∷ [String] ← atpArgs atp timeLimit file
  exec ∷ String   ← atpExec atp

  e ← liftIO $ findExecutable exec
  when (isNothing e) $ throwError $
    "The command " ++ exec ++ " associated with " ++ show atp
    ++ " does not exist.\nYou can use the command-line option --atp=NAME "
    ++ "to avoid call the defaults ATPs"

  -- To create the ATPs process we follow the ideas used by
  -- System.Process.readProcess.
  (_, outputH, _, atpPH) ← liftIO $
    createProcess (proc exec args) { std_out = CreatePipe }

  output ← liftIO $ hGetContents $ fromMaybe (__IMPOSSIBLE__) outputH
  _      ← liftIO $ forkIO $
             evaluate (length output) >>
             putMVar outputMVar (checkOutput atp output, atp)

  return atpPH

atpsAnswer ∷ [String] → MVar (Bool, ATP) → [ProcessHandle] → FilePath → Int →
             T ()
atpsAnswer atps outputMVar atpsPH file n =
  if n == length atps
    then do
      let msg ∷ String
          msg = "The ATP(s) did not prove the conjecture in " ++ file
      ifM (askTOpt optUnprovedNoError)
          (liftIO $ putStrLn msg)
          (throwError msg)
    else do
      output ← liftIO $ takeMVar outputMVar
      atpWithVersion ← atpVersion (snd output)
      if fst output
        then do
          reportS "" 1 $ atpWithVersion ++ " proved the conjecture in " ++ file
          liftIO $ do
            -- See note [All terminate].
            mapM_ terminateProcess atpsPH
            -- See note [Vampire termination].
            threadDelay 500000
            mapM_ terminateProcess atpsPH
        else do
          reportS "" 1 $ atpWithVersion ++ " *did not* prove the conjecture"
          atpsAnswer atps outputMVar atpsPH file (n + 1)

-- | The function 'callATPs' calls the selected 'ATP's on a TPTP conjecture.
callATPs ∷ FilePath → T ()
callATPs file = do
  atpsAux       ← askTOpt optATP
  timeLimitAux  ← askTOpt optTime
  outputMVar    ← liftIO (newEmptyMVar ∷ IO (MVar (Bool, ATP)))

  let atps ∷ [String]
      atps = if null atpsAux then defaultATPs else atpsAux

  reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."
  reportS "" 20 $ "ATPs to be used: " ++ show atps

  -- See note [Timeout increse].
  let timeLimit ∷ Int
      timeLimit = round (fromIntegral timeLimitAux * (1.1 ∷ Float))

  atpsPH ∷ [ProcessHandle] ←
    mapM optATP2ATP atps >>= mapM (\atp → runATP atp outputMVar timeLimit file)

  atpsAnswer atps outputMVar atpsPH file 0

------------------------------------------------------------------------------
-- Note [All terminate]

-- It seems that @terminateProcess@ is a nop if the process is
-- finished, therefore we don't care on terminate all the ATPs
-- processes.

------------------------------------------------------------------------------
-- Note [Timeout increse]

-- 12 June 2012: Hack. Running for example
--
-- @$ equinox --time 216 conjecture.tptp@
--
-- or
--
-- @$ agda2atp --time=216 --atp=equinox conjecture.agda@
--
-- it is possible prove the theorem. But running for example
--
-- @$ agda2atp --time=216 --atp=equinox --atp=vampire --atp=e conjecture.agda@
--
-- doesn't prove the theorem. I guess there is some overhead for
-- calling various ATPs from the program agda2atp. Therefore we
-- increase internally 10% the ATPs timeout.

------------------------------------------------------------------------------
-- Note [Vampire termination]

-- TODO: Ugly hack. Using the thread delay and repeating the
-- @terminateProcess@ instruction was the way to kill the Vampire
-- process.
--
-- 2012-01-13: Using the new field @create_group ∷ Bool@ for the
-- datatype @CreateProcess@ in System.Process-1.1.0.0, it is possible
-- to use the function @interruptProcessGroupOf@ to kill the process,
-- however some ATPs continued running after using this function. See
-- http://thread.gmane.org/gmane.comp.lang.haskell.cafe/95473/.
