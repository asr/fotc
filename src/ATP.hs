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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP
  ( ATP(..)  -- Required to avoid an Haddock warning.
  , callATPs
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Exception       ( evaluate )
import Control.Concurrent      ( forkIO, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad(fail) )
#endif
import Control.Monad ( mapM, mapM_, Monad((>>), (>>=), return) )

import Control.Monad.Error     ( MonadError(throwError) )
import Control.Monad.Trans     ( MonadIO(liftIO) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Bool     ( Bool )
import Data.Eq       ( Eq((==), (/=)) )
import Data.Int      ( Int )
import Data.List     ( (++), init, isInfixOf, length, null, takeWhile )
import Data.Function ( ($), (.) )
import Data.Functor  ( fmap )
import Data.Maybe    ( fromMaybe, Maybe(Just, Nothing) )
import Data.Tuple    ( fst, snd )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif
import GHC.Num ( Num((+)) )

import System.Directory ( findExecutable )
import System.IO        ( FilePath, hGetContents, IO, putStrLn )

import System.Process
  ( createProcess
  , CreateProcess(std_out)
  , proc
  , ProcessHandle
  , readProcess
  , StdStream(CreatePipe)
  , terminateProcess
  )

import Text.Show ( Show(show) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( Impossible(Impossible) , throwImpossible )
import Agda.Utils.Monad      ( ifM )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base    ( getTOpt, T )
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
atpExec Vampire  = getTOpt optVampireExec

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
atpOk E        = "Proof found!"                      -- E 1.5 Pussimbing
atpOk Equinox  = "+++ RESULT: Theorem"               -- Equinox 5.0alpha (2010-06-29)
atpOk IleanCoP = "Intuitionistic Theorem"            -- ileanCoP 1.3 beta1
atpOk Metis    = "SZS status Theorem"                -- Metis 2.3 (release 20110926)
atpOk SPASS    = "Proof found"                       -- SPASS 3.7
atpOk Vampire  = "Termination reason: Refutation\n"  -- Vampire 0.6 (revision 903)

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

atpArgs ∷ ATP → Int → FilePath → [String]
atpArgs E timeLimit file = [ "--cpu-limit=" ++ show timeLimit
                           , "--expert-heuristic=Auto"
                           , "--memory-limit=Auto"
                           , "--output-level=0"
                           , "--term-ordering=Auto"
                           , "--tstp-format"
                           , file
                           ]

-- Equinox bug? The option @--no-progress@ doesn't make any difference.
atpArgs Equinox timeLimit file = [ "--no-progress"
                                 , "--time", show timeLimit
                                 , file
                                 ]

-- N.B. The order of the IleanCop arguments is fixed.
atpArgs IleanCoP timeLimit file = [ file
                                  , show timeLimit
                                  ]

atpArgs Metis timeLimit file = [ "--time-limit", show timeLimit
                               , file
                               ]

atpArgs SPASS timeLimit file = [ "-TPTP"
                               , "-TimeLimit=" ++ show timeLimit
                               , file
                               ]

atpArgs Vampire timeLimit file = [ "--input_file", file
                                 , "-t", show timeLimit
                                 ]

runATP ∷ ATP → MVar (Bool, ATP) → Int → FilePath → T ProcessHandle
runATP atp outputMVar timeLimit file = do
  let args ∷ [String]
      args = atpArgs atp timeLimit file

  exec ∷ String ← atpExec atp

  e ← liftIO $ findExecutable exec
  case e of
    Nothing → throwError $
              "We could not find the command " ++ exec
              ++ " associated to the ATP " ++ show atp
              ++ ". Maybe you should use the flag --atp=NAME "
              ++ "to avoid calling the defaults ATPs"
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

atpsAnswer ∷ [String] → MVar (Bool, ATP) → [ProcessHandle] → FilePath → Int →
             T ()
atpsAnswer atps outputMVar atpsPH file n =
  if n == length atps
    then do
      let msg ∷ String
          msg = "The ATP(s) did not prove the conjecture in " ++ file
      ifM (getTOpt optUnprovedNoError)
          (liftIO $ putStrLn msg)
          (throwError msg)
    else do
      output ← liftIO $ takeMVar outputMVar
      atpWithVersion ← atpVersion (snd output)
      if fst output
        then do
          reportS "" 1 $ atpWithVersion ++ " proved the conjecture in " ++ file
          liftIO $ do
            -- It seems that @terminateProcess@ is a nop if the process
            -- is finished, therefore we don't care on terminate all
            -- the ATPs processes.
            mapM_ terminateProcess atpsPH

            -- TODO: Ugly hack. Using the thread delay and repeating
            -- the @terminateProcess@ instruction was the way to kill
            -- the Vampire process.
            --
            -- 2012-01-13: Using the new field @create_group ∷ Bool@ for
            -- the datatype @CreateProcess@ in System.Process-1.1.0.0,
            -- it is possible to use the function
            -- @interruptProcessGroupOf@ to kill the process, however
            -- some ATPs continued running after using this
            -- function. See
            -- http://thread.gmane.org/gmane.comp.lang.haskell.cafe/95473/.
            threadDelay 500000
            mapM_ terminateProcess atpsPH
        else do
          reportS "" 1 $ atpWithVersion ++ " *did not* prove the conjecture"
          atpsAnswer atps outputMVar atpsPH file (n + 1)

-- | The function 'callATPs' calls the selected 'ATP's on a TPTP conjecture.
callATPs ∷ FilePath → T ()
callATPs file = do
  atpsAux    ← getTOpt optATP
  timeLimit  ← getTOpt optTime
  outputMVar ← liftIO (newEmptyMVar ∷ IO (MVar (Bool, ATP)))

  let atps ∷ [String]
      atps = if null atpsAux then defaultATPs else atpsAux

  reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."
  reportS "" 20 $ "ATPs to be used: " ++ show atps

  atpsPH ∷ [ProcessHandle] ←
    mapM optATP2ATP atps >>= mapM (\atp → runATP atp outputMVar timeLimit file)

  atpsAnswer atps outputMVar atpsPH file 0
