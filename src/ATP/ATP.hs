-----------------------------------------------------------------------------
-- Call the ATPs
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP.ATP ( callATP ) where

-- Haskell imports
import Data.List ( isInfixOf )
import Data.Maybe ( fromMaybe )
import Control.Exception ( evaluate )
import Control.Concurrent ( forkIO )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad ( unless, when )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( throwError )
import Control.Monad.Trans.Reader ( ask )
import System.IO ( hGetContents )
import System.Process
    ( createProcess
    , proc
    , StdStream(CreatePipe)
    , std_out
    , terminateProcess
    )
-- import System.Timeout ( timeout )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import Common ( ER )
import Options ( Options(optOnlyFiles, optTime) )
import Reports ( reportS )
import TPTP.Files ( createGeneralRolesFile, createConjectureFile )
import TPTP.Types ( AF )

#include "../undefined.h"

-----------------------------------------------------------------------------

-- The ATPs.
data ATP = Equinox | Eprover | Metis
           deriving (Eq, Show)

nameATP :: ATP → String
nameATP Equinox = "equinox"
nameATP Eprover = "eprover"
nameATP Metis   = "metis"

-- Tested with Equinox cvs version.
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Tested with Eprover version E 1.1-004 Balasun.
eproverOk :: String
eproverOk = "Proof found!"

-- Tested with Metis version 2.2 (release 20100524).
metisOk :: String
metisOk = "SZS status Theorem"

checkOutputATP :: ATP → String → Bool
checkOutputATP atp output = isInfixOf (atpOk atp) output
       where
         atpOk :: ATP → String
         atpOk Equinox = equinoxOk
         atpOk Eprover = eproverOk
         atpOk Metis   = metisOk

argsATP :: ATP → Int → FilePath → [String]
argsATP Equinox timeLimit file = [ "--time", show timeLimit, file ]
argsATP Eprover timeLimit file = [ "--tstp-format"
                                 , "--soft-cpu-limit=" ++ show timeLimit
                                 , file
                                 ]
argsATP Metis   _         file = [ "--tptp", "/", file ]

callATPConjecture :: (AF, [AF]) → ER ()
callATPConjecture conjecture = do
  opts ← lift ask

  file ← lift $ createConjectureFile conjecture

  when (optOnlyFiles opts) $
    lift $ reportS "" 1 $ "Created the conjecture file " ++ file

  unless (optOnlyFiles opts) $ do

    let timeLimit :: Int
        timeLimit = optTime opts

    outputMVar ← liftIO (newEmptyMVar :: IO (MVar (Bool, ATP)))

    lift $ reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."

    -- To create the ATPs process we follow the ideas used by
    -- System.Process.readProcess.

    -- Equinox process
    (_, equinoxOH, _, equinoxPH) ← liftIO $
       createProcess (proc (nameATP Equinox) (argsATP Equinox timeLimit file))
                     { std_out = CreatePipe }

    equinoxOutput ← liftIO $ hGetContents $ fromMaybe __IMPOSSIBLE__ equinoxOH
    _ <- liftIO $ forkIO $
           evaluate (length equinoxOutput) >>
           putMVar outputMVar (checkOutputATP Equinox equinoxOutput, Equinox)

    -- Eprover process
    (_, eproverOH, _, eproverPH) ← liftIO $
       createProcess (proc (nameATP Eprover) (argsATP Eprover timeLimit file))
                     { std_out = CreatePipe }

    eproverOutput ← liftIO $ hGetContents $ fromMaybe __IMPOSSIBLE__ eproverOH
    _ <- liftIO $ forkIO $
           evaluate (length eproverOutput) >>
           putMVar outputMVar (checkOutputATP Eprover eproverOutput, Eprover)

    let answerATPs :: Int → ER ()
        answerATPs n =
          if n == 2
             then throwError $ "The ATPs did not prove the conjecture in " ++
                               file ++ "."
             else do
               output ← liftIO $ takeMVar outputMVar
               case output of
                 (True, atp) →
                     do lift $ reportS "" 1 $ show atp ++
                                              " proved the conjecture in " ++
                                              file
                        liftIO $ do
                        -- It seems that terminateProcess is a nop if
                        -- the process is finished, therefore we don't care
                        -- on terminate all the ATPs processes.
                        terminateProcess equinoxPH
                        terminateProcess eproverPH
                 (False, _ ) → answerATPs (n + 1)

    answerATPs 0

callATP :: [AF] → [(AF, [AF])] → ER ()
callATP generalRoles conjectures = do
  -- We create the general axioms/hints/definitions TPTP file.
  lift $ createGeneralRolesFile generalRoles

  -- We create the particular conjectures TPTP files.
  mapM_ callATPConjecture conjectures
