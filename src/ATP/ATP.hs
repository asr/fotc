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
import Control.Monad.Error ( throwError )
import Control.Monad.Reader ( ask )
import Control.Monad.Trans ( liftIO )
import System.IO ( hGetContents )
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
import Common ( T )
import Options ( Options(optATP, optOnlyFiles, optTime, optUnprovedError) )
import Reports ( reportS )
import TPTP.Files ( createGeneralRolesFile, createConjectureFile )
import TPTP.Types ( AF )

#include "../undefined.h"

-----------------------------------------------------------------------------
-- The ATPs.
data ATP = E
         | Equinox
         | IleanCoP
         | Metis
           deriving (Eq, Show)

atp2exec :: ATP → String
atp2exec E        = "eprover"
atp2exec Equinox  = "equinox"
atp2exec IleanCoP = "ileancop.sh"
atp2exec Metis    = "metis"

string2ATP :: String → ATP
string2ATP "e"        = E
string2ATP "equinox"  = Equinox
string2ATP "ileancop" = IleanCoP
string2ATP "metis"    = Metis
string2ATP _          = __IMPOSSIBLE__

-- Tested with E 1.2 Badamtam.
eOk :: String
eOk = "Proof found!"

-- Tested with Equinox 5.0alpha (2010-03-29).
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Tested with Metis 2.3 (release 20101019).
metisOk :: String
metisOk = "SZS status Theorem"

-- Tested with ileanCoP 1.3 beta1.
ileancopOk :: String
ileancopOk = "Intuitionistic Theorem"

checkOutputATP :: ATP → String → Bool
checkOutputATP atp output = atpOk atp `isInfixOf` output
    where
      atpOk :: ATP → String
      atpOk E        = eOk
      atpOk Equinox  = equinoxOk
      atpOk IleanCoP = ileancopOk
      atpOk Metis    = metisOk

argsATP :: ATP → Int → FilePath → [String]
argsATP E        timeLimit file = [ "--tstp-format"
                                  , "--soft-cpu-limit=" ++ show timeLimit
                                  , file
                                  ]
argsATP Equinox  timeLimit file = [ "--time", show timeLimit, file ]
argsATP IleanCoP timeLimit file = [ file, show timeLimit ]
argsATP Metis    timeLimit file = [ "--time-limit", show timeLimit
                                  , file
                                  ]

runATP :: ATP → MVar (Bool, ATP) → [String] → IO ProcessHandle
runATP atp outputMVar args = do

    -- To create the ATPs process we follow the ideas used by
    -- System.Process.readProcess.

    (_, outputH, _, atpPH) ←
      createProcess (proc (atp2exec atp) args)
                    { std_out = CreatePipe }

    output ← hGetContents $ fromMaybe __IMPOSSIBLE__ outputH
    _ <- forkIO $
           evaluate (length output) >>
           putMVar outputMVar (checkOutputATP atp output, atp)

    return atpPH

callATPConjecture :: (AF, [AF]) → T ()
callATPConjecture conjecture = do
  (_, opts) ← ask

  file ← createConjectureFile conjecture

  when (optOnlyFiles opts) $
    reportS "" 1 $ "Created the conjecture file " ++ file

  unless (optOnlyFiles opts) $ do

    let atps :: [String]
        atps = optATP opts

    when (null atps) __IMPOSSIBLE__

    let timeLimit :: Int
        timeLimit = optTime opts

    outputMVar ← liftIO (newEmptyMVar :: IO (MVar (Bool, ATP)))

    reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."
    reportS "" 20 $ "ATPs to be used: " ++ show atps

    atpsPH ← liftIO $
           mapM ((\atp → runATP atp outputMVar (argsATP atp timeLimit file)) .
                 string2ATP)
                atps

    let answerATPs :: Int → T ()
        answerATPs n =
          if n == length atps
             then do
               let msg :: String
                   msg = "The ATP(s) " ++ show atps ++
                         " did not prove the conjecture in " ++ file
               if optUnprovedError opts
                 then throwError msg
                 else reportS "" 1 msg
             else do
               output ← liftIO $ takeMVar outputMVar
               case output of
                 (True, atp) →
                     do reportS "" 1 $ show atp ++
                          " proved the conjecture in " ++ file
                        liftIO $
                           -- It seems that terminateProcess is a nop if
                           -- the process is finished, therefore we don't care
                           -- on terminate all the ATPs processes.
                           mapM_ terminateProcess atpsPH
                 (False, _ ) → answerATPs (n + 1)

    answerATPs 0

callATP :: [AF] → [(AF, [AF])] → T ()
callATP generalRoles conjectures = do
  -- We create the general axioms/hints/definitions TPTP file.
  createGeneralRolesFile generalRoles

  -- We create the particular conjectures TPTP files.
  mapM_ callATPConjecture conjectures
