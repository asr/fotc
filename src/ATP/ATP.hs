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
    , ProcessHandle
    , StdStream(CreatePipe)
    , std_out
    , terminateProcess
    )
-- import System.Timeout ( timeout )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import Common ( ER )
import Options ( Options(optATP, optOnlyFiles, optTime, optUnprovedError) )
import Reports ( reportS )
import TPTP.Files ( createGeneralRolesFile, createConjectureFile )
import TPTP.Types ( AF )

#include "../undefined.h"

-----------------------------------------------------------------------------
-- The ATPs.
data ATP = Eprover | Equinox | IleanCoP | Metis
           deriving (Eq, Show)

atp2exec :: ATP → String
atp2exec Eprover  = "eprover"
atp2exec Equinox  = "equinox"
atp2exec IleanCoP = "ileancop.sh"
atp2exec Metis    = "metis"

string2ATP :: String → ATP
string2ATP "eprover"  = Eprover
string2ATP "equinox"  = Equinox
string2ATP "ileancop" = IleanCoP
string2ATP "metis"    = Metis
string2ATP _          = __IMPOSSIBLE__

-- Tested with Eprover E 1.2 Badamtam.
eproverOk :: String
eproverOk = "Proof found!"

-- Tested with Equinox 5.0alpha (2010-03-29).
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Tested with Metis 2.3 (release 20100920).
metisOk :: String
metisOk = "SZS status Theorem"

-- Tested with ileanCoP 1.3 beta1.
ileancopOk :: String
ileancopOk = "Intuitionistic Theorem"

checkOutputATP :: ATP → String → Bool
checkOutputATP atp output = isInfixOf (atpOk atp) output
    where
      atpOk :: ATP → String
      atpOk Eprover  = eproverOk
      atpOk Equinox  = equinoxOk
      atpOk IleanCoP = ileancopOk
      atpOk Metis    = metisOk

argsATP :: ATP → Int → FilePath → [String]
argsATP Eprover  timeLimit file = [ "--tstp-format"
                                  , "--soft-cpu-limit=" ++ show timeLimit
                                  , file
                                  ]
argsATP Equinox  timeLimit file = [ "--time", show timeLimit, file ]
argsATP IleanCoP timeLimit file = [ file, show timeLimit ]
argsATP Metis   _          file = [ "--tptp", "/", file ]

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

callATPConjecture :: (AF, [AF]) → ER ()
callATPConjecture conjecture = do
  opts ← lift ask

  file ← lift $ createConjectureFile conjecture

  when (optOnlyFiles opts) $
    lift $ reportS "" 1 $ "Created the conjecture file " ++ file

  unless (optOnlyFiles opts) $ do

    let atps :: [String]
        atps = optATP opts

    when (null atps) __IMPOSSIBLE__

    let timeLimit :: Int
        timeLimit = optTime opts

    outputMVar ← liftIO (newEmptyMVar :: IO (MVar (Bool, ATP)))

    lift $ reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."

    atpsPH ← liftIO $
           mapM ((\atp → runATP atp outputMVar (argsATP atp timeLimit file)) .
                 string2ATP)
                atps

    let answerATPs :: Int → ER ()
        answerATPs n =
          if n == length atps
             then do
               let msg :: String
                   msg = "The ATP(s) " ++ show atps ++
                         " did not prove the conjecture in " ++ file
               if (optUnprovedError opts)
                 then throwError msg
                 else lift $ reportS "" 1 msg
             else do
               output ← liftIO $ takeMVar outputMVar
               case output of
                 (True, atp) →
                     do lift $ reportS "" 1 $ show atp ++
                                              " proved the conjecture in " ++
                                              file
                        liftIO $
                           -- It seems that terminateProcess is a nop if
                           -- the process is finished, therefore we don't care
                           -- on terminate all the ATPs processes.
                           mapM_ terminateProcess atpsPH
                 (False, _ ) → answerATPs (n + 1)

    answerATPs 0

callATP :: [AF] → [(AF, [AF])] → ER ()
callATP generalRoles conjectures = do
  -- We create the general axioms/hints/definitions TPTP file.
  lift $ createGeneralRolesFile generalRoles

  -- We create the particular conjectures TPTP files.
  mapM_ callATPConjecture conjectures
