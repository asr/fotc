-----------------------------------------------------------------------------
-- Call the ATPs
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module ATP.ATP ( callATP ) where

-- Haskell imports
import Data.List ( isInfixOf )
import Control.Concurrent ( forkIO, killThread, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad ( unless )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( throwError )
import Control.Monad.Trans.Reader ( ask )
-- import GHC.Conc ( threadStatus )
import System.Process ( readProcess )
-- import System.Timeout ( timeout )

-- Agda library imports
-- import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

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

runATP :: MVar (Bool, ATP) → FilePath → Int → ATP → IO ()
runATP outputMVar file timeLimit atp = do

  let args :: [String]
      args = case atp of
               Equinox → [ "--time", show timeLimit, file ]
               Eprover → [ "--tstp-format"
                          , "--soft-cpu-limit=" ++ show timeLimit
                          , file
                          ]
               Metis   → [ "--tptp", "/", file ]

  -- Hack. Because metis does not have a time control, we wrap the
  -- calls to the ATPs inside a timeout. This timeout only should be
  -- used to kill metis, therefore we added 3 secs to allow that
  -- equinox and eprover use their internal timeout.

  -- TODO: There is an problem with the function timeout and eprover
  -- output ← timeout (timeLimit * 1000000 + 3000000) (readProcess (show atp) args "")


  output ← readProcess (nameATP atp) args ""
  putMVar outputMVar (checkOutputATP atp output, atp)

callATPConjecture :: (AF, [AF]) → ER ()
callATPConjecture conjecture = do
  opts ← lift ask

  file ← lift $ createConjectureFile conjecture

  unless (optOnlyFiles opts) $ do

    let timeLimit :: Int
        timeLimit = optTime opts

    outputMVar ← liftIO (newEmptyMVar :: IO (MVar (Bool, ATP)))

    lift $ reportS "" 1 $ "Proving the conjecture in " ++ file ++ " ..."

    equinoxThread ← liftIO $
      forkIO (runATP outputMVar file timeLimit Equinox)

    -- Because Equinox and Eprover prove more or less the same theorems,
    -- we wait 1 sec. before launch the Eprover's thread.
    eproverThread ← liftIO $
      forkIO (threadDelay 1000000 >>
              runATP outputMVar file timeLimit Eprover)

    -- Because Equinox and Eprover prove almost all the theorems, we
    -- wait 2 sec. before launch the Metis's thread.
    -- when ( atp == Metis ) $ threadDelay 2000000

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
                                 -- e1 ← threadStatus equinoxThread
                                 -- e2 ← threadStatus eproverThread
                                 -- print e1
                                 -- print e2
                                 killThread eproverThread
                                 killThread equinoxThread
                 (False, _ ) → answerATPs (n + 1)

    answerATPs 0

callATP :: [AF] → [(AF, [AF])] → ER ()
callATP generalRoles conjectures = do
  -- We create the general axioms/hints/definitions TPTP file.
  lift $ createGeneralRolesFile generalRoles

  -- We create the particular conjectures TPTP files.
  mapM_ callATPConjecture conjectures
