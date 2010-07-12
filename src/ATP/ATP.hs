-----------------------------------------------------------------------------
-- Call the ATPs
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module ATP.ATP where

-- Haskell imports
import Data.List ( isInfixOf )
import Control.Concurrent ( forkIO, killThread, threadDelay )
import Control.Concurrent.MVar ( MVar, newEmptyMVar, putMVar, takeMVar )
import Control.Monad ( unless, when )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( throwError )
import Control.Monad.Trans.Reader ( ask )
import System.Process ( readProcess )
-- import System.Timeout ( timeout )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import Common ( ER )
import Options ( Options(optOnlyCreateFiles, optTime) )
import Reports ( reportS )
import TPTP.Files ( createAxiomsFile, createConjectureFile )
import TPTP.Types ( AF )

#include "../undefined.h"

-----------------------------------------------------------------------------

-- The ATPs.
data ATPs = Equinox | Eprover | Metis
            deriving Eq

instance Show ATPs where
    show Equinox = "equinox"
    show Eprover = "eprover"
    show Metis   = "metis"

-- Tested with Equinox cvs version.
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Tested with Eprover version E 1.1-004 Balasun.
eproverOk :: String
eproverOk = "Proof found!"

-- Tested with Metis version 2.2 (release 20100524).
metisOk :: String
metisOk = "SZS status Theorem"

checkOutputATP :: ATPs -> String -> Bool
checkOutputATP atp output = isInfixOf (atpOk atp) output
       where
         atpOk :: ATPs -> String
         atpOk Equinox = equinoxOk
         atpOk Eprover = eproverOk
         atpOk Metis   = metisOk

runATP :: MVar (Bool, ATPs) -> MVar () -> FilePath -> Int ->
          ATPs -> IO ()
runATP outputMVar syncMVar file timeLimit atp = do

  -- Because Equinox and Eprover prove more or less the same theorems,
  -- we wait 1 sec. before launch the Eprover's theread.
  when ( atp == Eprover ) $ threadDelay 1000000

  -- Because Equinox and Eprover prove almost all the theorems, we
  -- wait 2 sec. before launch the metis's theread.
  when ( atp == Metis ) $ threadDelay 2000000

  let args :: [String]
      args = case atp of
               Equinox -> [ "--time", show timeLimit, file ]
               Eprover -> [ "--tstp-format"
                          , "--soft-cpu-limit=" ++ show timeLimit
                          , file
                          ]
               Metis   -> [ "--tptp", "/", file ]


  -- Hack. Because metis does not have a time control, we wrap the
  -- calls to the ATPs inside a timeout. This timeout only should be
  -- used to kill metis, therefore we added 3 secs to allow that
  -- equinox and eprover use their internal timeout.

  -- TODO: There is an problem with the function timeout and eprover
  -- output <- timeout (timeLimit * 1000000 + 3000000) (readProcess (show atp) args "")

  -- putMVar syncMVar ()
  -- case output of
  --   Nothing -> putMVar outputMVar (False, atp)
  --   Just o  -> putMVar outputMVar (checkOutputATP atp o, atp)

  output <- readProcess (show atp) args ""
  putMVar syncMVar ()
  putMVar outputMVar (checkOutputATP atp output, atp)

callATPConjecture :: (AF, [AF]) -> ER ()
callATPConjecture conjecture = do
  opts <- lift ask

  file <- lift $ createConjectureFile conjecture

  unless (optOnlyCreateFiles opts) $ do

    let timeLimit :: Int
        timeLimit = optTime opts

    outputMVar <- liftIO (newEmptyMVar :: IO (MVar (Bool, ATPs)))
    syncMVar   <- liftIO (newEmptyMVar :: IO (MVar ()))

    lift $ reportS "" 1 $ "Proving the conjecture " ++ file ++ " ..."

    equinoxThread <- liftIO $
      forkIO (runATP outputMVar syncMVar file timeLimit Equinox )
    eproverThread <- liftIO $
      forkIO (runATP outputMVar syncMVar file timeLimit Eprover )

    fstOutput <- liftIO $ takeMVar outputMVar
    case fstOutput of
      (True, fstATP) -> do
        lift $ reportS "" 1 $ show fstATP ++ " proved the conjecture " ++ file
        -- The other atp's theread must be sleeping, so we can kill it.
        case fstATP of
          Equinox -> liftIO $ killThread eproverThread
          Eprover -> liftIO $ killThread equinoxThread
          _       -> __IMPOSSIBLE__

      (False, fstATP) -> do
          -- Wake up the other atp's theread
          _       <- liftIO $ takeMVar syncMVar

          sndOutput <- liftIO $ takeMVar outputMVar
          case sndOutput of
             (b, sndATP ) -> do
               when ( fstATP == sndATP ) __IMPOSSIBLE__
               case b of
                 True -> lift $ reportS "" 1 $
                                show sndATP ++ " proved the conjecture " ++
                                     file

                 False -> throwError $
                            "The ATPs did not prove the conjecture " ++
                            file ++ "."

callATP :: [AF] -> [(AF, [AF])] -> ER ()
callATP axioms conjectures = do
  -- We create the general axioms TPTP file.
  lift $ createAxiomsFile axioms

  -- We create the conjectures TPTP files.
  mapM_ callATPConjecture conjectures
