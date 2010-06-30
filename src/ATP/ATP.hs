-----------------------------------------------------------------------------
-- Call the ATP
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

-- Equinox cvs version
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Eprover version E 1.1-004 Balasun
eproverOk :: String
eproverOk = "Proof found!"

checkOutputATP :: String -> String -> Bool
checkOutputATP atp output = isInfixOf (atpOk atp) output
       where
         atpOk :: String -> String
         atpOk "equinox" = equinoxOk
         atpOk "eprover" = eproverOk
         atpOk _         = __IMPOSSIBLE__

runATP :: MVar (Bool, String) -> MVar () -> FilePath -> String ->
          String -> IO ()
runATP outputMVar synMVar file timeLimit atp = do

  -- Because Equinox and Eprover prove more or less the same theorems,
  -- we wait 1 sec. before launch the Eprover's theread.
  when ( atp == "eprover" ) $ threadDelay 1000000

  let args :: [String]
      args = case atp of
               "equinox" -> [ "--time", timeLimit, file ]
               "eprover" -> [ "--tstp-format"
                            , "--soft-cpu-limit=" ++ timeLimit
                            , file
                            ]
               _         -> __IMPOSSIBLE__

  output <- readProcess atp args ""

  putMVar synMVar ()
  putMVar outputMVar (checkOutputATP atp output, atp)

callATPConjecture :: (AF, [AF]) -> ER ()
callATPConjecture conjecture = do
  opts <- lift ask

  file <- lift $ createConjectureFile conjecture

  unless (optOnlyCreateFiles opts) $ do

    let timeLimit :: String
        timeLimit = show $ optTime opts

    outputMVar <- liftIO (newEmptyMVar :: IO (MVar (Bool, String)))
    synMVar    <- liftIO (newEmptyMVar :: IO (MVar ()))

    lift $ reportS "" 1 $ "Proving the conjecture " ++ file ++ " ..."

    equinoxThread <- liftIO $
      forkIO (runATP outputMVar synMVar file timeLimit "equinox" )
    eproverThread <- liftIO $
      forkIO (runATP outputMVar synMVar file timeLimit "eprover" )

    output1 <- liftIO $ takeMVar outputMVar
    case output1 of
      (True, "equinox") -> do
        lift $ reportS "callATPConjecture" 10 "Equinox proved, eprover nothing"
        lift $ reportS "" 1 $ "Equinox proved the conjecture " ++ file
        -- The Eprover's theread must be sleeping, so we can kill it.
        liftIO $ killThread eproverThread

      (True, "eprover") -> do
        lift $ reportS "callATPConjecture" 10 "Eprover proved, eprover nothing"
        lift $ reportS "" 1 $ "Eprover proved the conjecture " ++ file
        -- The Equinox's theread must be sleeping, so we can kill it.
        liftIO $ killThread equinoxThread

      (False, "equinox" ) -> do
          -- We wake up the Eprover's theread
          _       <- liftIO $ takeMVar synMVar

          output2 <- liftIO $ takeMVar outputMVar
          case output2 of
             (True, "eprover") -> do
               lift $ reportS "callATPConjecture" 10
                      "Eprover proved, equinox did not prove"
               lift $ reportS "" 1 $ "Eprover proved the conjecture " ++ file
             (False, "eprover") ->
               throwError $ "Equinox and eprover" ++
                            " did not prove the conjecture " ++ file ++ "."
             _ -> __IMPOSSIBLE__

      (False, "eprover" ) -> do
          -- We wake up the Equinox's theread
          _       <- liftIO $ takeMVar synMVar

          output2 <- liftIO $ takeMVar outputMVar
          case output2 of
             (True, "equinox") -> do
               lift $ reportS "callATPConjecture" 10
                      "Equinox proved, eprover did not prove"
               lift $ reportS "" 1 $ "Equinox proved the conjecture " ++ file
             (False, "equinox") ->
               throwError $ "Equinox and eprover" ++
                            " did not prove the conjecture " ++ file ++ "."
             _ -> __IMPOSSIBLE__

      _ -> __IMPOSSIBLE__

callATP :: [AF] -> [(AF, [AF])] -> ER ()
callATP axioms conjectures = do
  -- We create the general axioms TPTP file.
  lift $ createAxiomsFile axioms

  -- We create the conjectures TPTP files
  mapM_ callATPConjecture conjectures
