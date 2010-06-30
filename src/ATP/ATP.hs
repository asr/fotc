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

-- ATPs
data ATPs = Equinox | Eprover
            deriving Eq

instance Show ATPs where
    show Equinox = "equinox"
    show Eprover = "eprover"

-- Equinox cvs version
equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

-- Eprover version E 1.1-004 Balasun
eproverOk :: String
eproverOk = "Proof found!"

checkOutputATP :: ATPs -> String -> Bool
checkOutputATP atp output = isInfixOf (atpOk atp) output
       where
         atpOk :: ATPs -> String
         atpOk Equinox = equinoxOk
         atpOk Eprover = eproverOk

runATP :: MVar (Bool, ATPs) -> MVar () -> FilePath -> String ->
          ATPs -> IO ()
runATP outputMVar synMVar file timeLimit atp = do

  -- Because Equinox and Eprover prove more or less the same theorems,
  -- we wait 1 sec. before launch the Eprover's theread.
  when ( atp == Eprover ) $ threadDelay 1000000

  let args :: [String]
      args = case atp of
               Equinox -> [ "--time", timeLimit, file ]
               Eprover -> [ "--tstp-format"
                          , "--soft-cpu-limit=" ++ timeLimit
                          , file
                          ]

  output <- readProcess (show atp) args ""

  putMVar synMVar ()
  putMVar outputMVar (checkOutputATP atp output, atp)

callATPConjecture :: (AF, [AF]) -> ER ()
callATPConjecture conjecture = do
  opts <- lift ask

  file <- lift $ createConjectureFile conjecture

  unless (optOnlyCreateFiles opts) $ do

    let timeLimit :: String
        timeLimit = show $ optTime opts

    outputMVar <- liftIO (newEmptyMVar :: IO (MVar (Bool, ATPs)))
    synMVar    <- liftIO (newEmptyMVar :: IO (MVar ()))

    lift $ reportS "" 1 $ "Proving the conjecture " ++ file ++ " ..."

    equinoxThread <- liftIO $
      forkIO (runATP outputMVar synMVar file timeLimit Equinox )
    eproverThread <- liftIO $
      forkIO (runATP outputMVar synMVar file timeLimit Eprover )

    fstOutput <- liftIO $ takeMVar outputMVar
    case fstOutput of
      (True, fstATP) -> do
        lift $ reportS "" 1 $ show fstATP ++ " proved the conjecture " ++ file
        -- The other atp's theread must be sleeping, so we can kill it.
        case fstATP of
          Equinox -> liftIO $ killThread eproverThread
          Eprover -> liftIO $ killThread equinoxThread

      (False, fstATP) -> do
          -- Wake up the other atp's theread
          _       <- liftIO $ takeMVar synMVar

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
