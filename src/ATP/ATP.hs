-----------------------------------------------------------------------------
-- Call the ATP
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module ATP.ATP where

-- Haskell imports
import Data.List ( isInfixOf )
import Control.Monad ( unless )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( throwError )
import Control.Monad.Trans.Reader ( ask )
import System.Process ( readProcess )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import Common ( ER )
import Options ( Options(optATP, optOnlyCreateFiles, optTime) )
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
checkOutputATP atp output =
    if (isInfixOf (atpOk atp) output) then True else False
       where
         atpOk :: String -> String
         atpOk "equinox" = equinoxOk
         atpOk "eprover" = eproverOk
         atpOk _         = __IMPOSSIBLE__

callATPConjecture :: (AF, [AF]) -> ER ()
callATPConjecture conjecture = do
  opts <- lift ask

  file <- lift $ createConjectureFile conjecture

  unless (optOnlyCreateFiles opts) $ do
    let atp :: String
        atp = optATP opts

    let timeLimit :: String
        timeLimit = show $ optTime opts

    lift $ reportS "" 1 $ "Proving the conjecture " ++ file ++ " ..."

    output <- case atp of
      "equinox" -> lift $ liftIO $
                   readProcess atp [ "--time" , timeLimit , file ] ""

      "eprover" -> lift $ liftIO $
                   readProcess atp [ "--tstp-format"
                                   , "--cpu-limit=" ++ timeLimit
                                   , file
                                   ] ""

      _         -> throwError
                   "At the moment, the possible ATPs are equinox or eprover."

    if (checkOutputATP atp output)
     then return ()
     else throwError $ atp ++ " did not prove the conjecture " ++ file ++ "."

callATP :: [AF] -> [(AF, [AF])] -> ER ()
callATP axioms conjectures = do
  -- We create the general axioms TPTP file.
  lift $ createAxiomsFile axioms

  -- We create the conjectures TPTP files
  mapM_ callATPConjecture conjectures
