-----------------------------------------------------------------------------
-- Call the ATP
-----------------------------------------------------------------------------

module ATP.ATP where

-- Haskell imports
import Data.List ( isInfixOf )
import Control.Monad ( unless )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Reader ( ask )
import System.Process ( readProcess )

-- Local imports
import Options ( Options(optATP, optOnlyCreateFiles, optTime) )
import Reports ( R, reportS )
import TPTP.Files ( createAxiomsFile, createConjectureFile )
import TPTP.Types ( AF )

-----------------------------------------------------------------------------

equinoxOk :: String
equinoxOk = "+++ RESULT: Theorem"

checkOutputATP :: String -> String -> Bool
checkOutputATP atp output =
    if (isInfixOf (atpOk atp) output) then True else False
       where
         atpOk :: String -> String
         atpOk "equinox" = equinoxOk
         atpOk _         = error "The possible ATP are: equinox"

callATPConjecture :: (AF, [AF]) -> R ()
callATPConjecture conjecture = do
  opts <- ask

  file <- createConjectureFile conjecture

  unless (optOnlyCreateFiles opts) $ do
    let atp :: String
        atp = optATP opts

    reportS "" 1 $ "Proving the conjecture " ++ file
    output <- liftIO $
              readProcess atp ["--time", show $ optTime opts , file] ""
    if (checkOutputATP atp output)
      then return ()
      else error $ atp ++ " did not prove the conjecture " ++ file

callATP :: [AF] -> [(AF, [AF])] -> R ()
callATP axioms conjectures = do
  -- We create the general axioms TPTP file.
  createAxiomsFile axioms

  -- We create the conjectures TPTP files
  mapM_ callATPConjecture conjectures
