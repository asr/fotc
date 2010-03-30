------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

module TPTP.Files where

-- Haskell imports
import System.FilePath

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )
-- Local imports
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------
extTPTP :: String
extTPTP = ".tptp"

axiomsFile :: FilePath
axiomsFile = addExtension "/tmp/axioms" extTPTP

communHeader :: String
communHeader =
    "%-----------------------------------------------------------------------------\n" ++
    "% This file was generated automatically.\n" ++
    "%-----------------------------------------------------------------------------\n\n"

headerAxioms :: String
headerAxioms =
    communHeader ++
    "% This file corresponds to the ATP pragmas axioms.\n"

footerAxioms :: String
footerAxioms =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP pragmas axioms.\n"

headerTheorem :: String
headerTheorem =
    communHeader ++
    "% This file corresponds to an ATP pragma theorem.\n\n" ++
    "% We include the ATP pragmas axioms file.\n" ++
    "include('" ++ axiomsFile ++ "').\n\n"

footerTheorem :: String
footerTheorem =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP pragma theorem.\n"

addAxiom :: AnnotatedFormula -> FilePath -> IO ()
addAxiom af@(AF  _ AxiomTPTP _ ) file = appendFile file (show af)
addAxiom _                       _    = __IMPOSSIBLE__

createAxiomsFile :: [AnnotatedFormula] -> IO ()
createAxiomsFile afs = do
  _ <- writeFile axiomsFile headerAxioms
  _ <- mapM_ (flip addAxiom axiomsFile) afs
  _ <- appendFile axiomsFile footerAxioms
  return ()

createTheoremFile :: (AnnotatedFormula, [AnnotatedFormula]) -> IO ()
createTheoremFile (af@(AF name ConjectureTPTP _ ), hints) = do
  let file = addExtension ("/tmp/" ++ name) extTPTP
  _ <- writeFile file headerTheorem
  _ <- mapM_ (flip addAxiom file) hints
  _ <- appendFile file (show af)
  _ <- appendFile file footerTheorem
  return ()
createTheoremFile _ = __IMPOSSIBLE__
