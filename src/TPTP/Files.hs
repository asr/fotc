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

headerConjecture :: String
headerConjecture =
    communHeader ++
    "% This file corresponds to an ATP pragma conjecture and its hints.\n\n" ++
    "% We include the ATP pragmas axioms file.\n" ++
    "include('" ++ axiomsFile ++ "').\n\n"

footerConjecture :: String
footerConjecture =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP pragma conjecture.\n"

addAxiom :: AnnotatedFormula -> FilePath -> IO ()
addAxiom af@(AF  _ AxiomTPTP _ ) file = appendFile file (show af)
addAxiom _                       _    = __IMPOSSIBLE__

createAxiomsFile :: [AnnotatedFormula] -> IO ()
createAxiomsFile afs = do
  _ <- writeFile axiomsFile headerAxioms
  _ <- mapM_ (flip addAxiom axiomsFile) afs
  _ <- appendFile axiomsFile footerAxioms
  return ()

createConjectureFile :: (AnnotatedFormula, [AnnotatedFormula]) -> IO ()
createConjectureFile (af@(AF name ConjectureTPTP _ ), hints) = do
  let file = addExtension ("/tmp/" ++ name) extTPTP
  _ <- writeFile file headerConjecture
  _ <- mapM_ (flip addAxiom file) hints
  _ <- appendFile file (show af)
  _ <- appendFile file footerConjecture
  return ()
createConjectureFile _ = __IMPOSSIBLE__
