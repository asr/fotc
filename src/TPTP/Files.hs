------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

module TPTP.Files where

-- Local imports
import TPTP.Types

axiomsFile :: String
axiomsFile = "/tmp/externalAxioms.tptp"

headerAxioms :: String
headerAxioms =
  "%-----------------------------------------------------------------------------\n" ++
  "% This file was generated automatically.\n" ++
  "%-----------------------------------------------------------------------------\n\n" ++
  "% This file corresponds to the EXTERNAL axioms.\n\n"

footerAxioms :: String
footerAxioms =
  "\n" ++
  "%-----------------------------------------------------------------------------\n" ++
  "% End EXTERNAL axioms.\n"

addLinesTPTP :: [LineTPTP] -> IO ()
addLinesTPTP [] = return ()
addLinesTPTP (line@(MkLineTPTP  _ AxiomTPTP _ ) : xs) =
    appendFile axiomsFile (show line) >> addLinesTPTP xs
addLinesTPTP (MkLineTPTP  _ ConjectureTPTP _  : xs) = addLinesTPTP xs

createFilesTPTP :: [LineTPTP] -> IO ()
createFilesTPTP linesTPTP = do
  _ <- writeFile axiomsFile headerAxioms
  _ <- addLinesTPTP linesTPTP
  _ <- appendFile axiomsFile footerAxioms
  return ()
