{-# LANGUAGE CPP #-}

------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

module TPTP.Files where

-- Haskell imports
import Control.Monad
import Data.Map ( Map )
import qualified Data.Map as Map
import System.FilePath

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import Common.Types ( PostulateName )
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
    "% This file corresponds to the ATP pragmas axioms.\n\n"

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

addAxiom :: PostulateName -> AnnotatedFormula -> IO ()
addAxiom pName af@(AF  _ AxiomTPTP _ ) = do
  appendFile axiomsFile ("% The Agda axiom name was " ++ show pName ++ ".\n")
  appendFile axiomsFile (show af)
addAxiom _ _  = __IMPOSSIBLE__

addHint :: AnnotatedFormula -> FilePath -> IO ()
addHint af@(AF  _ AxiomTPTP _ ) file = appendFile file (show af)
addHint _                       _    = __IMPOSSIBLE__

createAxiomsFile :: Map PostulateName AnnotatedFormula -> IO ()
createAxiomsFile axioms = do
  _ <- writeFile axiomsFile headerAxioms
  _ <- zipWithM_ addAxiom (Map.keys axioms) (Map.elems axioms)
  _ <- appendFile axiomsFile footerAxioms
  return ()

createConjectureFile :: (AnnotatedFormula, [AnnotatedFormula]) -> IO ()
createConjectureFile (af@(AF name ConjectureTPTP _ ), hints) = do
  let file = addExtension ("/tmp/" ++ name) extTPTP
  _ <- writeFile file headerConjecture
  _ <- mapM_ (flip addHint file) hints
  _ <- appendFile file (show af)
  _ <- appendFile file footerConjecture
  return ()
createConjectureFile _ = __IMPOSSIBLE__
