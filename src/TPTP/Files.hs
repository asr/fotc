------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TPTP.Files where

-- Haskell imports
import Data.Char ( chr, ord )
import System.FilePath

-- Agda library imports
import Agda.Syntax.Common ( RoleATP(..) )
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import TPTP.Pretty
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------

class ValidFileName a where
    validFileName :: a -> FilePath

instance ValidFileName Char where
    validFileName c
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr ((ord c) - 8272)]
        | otherwise                   = [c]

-- Requires TypeSynonymInstances
instance ValidFileName String where
    validFileName s = concat $ map validFileName s

extTPTP :: String
extTPTP = ".tptp"

axiomsAndHintsFile :: FilePath
axiomsAndHintsFile = addExtension "/tmp/axioms" extTPTP

communHeader :: String
communHeader =
    "%-----------------------------------------------------------------------------\n" ++
    "% This file was generated automatically.\n" ++
    "%-----------------------------------------------------------------------------\n\n"

headerAxiomsAndHints :: String
headerAxiomsAndHints =
    communHeader ++
    "% This file corresponds to the ATP axioms and general hints.\n\n"

footerAxiomsAndHints :: String
footerAxiomsAndHints  =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP axioms and general hints.\n"

headerConjecture :: String
headerConjecture =
    communHeader ++
    "% This file corresponds to an ATP pragma conjecture and its hints.\n\n" ++
    "% We include the ATP pragmas axioms file.\n" ++
    "include('" ++ axiomsAndHintsFile ++ "').\n\n"

footerConjecture :: String
footerConjecture =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP pragma conjecture.\n"

addAxiom :: AnnotatedFormula -> FilePath -> IO ()
addAxiom af@(AF qName AxiomATP _ ) file = do
  appendFile file $ "% The original Agda axiom/hint name was " ++ show qName ++ ".\n"
  appendFile file (prettyTPTP af)
addAxiom _ _ = __IMPOSSIBLE__

addConjecture :: AnnotatedFormula -> FilePath -> IO ()
addConjecture af@(AF qName ConjectureATP _ ) file = do
  appendFile file $ "% The original Agda postulate name was " ++ show qName ++ ".\n"
  appendFile file (prettyTPTP af)
addConjecture _ _ = __IMPOSSIBLE__

createAxiomsAndHintsFile :: [AnnotatedFormula] -> IO ()
createAxiomsAndHintsFile afs = do
  _ <- writeFile axiomsAndHintsFile headerAxiomsAndHints
  _ <- mapM_ (flip addAxiom axiomsAndHintsFile) afs
  _ <- appendFile axiomsAndHintsFile footerAxiomsAndHints
  return ()

createConjectureFile :: (AnnotatedFormula, [AnnotatedFormula]) -> IO ()
createConjectureFile (af@(AF qName _ _ ), hints) = do
  let file = addExtension ("/tmp/" ++ (validFileName $ show qName)) extTPTP
  _ <- writeFile file headerConjecture
  _ <- mapM_ (flip addAxiom file) hints
  _ <- addConjecture af file
  _ <- appendFile file footerConjecture
  return ()
