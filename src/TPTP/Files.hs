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
import Agda.Syntax.Abstract.Name
    ( Name(nameBindingSite)
    , QName(qnameName)
    )
import Agda.Syntax.Common ( RoleATP(..) )
import Agda.Utils.Impossible ( Impossible(..) , throwImpossible )

-- Local imports
import MyAgda.Interface ( qNameLine )
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

agdaOriginalTerm :: QName -> String
agdaOriginalTerm qName =
    "% The original Agda term was\n" ++
    "% name:\t\t" ++ show qName ++ "\n" ++
    "% position:\t" ++
    (show $ nameBindingSite $ qnameName qName) ++ "\n"

addAxiom :: AnnotatedFormula -> FilePath -> IO ()
addAxiom af@(AF qName AxiomATP _ ) file = do
  appendFile file $ agdaOriginalTerm qName
  appendFile file $ prettyTPTP af
addAxiom _ _ = __IMPOSSIBLE__

addConjecture :: AnnotatedFormula -> FilePath -> IO ()
addConjecture af@(AF qName ConjectureATP _ ) file = do
  appendFile file $ agdaOriginalTerm qName
  appendFile file $ prettyTPTP af
addConjecture _ _ = __IMPOSSIBLE__

createAxiomsAndHintsFile :: [AnnotatedFormula] -> IO ()
createAxiomsAndHintsFile afs = do
  _ <- writeFile axiomsAndHintsFile headerAxiomsAndHints
  _ <- mapM_ (flip addAxiom axiomsAndHintsFile) afs
  _ <- appendFile axiomsAndHintsFile footerAxiomsAndHints
  return ()

createConjectureFile :: (AnnotatedFormula, [AnnotatedFormula]) -> IO ()
createConjectureFile (af@(AF qName _ _ ), hints) = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.
  let f = "/tmp/" ++
          (validFileName $ show qName) ++ "_" ++ (show $ qNameLine qName)
  let file = addExtension f extTPTP
  _ <- writeFile file headerConjecture
  _ <- mapM_ (flip addAxiom file) hints
  _ <- addConjecture af file
  _ <- appendFile file footerConjecture
  return ()
