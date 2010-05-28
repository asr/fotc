------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TPTP.Files where

-- Haskell imports
import Control.Monad.IO.Class ( liftIO )
import Data.Char ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
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
import Reports ( R, reportSLn )
import TPTP.Types

#include "../undefined.h"

------------------------------------------------------------------------------

class ValidFileName a where
    validFileName :: a -> FilePath

instance ValidFileName Char where
    validFileName c
        | c `elem` ['.', '_', '-'] = [c]
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr (ord c - 8272)]
        | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
        | otherwise = show $ ord c

-- Requires TypeSynonymInstances
instance ValidFileName String where
    validFileName s = concat $ map validFileName s

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
    "% This file corresponds to the ATP axioms, general hints, and definitions.\n\n"

footerAxioms :: String
footerAxioms  =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP axioms file.\n"

headerConjecture :: String
headerConjecture =
    communHeader ++
    "% This file corresponds to an ATP conjecture and its hints.\n\n" ++
    "% We include the ATP pragmas axioms file.\n" ++
    "include('" ++ axiomsFile ++ "').\n\n"

footerConjecture :: String
footerConjecture =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP conjecture file.\n"

agdaOriginalTerm :: QName -> RoleATP -> String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% name:\t\t" ++ show qName ++ "\n" ++
    "% role:\t\t" ++ show role ++ "\n" ++
    "% position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addAxiom :: AF -> FilePath -> IO ()
addAxiom af@(AF qName role _ ) file
  | role == AxiomATP ||
    role == DefinitionATP ||
    role == HintATP =
        do
          appendFile file $ agdaOriginalTerm qName role
          appendFile file $ prettyTPTP af

  | otherwise = __IMPOSSIBLE__

addConjecture :: AF -> FilePath -> R ()
addConjecture af file = do
  case af of
    (AF qName ConjectureATP _ ) -> do
          liftIO $ appendFile file $ agdaOriginalTerm qName ConjectureATP
          liftIO $ appendFile file $ prettyTPTP af

    _ -> __IMPOSSIBLE__

createAxiomsFile :: [AF] -> R ()
createAxiomsFile afs = do
  reportSLn "createAxiomsFile" 20 $ "Creating the general axioms file ... "
  liftIO $ do
    _ <- writeFile axiomsFile headerAxioms
    _ <- mapM_ (flip addAxiom axiomsFile) afs
    _ <- appendFile axiomsFile footerAxioms
    return ()

createConjectureFile :: (AF, [AF]) -> R FilePath
createConjectureFile (af@(AF qName _ _ ), hints) = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.
  let f = "/tmp/" ++
          validFileName (show qName) ++ "_" ++ show (qNameLine qName)
  let file = addExtension f extTPTP
  reportSLn "createConjectureFile" 20 $
                "Creating the conjecture file " ++ show file ++ " ..."
  liftIO $ do
    _ <- writeFile file headerConjecture
    _ <- mapM_ (flip addAxiom file) hints
    return ()

  addConjecture af file
  liftIO $ appendFile file footerConjecture
  return file