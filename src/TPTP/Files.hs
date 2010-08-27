------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Files
    ( createConjectureFile
    , createGeneralRolesFile
    ) where

-- Haskell imports
import Control.Monad.IO.Class ( liftIO )
import Data.Char ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import System.FilePath ( addExtension )

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
    validFileName :: a → FilePath

instance ValidFileName Char where
    validFileName c
        | c `elem` ['.', '_', '-'] = [c]
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr (ord c - 8272)]
        | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
        | otherwise = show $ ord c

-- Requires TypeSynonymInstances.
instance ValidFileName String where
    validFileName s = concat $ map validFileName s

extTPTP :: String
extTPTP = ".tptp"

outputDir :: String
outputDir = "/tmp/"

generalRolesFile :: FilePath
generalRolesFile = addExtension (outputDir ++ "general-roles") extTPTP

communHeader :: String
communHeader =
    "%-----------------------------------------------------------------------------\n" ++
    "% This file was generated automatically.\n" ++
    "%-----------------------------------------------------------------------------\n\n"

headerGeneralRoles :: String
headerGeneralRoles =
    communHeader ++
    "% This file corresponds to the ATP axioms, general hints, and definitions.\n\n"

footerGeneralRoles :: String
footerGeneralRoles  =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP axioms, general hints, and definitions file.\n"

headerConjecture :: String
headerConjecture =
    communHeader ++
    "% This file corresponds to an ATP conjecture and its hints.\n\n" ++
    "% We include the general ATP pragmas (axioms, hints and definitions).\n" ++
    "include('" ++ generalRolesFile ++ "').\n\n"

footerConjecture :: String
footerConjecture =
    "%-----------------------------------------------------------------------------\n" ++
    "% End ATP conjecture file.\n"

agdaOriginalTerm :: QName → RoleATP → String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% name:\t\t" ++ show qName ++ "\n" ++
    "% role:\t\t" ++ show role ++ "\n" ++
    "% position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addGeneralRole :: AF → FilePath → IO ()
addGeneralRole af@(AF qName role _ ) file
  | role `elem` [ AxiomATP, DefinitionATP, HintATP ] = do
      appendFile file $ agdaOriginalTerm qName role
      appendFile file $ prettyTPTP af

  | otherwise = __IMPOSSIBLE__

addConjecture :: AF → FilePath → R ()
addConjecture af file =
  case af of
    (AF qName ConjectureATP _ ) → do
          liftIO $ appendFile file $ agdaOriginalTerm qName ConjectureATP
          liftIO $ appendFile file $ prettyTPTP af

    _ → __IMPOSSIBLE__

createGeneralRolesFile :: [AF] → R ()
createGeneralRolesFile afs = do
  reportSLn "generalRoles" 20 $
            "Creating the general roles file " ++ generalRolesFile ++ " ..."
  liftIO $ do
    _ ← writeFile generalRolesFile headerGeneralRoles
    _ ← mapM_ (`addGeneralRole` generalRolesFile) afs
    _ ← appendFile generalRolesFile footerGeneralRoles
    return ()

createConjectureFile :: (AF, [AF]) → R FilePath
createConjectureFile (af@(AF qName _ _ ), hints) = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.
  let f = outputDir ++
          validFileName (show qName) ++ "_" ++ show (qNameLine qName)
  let file = addExtension f extTPTP
  reportSLn "createConjectureFile" 20 $
                "Creating the conjecture file " ++ show file ++ " ..."
  liftIO $ do
    _ ← writeFile file headerConjecture
    _ ← mapM_ (`addGeneralRole` file) hints
    return ()

  addConjecture af file
  liftIO $ appendFile file footerConjecture
  return file
