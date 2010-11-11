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
import Control.Monad.Reader ( ask )
import Control.Monad.Trans ( liftIO )
import Data.Char ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import System.Directory ( createDirectoryIfMissing )
import System.Environment ( getProgName )
import System.FilePath ( (</>), addExtension )

-- Agda library imports
import Agda.Syntax.Abstract.Name
    ( Name(nameBindingSite)
    , QName(qnameName)
    )
import Agda.Syntax.Common
    ( RoleATP(AxiomATP, ConjectureATP, DefinitionATP, HintATP) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
import AgdaLib.Interface ( qNameLine )
import Common ( T )
import Options ( Options(optOutputDir) )
import Reports ( reportSLn )
import TPTP.Pretty ( prettyTPTP )
import TPTP.Types ( AF(MkAF) )

#include "../undefined.h"

------------------------------------------------------------------------------
class ValidFileName a where
    validFileName :: a → FilePath

instance ValidFileName Char where
    validFileName c
        | c `elem` "._-" = [c]
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr (ord c - 8272)]
        | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
        | otherwise = show $ ord c

-- Requires TypeSynonymInstances.
instance ValidFileName String where
    validFileName = concatMap validFileName

extTPTP :: String
extTPTP = ".tptp"

commentLine :: String
commentLine = "%-----------------------------------------------------------------------------\n"

generalRolesFileName :: T FilePath
generalRolesFileName = do

    (_, opts) ← ask

    let outputDir :: String
        outputDir = optOutputDir opts

    liftIO $ createDirectoryIfMissing True outputDir

    return $ addExtension (outputDir </> "general-roles") extTPTP

communHeader :: IO String
communHeader = do
  prgName ← getProgName
  return $
    commentLine ++
    "% This file was generated automatically by " ++ prgName ++ ".\n" ++
    commentLine ++ "\n"

generalRolesHeader :: IO String
generalRolesHeader = do
  ch ← communHeader
  return $
    ch ++
    "% This file corresponds to the ATP axioms, general hints, and definitions.\n\n"

generalRolesFooter :: String
generalRolesFooter  =
    commentLine ++
    "% End ATP axioms, general hints, and definitions file.\n"

conjectureHeader :: FilePath → IO String
conjectureHeader generalRolesFile = do
  ch ← communHeader
  return $
    ch ++
    "% This file corresponds to an ATP conjecture and its hints.\n\n" ++
    "% We include the general ATP pragmas (axioms, hints and definitions).\n" ++
    "include('" ++ generalRolesFile ++ "').\n\n"

conjectureFooter :: String
conjectureFooter =
    commentLine ++
    "% End ATP conjecture file.\n"

agdaOriginalTerm :: QName → RoleATP → String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% name:\t\t" ++ show qName ++ "\n" ++
    "% role:\t\t" ++ show role ++ "\n" ++
    "% position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addGeneralRole :: AF → FilePath → IO ()
addGeneralRole af@(MkAF qName role _) file
  | role `elem` [ AxiomATP, DefinitionATP, HintATP ] = do
      appendFile file $ agdaOriginalTerm qName role
      appendFile file $ prettyTPTP af

  | otherwise = __IMPOSSIBLE__

addConjecture :: AF → FilePath → T ()
addConjecture af file =
  case af of
    (MkAF qName ConjectureATP _) → do
          liftIO $ appendFile file $ agdaOriginalTerm qName ConjectureATP
          liftIO $ appendFile file $ prettyTPTP af

    _ → __IMPOSSIBLE__

createGeneralRolesFile :: [AF] → T ()
createGeneralRolesFile afs = do

  file ← generalRolesFileName

  reportSLn "generalRoles" 20 $
            "Creating the general roles file " ++ file ++ " ..."
  liftIO $ do
    grh ← generalRolesHeader
    _   ← writeFile file grh
    _   ← mapM_ (`addGeneralRole` file) afs
    _   ← appendFile file generalRolesFooter
    return ()

createConjectureFile :: (AF, [AF]) → T FilePath
createConjectureFile (af@(MkAF qName _ _), hints) = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  (_, opts) ← ask

  let outputDir :: FilePath
      outputDir = optOutputDir opts

  let f :: FilePath
      f = outputDir </>
          validFileName (show qName) ++ "_" ++ show (qNameLine qName)

  let conjectureFile :: FilePath
      conjectureFile = addExtension f extTPTP

  reportSLn "createConjectureFile" 20 $
            "Creating the conjecture file " ++ show conjectureFile ++ " ..."

  generalRolesFile ← generalRolesFileName

  liftIO $ do
    ch ← conjectureHeader generalRolesFile
    _  ← writeFile conjectureFile ch
    _  ← mapM_ (`addGeneralRole` conjectureFile) hints
    return ()

  addConjecture af conjectureFile
  liftIO $ appendFile conjectureFile conjectureFooter
  return conjectureFile
