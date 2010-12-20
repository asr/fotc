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
import Control.Monad.State  ( get )
import Control.Monad.Trans  ( liftIO )
import Data.Char            ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import System.Directory     ( createDirectoryIfMissing )
import System.Environment   ( getProgName )
import System.FilePath      ( (</>), addExtension, replaceExtension )

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
import Monad.Base        ( T, TState(tFile, tOpts) )
import Monad.Reports     ( reportSLn )
import Options           ( Options(optOutputDir) )
import TPTP.Pretty       ( prettyTPTP )
import TPTP.Types
    ( AF(MkAF)
    , ConjectureAFs(definitionsAF, localHintsAF, theConjectureAF)
    , GeneralRolesAF(axiomsAF
                    , hintsAF
                    , requiredDefsbyAxiomsAF
                    , requiredDefsbyHintsAF
                    )
    )
import Utils.String ( replace )

#include "../undefined.h"

------------------------------------------------------------------------------

class AsciiName a where
    asciiName :: a → FilePath

instance AsciiName Char where
    asciiName c
        | c `elem` "._-" = [c]
        -- The character is a subscript number (i.e. ₀, ₁, ₂, ...).
        | ord c `elem` [8320 .. 8329] = [chr (ord c - 8272)]
        | isDigit c || isAsciiUpper c || isAsciiLower c = [c]
        | otherwise = show $ ord c

-- Requires TypeSynonymInstances.
instance AsciiName String where
    asciiName = concatMap asciiName

tptpExt :: String
tptpExt = ".tptp"

commentLine :: String
commentLine = "%-----------------------------------------------------------------------------\n"

generalRolesFileName :: T FilePath
generalRolesFileName = do

    state ← get

    let outputDir :: String
        outputDir = optOutputDir $ tOpts state

    liftIO $ createDirectoryIfMissing True outputDir

    return $ outputDir </>
             replace '/' '.' (replaceExtension (tFile state) tptpExt)

commonHeader :: IO String
commonHeader = do
  prgName ← getProgName
  return $
    commentLine ++
    "% This file was generated automatically by " ++ prgName ++ ".\n" ++
    commentLine ++ "\n"

generalRolesHeader :: T String
generalRolesHeader = do
  state ← get
  ch    ← liftIO commonHeader
  return $
    ch ++
    "% This file corresponds to the general ATP pragmas (axioms and general hints)\n" ++
    "% for the file " ++ show (tFile state) ++ ".\n\n"

generalRolesFooter :: String
generalRolesFooter  =
    "% End general ATP pragmas file.\n"

conjectureHeader :: T String
conjectureHeader = do
  generalRolesFile ← generalRolesFileName
  ch               ← liftIO commonHeader
  return $
    ch ++
    "% This file corresponds to an ATP pragma conjecture, its local hints,\n" ++
    "% and the required definitions.\n\n" ++
    "% We include the general ATP pragmas (axioms, hints and definitions).\n" ++
    "include('" ++ generalRolesFile ++ "').\n\n"

conjectureFooter :: String
conjectureFooter =
    "% End ATP pragma conjecture file.\n"

agdaOriginalTerm :: QName → RoleATP → String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% Name:\t\t" ++ show qName ++ "\n" ++
    "% Role:\t\t" ++ show role ++ "\n" ++
    "% Position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addRole :: AF → RoleATP → FilePath → IO ()
addRole af@(MkAF qName afRole _) role file =
    if (afRole == role)
      then do
        appendFile file $ agdaOriginalTerm qName role
        appendFile file $ prettyTPTP af
      else __IMPOSSIBLE__

addRoles :: [AF] → RoleATP → FilePath → String → IO ()
addRoles afs role file str = do
  let headerRoleComment :: String
      headerRoleComment =
          commentLine ++
          "% The " ++ str ++ ".\n\n"

  let footerRoleComment :: String
      footerRoleComment =
          "% End " ++ str ++ ".\n\n"

  _  ← appendFile file headerRoleComment
  _  ← mapM_ (\af → addRole af role file) afs
  _  ← appendFile file footerRoleComment
  return ()

createGeneralRolesFile :: GeneralRolesAF → T ()
createGeneralRolesFile generalRolesAF = do

  file ← generalRolesFileName

  reportSLn "generalRoles" 20 $
            "Creating the general roles file " ++ file ++ " ..."

  grh ← generalRolesHeader
  liftIO $ do
    _   ← writeFile file grh
    _   ← addRoles (axiomsAF generalRolesAF) AxiomATP file "general axioms"
    _   ← addRoles (requiredDefsbyAxiomsAF generalRolesAF) DefinitionATP file
                   "required ATP definitions by the general axioms"
    _   ← addRoles (hintsAF generalRolesAF) HintATP file "general hints"
    _   ← addRoles (requiredDefsbyHintsAF generalRolesAF) DefinitionATP file
                   "required ATP definitions by the general hints"
    _   ← appendFile file generalRolesFooter
    return ()

createConjectureFile :: ConjectureAFs → T FilePath
createConjectureFile conjectureAFs = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  state ← get

  let qName :: QName
      qName = case theConjectureAF conjectureAFs of
                MkAF _qName _ _ → _qName

  let outputDir :: FilePath
      outputDir = optOutputDir $ tOpts state

  let f :: FilePath
      f = outputDir </>
          asciiName (show qName) ++ "_" ++ show (qNameLine qName)

  let conjectureFile :: FilePath
      conjectureFile = addExtension f tptpExt

  reportSLn "createConjectureFile" 20 $
            "Creating the conjecture file " ++ show conjectureFile ++ " ..."

  conjectureH ← conjectureHeader
  liftIO $ do
    _ ← writeFile conjectureFile conjectureH
    _ ← addRoles (localHintsAF conjectureAFs) HintATP conjectureFile
                 "local hints"
    _ ← addRoles (definitionsAF conjectureAFs) DefinitionATP conjectureFile
                 "required ATP definition"
    _ ← addRoles [theConjectureAF conjectureAFs] ConjectureATP conjectureFile
                 "conjecture"
    _ ← appendFile conjectureFile conjectureFooter
    return ()

  return conjectureFile
