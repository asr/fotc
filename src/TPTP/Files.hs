------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Files ( createConjectureFile ) where

-- Haskell imports
import Control.Monad        ( unless, when )
import Control.Monad.State  ( get )
import Control.Monad.Trans  ( liftIO )
import Data.Char            ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import System.Directory     ( createDirectoryIfMissing )
import System.Environment   ( getProgName )
import System.FilePath      ( (</>), addExtension )

-- Agda library imports
import Agda.Syntax.Abstract.Name
    ( Name(nameBindingSite)
    , QName(qnameName)
    )
import Agda.Syntax.Common
    ( ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
import AgdaLib.Interface ( qNameLine )
import Monad.Base        ( T, TState(tOpts) )
import Monad.Reports     ( reportS, reportSLn )
import Options           ( Options(optOnlyFiles, optOutputDir) )
import TPTP.Pretty       ( prettyTPTP )
import TPTP.Types
    ( AF(MkAF)
    , allRequiredDefs
    , commonRequiredDefs
    , ConjectureSet(conjectureLocalHints
                   , requiredDefsByConjecture
                   , requiredDefsByLocalHints
                   , theConjecture
                   )
    , GeneralRoles(axioms
                  , hints
                  , requiredDefsByAxioms
                  , requiredDefsByHints
                  )
    , removeCommonRequiredDefs
    )
import Utils.List    ( nonDuplicate )
import Utils.Version ( version )

#include "../undefined.h"

------------------------------------------------------------------------------

class AsciiName a where
    asciiName ∷ a → FilePath

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

tptpExt ∷ String
tptpExt = ".tptp"

commentLine ∷ String
commentLine = "%-----------------------------------------------------------------------------\n"

commentLineLn ∷ String
commentLineLn = commentLine ++ "\n"

conjectureHeader ∷ IO String
conjectureHeader = do
  prgName ← getProgName
  return $
    commentLine ++
    "% This file was generated automatically by " ++ prgName ++
    " version " ++ version ++ ".\n" ++
    commentLineLn

conjectureFooter ∷ String
conjectureFooter =
    "% End ATP pragma conjecture file.\n"

agdaOriginalTerm ∷ QName → ATPRole → String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% Name:\t\t" ++ show qName ++ "\n" ++
    "% Role:\t\t" ++ show role ++ "\n" ++
    "% Position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addRole ∷ AF → ATPRole → FilePath → IO ()
addRole af@(MkAF qName afRole _) role file =
    if afRole == role
      then do
        appendFile file $ agdaOriginalTerm qName role
        appendFile file $ prettyTPTP af
      else __IMPOSSIBLE__

addRoles ∷ [AF] → ATPRole → FilePath → String → IO ()
addRoles afs role file str = do
  let headerRoleComment ∷ String
      headerRoleComment =
          commentLine ++
          "% The " ++ str ++ ".\n\n"

  let footerRoleComment ∷ String
      footerRoleComment =
          "% End " ++ str ++ ".\n\n"

  _  ← appendFile file headerRoleComment
  _  ← mapM_ (\af → addRole af role file) afs
  _  ← appendFile file footerRoleComment
  return ()

createConjectureFile ∷ GeneralRoles → ConjectureSet → T FilePath
createConjectureFile generalRoles conjectureSet = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  state ← get

  let opts ∷ Options
      opts = tOpts state

  let qName ∷ QName
      qName = case theConjecture conjectureSet of
                MkAF _qName _ _ → _qName

  let outputDir ∷ FilePath
      outputDir = optOutputDir opts

  liftIO $ createDirectoryIfMissing True outputDir

  let f ∷ FilePath
      f = outputDir </>
          asciiName (show qName) ++ "_" ++ show (qNameLine qName)

  let file ∷ FilePath
      file = addExtension f tptpExt

  reportSLn "createConjectureFile" 20 $
            "Creating the conjecture file " ++ show file ++ " ..."

  let commonDefs ∷ [AF]
      commonDefs = commonRequiredDefs generalRoles conjectureSet

  let (newGeneralRoles, newConjectureSet) =
          removeCommonRequiredDefs generalRoles conjectureSet

  unless (nonDuplicate (allRequiredDefs newGeneralRoles newConjectureSet))
         (__IMPOSSIBLE__)

  liftIO $ do
    conjectureH ← conjectureHeader
    _ ← writeFile file conjectureH
    _ ← addRoles commonDefs ATPDefinition file "common required definitions"
    _ ← addRoles (axioms newGeneralRoles) ATPAxiom file "general axioms"
    _ ← addRoles (requiredDefsByAxioms newGeneralRoles) ATPDefinition file
                   "required ATP definitions by the general axioms"
    _ ← addRoles (hints newGeneralRoles) ATPHint file "general hints"
    _ ← addRoles (requiredDefsByHints newGeneralRoles) ATPDefinition file
                   "required ATP definitions by the general hints"
    _ ← addRoles (conjectureLocalHints newConjectureSet) ATPHint file "local hints"
    _ ← addRoles (requiredDefsByLocalHints newConjectureSet) ATPDefinition file
                   "required ATP definitions by the local hints"
    _ ← addRoles (requiredDefsByConjecture newConjectureSet) ATPDefinition file
                 "required ATP definitions by the conjecture"
    _ ← addRoles [theConjecture newConjectureSet] ATPConjecture file "conjecture"
    _ ← appendFile file conjectureFooter
    return ()

  when (optOnlyFiles opts) $
       reportS "" 1 $ "Created the conjecture file " ++ file

  return file
