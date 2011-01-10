------------------------------------------------------------------------------
-- Creation of the TPTP files
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Files ( createConjectureFile ) where

-- Haskell imports
import Control.Monad        ( unless )
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
    ( RoleATP(AxiomATP, ConjectureATP, DefinitionATP, HintATP) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
import AgdaLib.Interface ( qNameLine )
import Monad.Base        ( T, TState(tOpts) )
import Monad.Reports     ( reportSLn )
import Options           ( Options(optOutputDir) )
import TPTP.Pretty       ( prettyTPTP )
import TPTP.Types
    ( AF(MkAF)
    , allRequiredDefsAF
    , commonRequiredDefsAF
    , ConjectureAFs(localHintsAF
                   , requiredDefsByConjectureAF
                   , requiredDefsByLocalHintsAF
                   , theConjectureAF
                   )
    , GeneralRolesAF(axiomsAF
                    , hintsAF
                    , requiredDefsByAxiomsAF
                    , requiredDefsByHintsAF
                    )
    , removeCommonRequiredDefsAF
    )
import Utils.List ( nonDuplicate )

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
    "% This file was generated automatically by " ++ prgName ++ ".\n" ++
    commentLineLn

conjectureFooter ∷ String
conjectureFooter =
    "% End ATP pragma conjecture file.\n"

agdaOriginalTerm ∷ QName → RoleATP → String
agdaOriginalTerm qName role =
    "% The original Agda term was:\n" ++
    "% Name:\t\t" ++ show qName ++ "\n" ++
    "% Role:\t\t" ++ show role ++ "\n" ++
    "% Position:\t" ++ show (nameBindingSite $ qnameName qName) ++ "\n"

addRole ∷ AF → RoleATP → FilePath → IO ()
addRole af@(MkAF qName afRole _) role file =
    if afRole == role
      then do
        appendFile file $ agdaOriginalTerm qName role
        appendFile file $ prettyTPTP af
      else __IMPOSSIBLE__

addRoles ∷ [AF] → RoleATP → FilePath → String → IO ()
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

createConjectureFile ∷ GeneralRolesAF → ConjectureAFs → T FilePath
createConjectureFile generalRolesAF conjectureAFs = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  state ← get

  let qName ∷ QName
      qName = case theConjectureAF conjectureAFs of
                MkAF _qName _ _ → _qName

  let outputDir ∷ FilePath
      outputDir = optOutputDir $ tOpts state

  liftIO $ createDirectoryIfMissing True outputDir

  let f ∷ FilePath
      f = outputDir </>
          asciiName (show qName) ++ "_" ++ show (qNameLine qName)

  let file ∷ FilePath
      file = addExtension f tptpExt

  reportSLn "createConjectureFile" 20 $
            "Creating the conjecture file " ++ show file ++ " ..."

  let commonDefs ∷ [AF]
      commonDefs = commonRequiredDefsAF generalRolesAF conjectureAFs

  let (newGeneralRolesAF, newConjectureAFs) =
          removeCommonRequiredDefsAF generalRolesAF conjectureAFs

  unless (nonDuplicate (allRequiredDefsAF newGeneralRolesAF newConjectureAFs))
         (__IMPOSSIBLE__)

  liftIO $ do
    conjectureH ← conjectureHeader
    _ ← writeFile file conjectureH
    _ ← addRoles commonDefs DefinitionATP file "common required definitions"
    _ ← addRoles (axiomsAF newGeneralRolesAF) AxiomATP file "general axioms"
    _ ← addRoles (requiredDefsByAxiomsAF newGeneralRolesAF) DefinitionATP file
                   "required ATP definitions by the general axioms"
    _ ← addRoles (hintsAF newGeneralRolesAF) HintATP file "general hints"
    _ ← addRoles (requiredDefsByHintsAF newGeneralRolesAF) DefinitionATP file
                   "required ATP definitions by the general hints"
    _ ← addRoles (localHintsAF newConjectureAFs) HintATP file "local hints"
    _ ← addRoles (requiredDefsByLocalHintsAF newConjectureAFs) DefinitionATP file
                   "required ATP definitions by the local hints"
    _ ← addRoles (requiredDefsByConjectureAF newConjectureAFs) DefinitionATP file
                 "required ATP definitions by the conjecture"
    _ ← addRoles [theConjectureAF newConjectureAFs] ConjectureATP file "conjecture"
    _ ← appendFile file conjectureFooter
    return ()

  return file
