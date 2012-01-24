------------------------------------------------------------------------------
-- |
-- Module      : TPTP.Files
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Creation of the TPTP files.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Files ( createConjectureFile ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad        ( unless )
import Control.Monad.Trans  ( MonadIO(liftIO) )
import Data.Char            ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import Data.Functor         ( (<$>) )
import System.Directory     ( createDirectoryIfMissing )
import System.FilePath      ( (</>), addExtension )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( Name(nameBindingSite)
  , QName(qnameName)
  )

import Agda.Syntax.Common
    ( ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint) )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.Interface ( qNameLine )
import Monad.Base        ( getTOpts, T )
import Monad.Reports     ( reportS, reportSLn )
import Options           ( Options(optOnlyFiles, optOutputDir) )
import TPTP.Pretty       ( PrettyTPTP(prettyTPTP) )

import TPTP.Types
  ( AF(MkAF)
  , allRequiredDefs
  , ConjectureSet(conjectureDefs
                 , conjectureLocalHints
                 , localHintsDefs
                 , theConjecture
                 )
  , commonRequiredDefs
  , dropCommonRequiredDefs
  , GeneralRoles(axioms, axiomsDefs, hints, hintsDefs)
  )

import Utils.List    ( nonDuplicate )
import Utils.Monad   ( whenM )
import Utils.Show    ( showLn )
import Utils.Version ( progNameVersion )

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
  prg ← progNameVersion
  return $
    commentLine
    ++ "% This file was generated automatically by "
    ++ prg ++ ".\n"
    ++ commentLineLn

conjectureFooter ∷ String
conjectureFooter = "% End ATP pragma conjecture file.\n"

agdaOriginalTerm ∷ QName → ATPRole → String
agdaOriginalTerm qName role =
  "% The original Agda term was:\n"
  ++ "% Name:\t\t" ++ showLn qName
  ++ "% Role:\t\t" ++ showLn role
  ++ "% Position:\t" ++ showLn (nameBindingSite $ qnameName qName)

addRole ∷ AF → ATPRole → FilePath → IO ()
addRole af@(MkAF qName afRole _) role file =
  if afRole == role
  then do
    appendFile file $ agdaOriginalTerm qName role
    appendFile file $ prettyTPTP af
  else __IMPOSSIBLE__

addRoles ∷ [AF] → ATPRole → FilePath → String → IO ()
addRoles afs role file str = do
  let header, footer ∷ String
      header = commentLine ++ "% The " ++ str ++ ".\n\n"
      footer = "% End " ++ str ++ ".\n\n"

  _  ← appendFile file header
  _  ← mapM_ (\af → addRole af role file) afs
  _  ← appendFile file footer
  return ()

-- | The function 'createConjectureFile' creates a TPTP file with a
-- conjecture.
createConjectureFile ∷ GeneralRoles → ConjectureSet → T FilePath
createConjectureFile generalRoles conjectureSet = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  outputDir ← optOutputDir <$> getTOpts

  let qName ∷ QName
      qName = case theConjecture conjectureSet of
                MkAF _qName _ _ → _qName

  liftIO $ createDirectoryIfMissing True outputDir

  let f ∷ FilePath
      f = outputDir </>
          asciiName (show qName) ++ "_" ++ show (qNameLine qName)

      file ∷ FilePath
      file = addExtension f tptpExt

  reportSLn "createConjectureFile" 20 $
            "Creating the conjecture file " ++ show file ++ " ..."

  let commonDefs ∷ [AF]
      commonDefs = commonRequiredDefs generalRoles conjectureSet

      (newGeneralRoles, newConjectureSet) =
          dropCommonRequiredDefs generalRoles conjectureSet

  unless (nonDuplicate (allRequiredDefs newGeneralRoles newConjectureSet))
         (__IMPOSSIBLE__)

  liftIO $ do
    conjectureH ← conjectureHeader
    _ ← writeFile file conjectureH
    _ ← addRoles commonDefs ATPDefinition file "common required definitions"
    _ ← addRoles (axioms newGeneralRoles) ATPAxiom file "general axioms"
    _ ← addRoles (axiomsDefs newGeneralRoles) ATPDefinition file
                   "required ATP definitions by the general axioms"
    _ ← addRoles (hints newGeneralRoles) ATPHint file "general hints"
    _ ← addRoles (hintsDefs newGeneralRoles) ATPDefinition file
                   "required ATP definitions by the general hints"
    _ ← addRoles (conjectureLocalHints newConjectureSet) ATPHint file "local hints"
    _ ← addRoles (localHintsDefs newConjectureSet) ATPDefinition file
                   "required ATP definitions by the local hints"
    _ ← addRoles (conjectureDefs newConjectureSet) ATPDefinition file
                 "required ATP definitions by the conjecture"
    _ ← addRoles [theConjecture newConjectureSet] ATPConjecture file "conjecture"
    _ ← appendFile file conjectureFooter
    return ()

  whenM (optOnlyFiles <$> getTOpts) $
       reportS "" 1 $ "Created the conjecture file " ++ file

  return file
