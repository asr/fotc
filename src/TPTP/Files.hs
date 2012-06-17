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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TPTP.Files ( createConjectureFile ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>), (>>=), fail) )
#endif
import Control.Monad ( mapM_, Monad(return), unless )

import Control.Monad.Trans  ( MonadIO(liftIO) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Char     ( Char, chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import Data.Bool     ( (||), Bool(True), otherwise )
import Data.Function ( ($) )
import Data.List     ( (++), concatMap, elem )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif
import GHC.Num ( Num((-)) )

import System.Directory ( createDirectoryIfMissing )
import System.FilePath  ( (</>), addExtension )
import System.IO        ( appendFile, FilePath, IO, writeFile )

import Text.Show ( Show(show) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( Name(nameBindingSite)
  , QName(qnameName)
  )

import Agda.Syntax.Common    ( ATPRole )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( whenM )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.Interface   ( qNameLine )
import Monad.Base          ( getTOpt, T )
import Monad.Reports       ( reportS, reportSLn )
import Options             ( Options(optOnlyFiles, optOutputDir) )
import TPTP.ConcreteSyntax ( ToTPTP(toTPTP) )

import TPTP.Types
  ( AF(MkAF)
  , allRequiredDefs
  , ConjectureSet(defsConjecture
                 , defsLocalHints
                 , localHintsConjecture
                 , theConjecture
                 )
  , commonRequiredDefs
  , dropCommonRequiredDefs
  , GeneralRoles(axioms, defsAxioms, defsHints, hints)
  )

import Utils.List    ( nonDuplicate )
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

-- Requires @TypeSynonymInstances@.
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

addRole ∷ AF → FilePath → IO ()
addRole af@(MkAF qName afRole _) file = do
  appendFile file $ agdaOriginalTerm qName afRole
  appendFile file $ toTPTP af

addRoles ∷ [AF] → FilePath → String → IO ()
addRoles []  _    _   = return ()
addRoles afs file str = do
  let header, footer ∷ String
      header = commentLine ++ "% The " ++ str ++ ".\n\n"
      footer = "% End " ++ str ++ ".\n\n"

  _  ← appendFile file header
  _  ← mapM_ (`addRole` file) afs
  _  ← appendFile file footer
  return ()

-- | The function 'createConjectureFile' creates a TPTP file with a
-- conjecture.
createConjectureFile ∷ GeneralRoles → ConjectureSet → T FilePath
createConjectureFile generalRoles conjectureSet = do
  -- To avoid clash names with the terms inside a where clause, we
  -- added the line number where the term was defined to the file
  -- name.

  unless (nonDuplicate (axioms generalRoles))     (__IMPOSSIBLE__)
  unless (nonDuplicate (defsAxioms generalRoles)) (__IMPOSSIBLE__)
  unless (nonDuplicate (hints generalRoles))      (__IMPOSSIBLE__)
  unless (nonDuplicate (defsHints generalRoles))  (__IMPOSSIBLE__)

  unless (nonDuplicate (defsConjecture conjectureSet))       (__IMPOSSIBLE__)
  unless (nonDuplicate (localHintsConjecture conjectureSet)) (__IMPOSSIBLE__)
  unless (nonDuplicate (defsLocalHints conjectureSet))       (__IMPOSSIBLE__)

  outputDir ← getTOpt optOutputDir

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
    writeFile file conjectureH
    addRoles commonDefs file "common required definitions"
    addRoles (axioms newGeneralRoles) file "general axioms"
    addRoles (defsAxioms newGeneralRoles) file
             "required ATP definitions by the general axioms"
    addRoles (hints newGeneralRoles) file "general hints"
    addRoles (defsHints newGeneralRoles) file
             "required ATP definitions by the general hints"
    addRoles (localHintsConjecture  newConjectureSet) file "local hints"
    addRoles (defsLocalHints newConjectureSet) file
             "required ATP definitions by the local hints"
    addRoles (defsConjecture newConjectureSet) file
             "required ATP definitions by the conjecture"
    addRoles [theConjecture newConjectureSet] file "conjecture"
    appendFile file conjectureFooter
    return ()

  whenM (getTOpt optOnlyFiles) $
       reportS "" 1 $ "Created the conjecture file " ++ file

  return file
