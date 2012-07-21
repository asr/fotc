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

import Data.Char       ( chr, isAsciiUpper, isAsciiLower, isDigit, ord )
import Data.List.Utils ( replace )

import System.Directory ( createDirectoryIfMissing )
import System.FilePath  ( (</>), addExtension )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name
  ( mnameToConcrete
  , Name(nameConcrete)
  , QName(qnameModule, qnameName)
  )

import Agda.Syntax.Common ( ATPRole )

import Agda.Syntax.Concrete.Name
  ( moduleNameToFileName
  , nameStringParts
  , toTopLevelModuleName
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( whenM )

------------------------------------------------------------------------------
-- Local imports

import AgdaInternal.Interface ( qNameLine )
import Monad.Base             ( getTOpt, T )
import Monad.Reports          ( reportS, reportSLn )
import Options                ( Options(optOnlyFiles, optOutputDir) )
import TPTP.ConcreteSyntax    ( ToTPTP(toTPTP) )

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
    | c == '-' = [c]
    | c `elem` "._" = __IMPOSSIBLE__
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
conjectureFooter = commentLine ++ "% End TPTP file.\n"

agdaOriginalTerm ∷ QName → ATPRole → String
agdaOriginalTerm qName role =
  "% The original Agda term was:\n"
  ++ "% Name:\t" ++ showLn qName
  ++ "% Role:\t" ++ showLn role
  ++ "% Line:\t" ++ showLn (qNameLine qName)

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

  appendFile file header
  mapM_ (`addRole` file) afs
  appendFile file footer

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

      moduleDir ∷ FilePath
      moduleDir = ((`moduleNameToFileName` [])
                   . toTopLevelModuleName
                   . mnameToConcrete
                   . qnameModule) qName

      -- We removed the "/_"s in the module name produced by Agda when
      -- the qName is inside a where clause.
      finalDir ∷ FilePath
      finalDir = outputDir </> replace "/_" "" moduleDir

  liftIO $ createDirectoryIfMissing True finalDir

  reportSLn "createConjectureFile" 20 $ "Final dir: " ++ finalDir

  let f ∷ FilePath
      f = finalDir </>
           show (qNameLine qName)
          ++ "-"
          ++ asciiName ((concat . nameStringParts . nameConcrete . qnameName) qName)

      file ∷ FilePath
      file = addExtension f tptpExt

  reportSLn "createConjectureFile" 20 $
            "Creating " ++ show file ++ " ..."

  let commonDefs ∷ [AF]
      commonDefs = commonRequiredDefs generalRoles conjectureSet

      (newGeneralRoles, newConjectureSet) =
          dropCommonRequiredDefs generalRoles conjectureSet

  unless (nonDuplicate (allRequiredDefs newGeneralRoles newConjectureSet))
         (__IMPOSSIBLE__)

  liftIO $ do
    conjectureH ← conjectureHeader
    writeFile file conjectureH
    addRoles commonDefs file "common required definition(s)"
    addRoles (axioms newGeneralRoles) file "general axiom(s)"
    addRoles (defsAxioms newGeneralRoles) file
             "required ATP definition(s) by the general axiom(s)"
    addRoles (hints newGeneralRoles) file "general hint(s)"
    addRoles (defsHints newGeneralRoles) file
             "required ATP definition(s) by the general hint(s)"
    addRoles (localHintsConjecture  newConjectureSet) file "local hint(s)"
    addRoles (defsLocalHints newConjectureSet) file
             "required ATP definition(s) by the local hint(s)"
    addRoles (defsConjecture newConjectureSet) file
             "required ATP definition(s) by the conjecture"
    addRoles [theConjecture newConjectureSet] file "conjecture"
    appendFile file conjectureFooter

  whenM (getTOpt optOnlyFiles) $
       reportS "" 1 $ "Created " ++ file

  return file
