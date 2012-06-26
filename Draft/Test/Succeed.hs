------------------------------------------------------------------------------
-- |
-- Module      : Test.Succeed
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Suite of successfull tests.
------------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fwarn-auto-orphans #-}
{-# OPTIONS_GHC -fwarn-auto-orphans #-}
{-# OPTIONS_GHC -fwarn-identities #-}
{-# OPTIONS_GHC -fwarn-incomplete-record-updates #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fwarn-missing-import-lists #-}
{-# OPTIONS_GHC -fwarn-missing-local-sigs #-}
{-# OPTIONS_GHC -fwarn-monomorphism-restriction #-}
{-# OPTIONS_GHC -fwarn-tabs #-}
{-# OPTIONS_GHC -Werror #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main ( main ) where

import Control.Monad ( mapM, Monad((>>=), return) )

import Data.Eq       ( Eq((==)) )
import Data.Function ( ($) )
import Data.List     ( (++), all, isInfixOf )
import Data.String   ( String )

import System.Exit
  ( ExitCode(ExitFailure, ExitSuccess)
  , exitFailure
  , exitSuccess
  )

import System.FilePath.Find ( (==?), always, extension, find )
import System.IO            ( FilePath, IO, putStr, putStrLn )
import System.Process       ( readProcessWithExitCode )

------------------------------------------------------------------------------

agdaOptions ∷ [String]
agdaOptions = ["--ignore-interfaces"]

succeedPath ∷ String
succeedPath = "Test/Succeed/"

test ∷ FilePath → IO ExitCode
test file = do
  putStrLn $ "Testing: " ++ file
  (exitCode1, output1, err1) ←
    readProcessWithExitCode "agda" (agdaOptions ++ [file]) []
  case exitCode1 of
    ExitFailure _ → do
      putStr output1
      putStr err1
      exitFailure
    ExitSuccess → do
      (exitCode2, output2, err2) ←
        if "NonFOL" `isInfixOf` file
          then readProcessWithExitCode "agda2atp" ["--non-fol", file] []
          else readProcessWithExitCode "agda2atp" [file] []
      putStr output2
      putStr err2
      return exitCode2

tests ∷ IO [ExitCode]
tests = find always (extension ==? ".agda") succeedPath >>= mapM test

main ∷ IO ExitCode
main = do
  exitCodes ← tests
  if all (ExitSuccess ==) exitCodes
    then exitSuccess
    else exitFailure
