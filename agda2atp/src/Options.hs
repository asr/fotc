-----------------------------------------------------------------------------
-- |
-- Module      : Options
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Process the arguments.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Options
  ( defaultOptions
  , options
  , MOptions  -- Required to avoid an Haddock warning.
  , Options( optInputFile
           , optAgdaIncludePath
           , optATP
           , optHelp
           , optOnlyFiles
           , optOutputDir
           , optSnapshotDir
           , optSnapshotNoError
           , optSnapshotTest
           , optTime
           , optUnprovedNoError
           , optVampireExec
           , optVerbose
           , optVersion
           )
  , printUsage
  , processOptions
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Char ( isDigit )
import Data.List ( foldl' )

import System.Console.GetOpt
  ( ArgDescr(NoArg, ReqArg)
  , ArgOrder(ReturnInOrder)
  , getOpt
  , OptDescr(Option)
  , usageInfo
  )

import System.Environment ( getProgName )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.Impossible    ( Impossible(Impossible), throwImpossible )
import Agda.Utils.List          ( wordsBy )

import qualified Agda.Utils.Trie as Trie ( insert, singleton )

------------------------------------------------------------------------------
-- Local imports

#include "undefined.h"

-----------------------------------------------------------------------------

-- | Program command-line options.
data Options = Options
  { optInputFile       ∷ Maybe FilePath
  , optAgdaIncludePath ∷ [FilePath]
  , optATP             ∷ [String]
  , optHelp            ∷ Bool
  , optOnlyFiles       ∷ Bool
  , optOutputDir       ∷ FilePath
  , optSnapshotDir     ∷ FilePath
  , optSnapshotNoError ∷ Bool
  , optSnapshotTest    ∷ Bool
  , optTime            ∷ Int
  , optUnprovedNoError ∷ Bool
  , optVampireExec     ∷ String
  , optVerbose         ∷ Verbosity
  , optVersion         ∷ Bool
  }

-- N.B. The default ATPs are handled by @ATP.callATPs@.
--
-- | Default options use by the program.
defaultOptions ∷ Options
defaultOptions = Options
  { optInputFile       = Nothing
  , optAgdaIncludePath = []
  , optATP             = []
  , optHelp            = False
  , optOnlyFiles       = False
  , optOutputDir       = "/tmp"
  , optSnapshotDir     = "snapshot"
  , optSnapshotNoError = False
  , optSnapshotTest    = False
  , optTime            = 300
  , optUnprovedNoError = False
  , optVampireExec     = "vampire_lin64"
  , optVerbose         = Trie.singleton [] 1
  , optVersion         = False
  }

-- | 'Options' monad.
type MOptions = Options → Either String Options

inputFileOpt ∷ FilePath → MOptions
inputFileOpt file opts =
  case optInputFile opts of
    Nothing → Right opts { optInputFile = Just file }
    Just _  → Left "Only one input file allowed"

agdaIncludePathOpt ∷ FilePath → MOptions
agdaIncludePathOpt [] _ =
  error "Option `--agda-include-path' requires an argument DIR"
agdaIncludePathOpt dir opts =
  Right opts { optAgdaIncludePath = optAgdaIncludePath opts ++ [dir] }

atpOpt ∷ String → MOptions
atpOpt []   _    = Left "Option `--atp' requires an argument NAME"
atpOpt name opts = Right opts { optATP = optATP opts ++ [name] }

helpOpt ∷ MOptions
helpOpt opts = Right opts { optHelp = True }

onlyFilesOpt ∷ MOptions
onlyFilesOpt opts = Right opts { optOnlyFiles = True }

outputDirOpt ∷ FilePath → MOptions
outputDirOpt []  _    = Left "Option `--output-dir' requires an argument DIR"
outputDirOpt dir opts = Right opts { optOutputDir = dir }

snapshotDirOpt ∷ FilePath → MOptions
snapshotDirOpt []  _    = Left "Option `--snapshot-dir' requires an argument DIR"
snapshotDirOpt dir opts = Right opts { optSnapshotDir = dir }

snapshotNoErrorOpt ∷ MOptions
snapshotNoErrorOpt opts = Right opts { optSnapshotNoError = True
                                     , optSnapshotTest = True
                                     }

snapshotTestOpt ∷ MOptions
snapshotTestOpt opts = Right opts { optSnapshotTest = True }

timeOpt ∷ String → MOptions
timeOpt []   _    = Left "Option `--time' requires an argument NUM"
timeOpt secs opts =
  if all isDigit secs
  then Right opts { optTime = read secs }
  else Left "Option `--time' requires a non-negative integer argument"

unprovedNoErrorOpt ∷ MOptions
unprovedNoErrorOpt opts = Right opts { optUnprovedNoError = True }

vampireExecOpt ∷ String → MOptions
vampireExecOpt []   _    = Left "Option `--vampire-exec' requires an argument COMMAND"
vampireExecOpt name opts = Right opts { optVampireExec = name }

-- Adapted from @Agda.Interaction.Options.verboseFlag@.
verboseOpt ∷ String → MOptions
verboseOpt [] _ = Left "Option `--verbose' requires an argument of the form x.y.z:N or N"
verboseOpt str opts =
  Right opts { optVerbose = Trie.insert k n $ optVerbose opts }
  where
  k ∷ [String]
  n ∷ Int
  (k, n) = parseVerbose str

  parseVerbose ∷ String → ([String], Int)
  parseVerbose s =
    case wordsBy (`elem` ":.") s of
      []  → __IMPOSSIBLE__
      ss  → let m ∷ Int
                m = read $ last ss
            in  (init ss, m)

versionOpt ∷ MOptions
versionOpt opts = Right opts { optVersion = True }

-- | Description of the command-line 'Options'.
options ∷ [OptDescr MOptions]
options =
  [ Option "i" ["agda-include-path"] (ReqArg agdaIncludePathOpt "DIR")
               "look for imports in DIR"
  , Option []  ["atp"] (ReqArg atpOpt "NAME") $
               "set the ATP (e, equinox, metis, spass, vampire)\n"
               ++ "(default: e, equinox, and vampire)"
  , Option []  ["help"] (NoArg helpOpt)
               "show this help"
  , Option []  ["only-files"] (NoArg onlyFilesOpt)
               "do not call the ATPs, only to create the TPTP files"
  , Option []  ["output-dir"] (ReqArg outputDirOpt "DIR")
               "directory in which TPTP files are placed (default: /tmp)"
  , Option []  ["snapshot-dir"] (ReqArg snapshotDirOpt "DIR") $
               "directory where is the snapshot of the TPTP files\n"
               ++ "(default: snapshot)"
  , Option []  ["snapshot-no-error"] (NoArg snapshotNoErrorOpt) $
               "a difference in the snapshot-test does not generate an error\n"
               ++ "(implies --snapshot-test)"
  , Option []  ["snapshot-test"] (NoArg snapshotTestOpt)
               "compare the generated TPTP files against a snapshot of them"
  , Option []  ["time"] (ReqArg timeOpt "NUM")
               "set timeout for the ATPs in seconds (default: 300)"
  , Option []  ["unproved-conjecture-no-error"] (NoArg unprovedNoErrorOpt)
               "an unproved TPTP conjecture does not generate an error\n"
  , Option []  ["vampire-exec"] (ReqArg vampireExecOpt "COMMAND")
               "set the vampire executable (default: vampire_lin64)"
  , Option "v" ["verbose"] (ReqArg verboseOpt "N")
               "set verbosity level to N"
  , Option []  ["version"] (NoArg versionOpt)
               "show version number"
  ]

usageHeader ∷ String → String
usageHeader prgName =
  "Usage: " ++ prgName ++ " [OPTIONS] FILE\n"

-- | Print usage information.
printUsage ∷ IO ()
printUsage = do
  progName ← getProgName
  putStrLn $ usageInfo (usageHeader progName) options

processOptionsHelper ∷ [String] → (FilePath → MOptions) → MOptions
processOptionsHelper argv f defaults =
  case getOpt (ReturnInOrder f) options argv of
    (o, _, [])   → foldl' (>>=) (return defaults) o
    (_, _, errs) → Left $ init $ init $ unlines errs

-- | Processing the command-line 'Options'.
processOptions ∷ [String] → Either String Options
processOptions argv = processOptionsHelper argv inputFileOpt defaultOptions
