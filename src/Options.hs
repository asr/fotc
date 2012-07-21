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
  , Options( optAgdaIncludePath
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
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Char ( isDigit )
import Data.List ( foldl' )

import System.Console.GetOpt
  ( ArgDescr(NoArg, ReqArg)
  , ArgOrder(Permute)
  , getOpt
  , OptDescr(Option)
  , usageInfo
  )

import System.Environment ( getProgName )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.List          ( wordsBy )

import qualified Agda.Utils.Trie as Trie ( insert, singleton )

-----------------------------------------------------------------------------

-- | Program command-line options.
data Options = MkOptions
  { optAgdaIncludePath ∷ [FilePath]
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
defaultOptions = MkOptions
  { optAgdaIncludePath = []
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

agdaIncludePathOpt ∷ FilePath → Options → Options
agdaIncludePathOpt [] _ =
  error "Option --agda-include-path (or -i) requires an argument DIR"
agdaIncludePathOpt dir opts =
  opts { optAgdaIncludePath = optAgdaIncludePath opts ++ [dir] }

atpOpt ∷ String → Options → Options
atpOpt []   _    = error "Option --atp requires an argument NAME"
atpOpt name opts = opts { optATP = optATP opts ++ [name] }

helpOpt ∷ Options → Options
helpOpt opts = opts { optHelp = True }

onlyFilesOpt ∷ Options → Options
onlyFilesOpt opts = opts { optOnlyFiles = True }

outputDirOpt ∷ FilePath → Options → Options
outputDirOpt []  _    = error "Option --output-dir requires an argument DIR"
outputDirOpt dir opts = opts { optOutputDir = dir }

snapshotDirOpt ∷ FilePath → Options → Options
snapshotDirOpt []  _    = error "Option --snapshot-dir requires an argument DIR"
snapshotDirOpt dir opts = opts { optSnapshotDir = dir }

snapshotNoErrorOpt ∷ Options → Options
snapshotNoErrorOpt opts = opts { optOnlyFiles = True
                               , optSnapshotNoError = True
                               , optSnapshotTest = True
                               }

snapshotTestOpt ∷ Options → Options
snapshotTestOpt opts = opts { optOnlyFiles = True
                            , optSnapshotTest = True
                            }

timeOpt ∷ String → Options → Options
timeOpt []   _    = error "Option --time requires an argument NUM"
timeOpt secs opts =
  if all isDigit secs
  then opts { optTime = read secs }
  else error "Option --time requires a non-negative integer argument"

unprovedNoErrorOpt ∷ Options → Options
unprovedNoErrorOpt opts = opts { optUnprovedNoError = True }

vampireExecOpt ∷ String → Options → Options
vampireExecOpt []   _    = error "Option --vampire-exec requires an argument COMMAND"
vampireExecOpt name opts = opts { optVampireExec = name }

-- Adapted from @Agda.Interaction.Options.verboseFlag@.
verboseOpt ∷ String → Options → Options
verboseOpt str opts = opts { optVerbose = Trie.insert k n $ optVerbose opts }
  where
  k ∷ [String]
  n ∷ Int
  (k, n) = parseVerbose str

  parseVerbose ∷ String → ([String], Int)
  parseVerbose s =
    case wordsBy (`elem` ":.") s of
      []  → error "Option --verbose requieres an argument of the form x.y.z:N or N"
      ss  → let m ∷ Int
                m = read $ last ss
            in  (init ss, m)

versionOpt ∷ Options → Options
versionOpt opts = opts { optVersion = True }

-- | Description of the command-line 'Options'.
options ∷ [OptDescr (Options → Options)]
options =
  [ Option "i" ["agda-include-path"] (ReqArg agdaIncludePathOpt "DIR")
               "look for imports in DIR"
  , Option []  ["atp"] (ReqArg atpOpt "NAME") $
               "set the ATP (e, equinox, metis, spass, vampire)\n"
               ++ "(default: e, equinox, and vampire)"
  , Option "?" ["help"] (NoArg helpOpt)
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
               ++ "(implies --only-files and --snapshot-test)"
  , Option []  ["snapshot-test"] (NoArg snapshotTestOpt) $
               "compare the generated TPTP files against a snapshot of them\n"
               ++ "(implies --only-files)"
  , Option []  ["time"] (ReqArg timeOpt "NUM")
               "set timeout for the ATPs in seconds (default: 300)"
  , Option []  ["unproved-conjecture-no-error"] (NoArg unprovedNoErrorOpt)
               "an unproved TPTP conjecture does not generate an error\n"
  , Option []  ["vampire-exec"] (ReqArg vampireExecOpt "COMMAND")
               "set the vampire executable (default: vampire_lin64)"
  , Option "v" ["verbose"] (ReqArg verboseOpt "N")
               "set verbosity level to N"
  , Option "V" ["version"] (NoArg versionOpt)
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

-- | Processing the command-line 'Options'.
processOptions ∷ [String] → Either String (Options, FilePath)
processOptions argv =
  case getOpt Permute options argv of
    ([], [], []) → Right (defaultOptions, [])

    (o, files, []) → do
      let opts ∷ Options
          opts = foldl' (flip id) defaultOptions o

      case files of
        []       → Right (opts, [])
        (x : []) → Right (opts, x)
        _        → Left "Only one input file allowed"

    (_, _, errs) → Left $ init $ init $ unlines errs
