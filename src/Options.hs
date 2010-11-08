-----------------------------------------------------------------------------
-- Process the arguments
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Options
    ( Options(..)
    , processOptions
    , usage
    ) where

-- Haskell imports
import Control.Monad.Error ( ErrorT, throwError )
import Control.Monad.Trans ( liftIO )

import System.Console.GetOpt
    ( ArgDescr(NoArg, ReqArg)
    , ArgOrder (Permute)
    , getOpt
    , OptDescr(Option)
    , usageInfo
    )

-- Agda library imports
import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.List ( wordsBy )
-- import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie ( insert, singleton )

-- Local imports
import Utils.IO ( bye )

-----------------------------------------------------------------------------

data Options = MkOptions
    { optAgdaIncludePath :: [FilePath]
    , optATP             :: [String]
    , optDefAsAxiom      :: Bool
    , optHelp            :: Bool
    , optOnlyFiles       :: Bool
    , optOutputDir       :: FilePath
    , optTime            :: Int
    , optUnprovedError   :: Bool
    , optVerbose         :: Verbosity
    , optVersion         :: Bool
    } deriving ( Show )

defaultOptATP :: [String]
defaultOptATP = ["e", "equinox", "metis"]

defaultOptions :: Options
defaultOptions = MkOptions
  { optAgdaIncludePath = []
  , optATP             = []  -- N.B. The default is defined by
                             -- defaultOptATP and it is handle by
                             -- Options.processOptions.
  , optDefAsAxiom      = False
  , optHelp            = False
  , optOnlyFiles       = False
  , optOutputDir       = "/tmp"
  , optTime            = 300
  , optUnprovedError   = False
  , optVerbose         = Trie.singleton [] 1
  , optVersion         = False
  }

agdaIncludePathOpt :: FilePath → Options → Options
agdaIncludePathOpt dir opts =
    opts { optAgdaIncludePath = optAgdaIncludePath opts ++ [dir] }

atpOpt :: String → Options → Options
atpOpt name opts = opts { optATP = optATP opts ++ [name] }

defAsAxiomOpt :: Options → Options
defAsAxiomOpt opts = opts { optDefAsAxiom = True }

helpOpt :: Options → Options
helpOpt opts = opts { optHelp = True }

timeOpt :: String → Options → Options
timeOpt secs opts = opts { optTime = read secs }

onlyFilesOpt :: Options → Options
onlyFilesOpt opts = opts { optOnlyFiles = True }

outputDirOpt :: FilePath → Options → Options
outputDirOpt dir opts = opts { optOutputDir = dir }

unprovedErrorOpt :: Options → Options
unprovedErrorOpt opts = opts { optUnprovedError = True }

-- Adapted from: Agda.Interaction.Options.verboseFlag.
verboseOpt :: String → Options → Options
verboseOpt str opts = opts { optVerbose = Trie.insert k n $ optVerbose opts }
    where
      (k, n) :: ([String], Int) = parseVerbose str
      parseVerbose :: String → ([String], Int)
      parseVerbose s =
          case wordsBy (`elem` ":.") s of
            []  → error "Argument to verbose should be on the form x.y.z:N or N"
            ss  → let m :: Int
                      m = read $ last ss
                  in (init ss, m)

versionOpt :: Options → Options
versionOpt opts = opts { optVersion = True }

options :: [OptDescr (Options → Options)]
options =
  [ Option "i" ["agda-include-path"] (ReqArg agdaIncludePathOpt "DIR")
               "looks for imports in DIR"
  , Option []  ["atp"] (ReqArg atpOpt "name")
               "set the ATP (default: e, equinox, and metis)"
  , Option []  ["definitions-as-axioms"] (NoArg defAsAxiomOpt)
               "translate the TPTP definitions as TPTP axioms"
  , Option "?" ["help"] (NoArg helpOpt)
               "show this help"
  , Option []  ["only-files"] (NoArg onlyFilesOpt)
               "do not call the ATPs, only to create the TPTP files"
  , Option []  ["output-dir"] (ReqArg outputDirOpt "DIR")
               "directory in which TPTP files are placed (default: /tmp)"
  , Option []  ["time"] (ReqArg timeOpt "secs")
               "set timeout for the ATPs in seconds (default: 300)"
  , Option []  ["unproved-conjecture-error"] (NoArg unprovedErrorOpt)
               "an unproved TPTP conjecture generates an error"
  , Option "v" ["verbose"] (ReqArg verboseOpt "N")
               "set verbosity level to N"
  , Option "V" ["version"] (NoArg versionOpt)
               "show version number"
  ]

usageHeader :: String → String
usageHeader prgName =
    "Usage: " ++ prgName ++ " [OPTION...] file \n"

usage :: String → String
usage prgName = usageInfo (usageHeader prgName) options

processOptions :: [String] → String → ErrorT String IO (Options, String)
processOptions argv prgName =
  case getOpt Permute options argv of
    (_, [], []) → liftIO $ bye $ usage prgName

    (o, (file : []), []) → do
      let opts :: Options
          opts = foldl (flip id) defaultOptions o

      let finalOpts :: Options
          finalOpts =
              if null (optATP opts)  -- No ATPs was chosen.
              then opts { optATP = defaultOptATP }  -- We set up the
                                                    -- defaults ATPs.
              else opts

      return (finalOpts, file)

    (_, _files, []) → throwError "Only one input file allowed"

    (_, _, errors) → throwError $ unlines errors
