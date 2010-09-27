-----------------------------------------------------------------------------
-- Process the arguments
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Options where

-- Haskell imports
import System.Console.GetOpt
    ( ArgDescr(..)
    , ArgOrder (Permute)
    , getOpt
    , OptDescr (..)
    , usageInfo
    )

-- Agda library imports
import Agda.Utils.List ( wordsBy )
import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie

-- Local imports
import Utils.IO ( bye )

-----------------------------------------------------------------------------
data Options = MkOptions
    { optVersion       :: Bool
    , optHelp          :: Bool
    , optVerbose       :: Trie String Int
    , optATP           :: [String]
    , optOnlyFiles     :: Bool
    , optTime          :: Int
    , optDefAsAxiom    :: Bool
    , optOutputDir     :: FilePath
    , optUnprovedError :: Bool
    } deriving ( Show )

defaultOptions :: Options
defaultOptions = MkOptions
  { optVersion       = False
  , optHelp          = False
  , optVerbose       = Trie.singleton [] 1
  , optATP           = []
  , optOnlyFiles     = False
  , optTime          = 300
  , optDefAsAxiom    = False
  , optOutputDir     = "/tmp"
  , optUnprovedError = False
  }

versionOpt :: Options → Options
versionOpt opts = opts { optVersion = True }

helpOpt :: Options → Options
helpOpt opts = opts { optHelp = True }

-- Adapted from: Agda.Interaction.Options.verboseFlag.
verboseOpt :: String → Options → Options
verboseOpt str opts = opts { optVerbose = Trie.insert k n $ optVerbose opts }
    where
      (k, n) :: ([String], Int) = parseVerbose str
      parseVerbose :: String → ([String], Int)
      parseVerbose s =
          case wordsBy (`elem` ":.") s of
            []  → error "argument to verbose should be on the form x.y.z:N or N"
            ss  → let m :: Int
                      m = read $ last ss
                  in (init ss, m)

atpOpt :: String → Options → Options
atpOpt name opts = opts { optATP = name : optATP opts }

onlyFilesOpt :: Options → Options
onlyFilesOpt opts = opts { optOnlyFiles = True }

timeOpt :: String → Options → Options
timeOpt secs opts = opts { optTime = read secs }

defAsAxiomOpt :: Options → Options
defAsAxiomOpt opts = opts { optDefAsAxiom = True }

outputDirOpt :: FilePath → Options → Options
outputDirOpt dir opts = opts { optOutputDir = dir }

unprovedErrorOpt :: Options → Options
unprovedErrorOpt opts = opts { optUnprovedError = True }

options :: [OptDescr (Options → Options)]
options =
  [ Option ['V'] ["version"] (NoArg versionOpt)
                 "show version number"
  , Option ['?'] ["help"] (NoArg helpOpt)
                 "show this help"
  , Option ['v'] ["verbose"] (ReqArg verboseOpt "N")
                 "set verbosity level to N"
  , Option []    ["atp"] (ReqArg atpOpt "name")
                  "set the ATP (eprover, equinox, and/or metis)"
  , Option []    ["only-files"] (NoArg onlyFilesOpt)
                 "do not call the ATPs, only to create the TPTP files"
  , Option []    ["time"] (ReqArg timeOpt "secs")
                 "set timeout for the ATPs in seconds (default: 300)"
  , Option []    ["definitions-as-axioms"] (NoArg defAsAxiomOpt)
                 "translate the TPTP definitions as TPTP axioms"
  , Option []    ["output-dir"] (ReqArg outputDirOpt "DIR")
                 "directory in which TPTP files are placed (default: /tmp)"
  , Option []    ["unproved-conjecture-error"] (NoArg unprovedErrorOpt)
                 "an unproved TPTP conjecture generates an error"
  ]

usageHeader :: String → String
usageHeader prgName =
    "Usage: " ++ prgName ++ " [OPTION...] file \n"

usage :: String → String
usage prgName = usageInfo (usageHeader prgName) options

parseOptions :: [String] → String → IO (Options, [String])
parseOptions argv prgName =
  case getOpt Permute options argv of
    ([],   [], [])      → bye $ usage prgName
    (o, names, [])      → return (foldl (flip id) defaultOptions o, names)
    (_,     _, _errors) → error "parseOptions: not implemented"
