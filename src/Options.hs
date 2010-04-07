-----------------------------------------------------------------------------
-- Process the arguments
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Options where

-- Haskell imports
import System.Console.GetOpt ( ArgDescr(..)
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
    { optVersion :: Bool
    , optHelp    :: Bool
    , optVerbose :: Trie String Int
    , optATP     :: String
    } deriving ( Show )

defaultOptions :: Options
defaultOptions = MkOptions
  { optVersion = False
  , optHelp    = False
  , optVerbose = Trie.singleton [] 1
  , optATP     = "equinox"
  }

versionOpt :: Options -> Options
versionOpt opts = opts { optVersion = True }

helpOpt :: Options -> Options
helpOpt opts = opts { optHelp = True }

-- Adapted from: Agda.Interaction.Options.verboseFlag.
verboseOpt :: String -> Options -> Options
verboseOpt str opts = opts { optVerbose = Trie.insert k n $ optVerbose opts }
    where (k, n) :: ([String], Int) = parseVerbose str
          parseVerbose :: String -> ([String], Int)
          parseVerbose s = case wordsBy (`elem` ":.") s of
            []  -> error
                     "argument to verbose should be on the form x.y.z:N or N"
            ss  -> let m :: Int
                       m = read $ last ss
                   in (init ss, m)

atpOpt :: String -> Options -> Options
atpOpt name opts = opts { optATP = name }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['V'] ["version"] (NoArg versionOpt)
                 "show version number"
  , Option ['?'] ["help"] (NoArg helpOpt)
                 "show this help"
  , Option ['v'] ["verbose"] (ReqArg verboseOpt "N")
                  "set verbosity level to N"
  , Option []    ["ATP"] (ReqArg atpOpt "name")
                  "set the ATP (default: equinox)"
  ]

usageHeader :: String -> String
usageHeader prgName =
    "Usage: " ++ prgName ++ " [OPTION...] file \n"

usage :: String -> String
usage prgName = usageInfo (usageHeader prgName) options

parseOptions :: [String] -> String -> IO (Options, [String])
parseOptions argv prgName =
  case getOpt Permute options argv of
    ([],   [], [])      -> bye $ usage prgName
    (o, names, [])      -> return (foldl (flip id) defaultOptions o, names)
    (_,     _, _errors) -> error "parseOptions: not implemented"
