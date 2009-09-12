module Options where

import System.Console.GetOpt ( ArgDescr(..)
                             , ArgOrder (Permute)
                             , getOpt
                             , OptDescr (..)
                             -- , usageInfo
                             )

import Agda.Utils.List ( wordsBy )
import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie

data Options = MkOptions
    { -- optVersion   :: Bool
    -- , optHelp      :: Bool
    optVerbose   :: Trie String Int
    } deriving ( Show )

defaultOptions :: Options
defaultOptions = MkOptions
  { -- optVersion   = False
  -- , optHelp      = False
  optVerbose   = Trie.singleton [] 1
  }

-- Adapted from: Agda.Interaction.Options.verboseFlag.
verboseOpt :: String -> Options -> Options
verboseOpt str opts = opts { optVerbose = Trie.insert k n $ optVerbose opts }
    where -- TODO: Why is not posibble to assign the signature
          --       (k, n) :: ([String], Int)?
          (k, n) = parseVerbose str

          parseVerbose :: String -> ([String], Int)
          parseVerbose s = case wordsBy (`elem` ":.") s of
            []  -> error -- ToDo: We should be use 'msgError'.
                     "argument to verbose should be on the form x.y.z:N or N"
            ss  -> let m :: Int
                       m = read $ last ss
                   in (init ss, m)

options :: [OptDescr (Options -> Options)]
options =
  [ -- Option ['V'] ["version"] (NoArg versionOpt)
    --             "show version number"
  -- , Option ['h'] ["help"] (NoArg helpOpt)
  --               "show help"
  Option ['v'] ["verbose"] (ReqArg verboseOpt "N")
                  "set verbosity level to N"
  ]

parseOptions :: [String] -> String -> IO (Options, [String])
parseOptions argv _prgName = do
  case getOpt Permute options argv of
    ([],   [], [])     -> error "parseOptions: not implemented"
    (o, names, [])     -> return (foldl (flip id) defaultOptions o, names)
    (_,     _, errors) -> error "parseOptions: not implemented"
