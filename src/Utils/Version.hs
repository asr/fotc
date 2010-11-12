{-# LANGUAGE UnicodeSyntax #-}

module Utils.Version ( printVersion ) where

-- Haskell imports
import Data.Version ( showVersion )

-- Local imports
import qualified Paths_agda2atp as P ( version )

------------------------------------------------------------------------------

version :: String
version = showVersion P.version

-- | Print version information.
printVersion :: String → IO ()
printVersion prgName = putStrLn $ prgName ++ " version " ++ version
