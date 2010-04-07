module Utils.Version ( version ) where

-- Haskell imports
import Data.Version ( showVersion )

-- Local imports
import qualified Paths_agda2atp as P ( version )

version :: String
version = showVersion P.version
