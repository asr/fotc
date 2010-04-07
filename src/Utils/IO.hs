module Utils.IO where

-- Haskell imports
import System.Exit ( exitSuccess )

bye :: String -> IO a
bye s = putStrLn s >> exitSuccess
