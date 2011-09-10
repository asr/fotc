{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- |
-- Module      : Utils.Version
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'Version'.
------------------------------------------------------------------------------

module Utils.Version ( printVersion , version ) where

-- Haskell imports
import Data.Version ( showVersion )

-- Local imports
import qualified Paths_agda2atp as P ( version )

------------------------------------------------------------------------------

version ∷ String
version = showVersion P.version

-- | Print version information.
printVersion ∷ String → IO ()
printVersion prgName = putStrLn $ prgName ++ " version " ++ version
