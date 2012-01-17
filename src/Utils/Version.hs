------------------------------------------------------------------------------
-- |
-- Module      : Utils.Version
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'Version'.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Version ( printVersion , version ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Version       ( showVersion )
import System.Environment ( getProgName )

------------------------------------------------------------------------------
-- Local imports

import qualified Paths_agda2atp as P ( version )

------------------------------------------------------------------------------

version ∷ String
version = showVersion P.version

-- | Print version information.
printVersion ∷ IO ()
printVersion = do
  progName ← getProgName
  putStrLn $ progName ++ " version " ++ version
