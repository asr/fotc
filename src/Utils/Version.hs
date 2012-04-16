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

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Version ( progNameVersion ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>=), fail) )
#endif
import Control.Monad ( Monad(return) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Version  ( showVersion )
import Data.Function ( ($) )
import Data.List     ( (++) )

import System.Environment ( getProgName )
import System.IO          ( IO )

------------------------------------------------------------------------------
-- Local imports

import qualified Paths_agda2atp as P ( version )

------------------------------------------------------------------------------

-- | Return program name and version information.
progNameVersion ∷ IO String
progNameVersion = do
  progName ← getProgName
  return $ progName ++ " version " ++ showVersion P.version
