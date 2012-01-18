-----------------------------------------------------------------------------
-- |
-- Module      : Monad.Reports
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Reports via the verbose option.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Reports ( reportS, reportSLn ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( when )
import Control.Monad.Trans ( MonadIO(liftIO) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.Impossible    ( Impossible (Impossible), throwImpossible )

import qualified Agda.Utils.Trie as Trie ( lookupPath )

import Agda.Utils.List ( wordsBy )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base ( getTOpts, T )
import Options    ( Options(optVerbose) )

#include "../undefined.h"

-----------------------------------------------------------------------------
-- Nice way to report things via the verbose option.
-- Adapted from Agda.TypeChecking.Monad.Options.

type VerboseKey = String

getVerbosity ∷ T Verbosity
getVerbosity = fmap optVerbose getTOpts

-- Precondition: The level must be non-negative.
verboseS ∷ VerboseKey → Int → T () → T ()
verboseS k n action | n < 0     =  __IMPOSSIBLE__
                    | otherwise = do
  t ← getVerbosity
  let ks = wordsBy (`elem` ".:") k
      m  = maximum $ 0 : Trie.lookupPath ks t
  when (n <= m) action

reportS ∷ VerboseKey → Int → String → T ()
reportS k n s = verboseS k n $ liftIO $ putStr (s ++ "\n")

reportSLn ∷ VerboseKey → Int → String → T ()
reportSLn k n s = verboseS k n $ liftIO $ putStrLn (s ++ "\n")
