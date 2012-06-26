-----------------------------------------------------------------------------
-- |
-- Module      : Monad.Reports
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Reports via the @--verbose@ option.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Reports
  ( reportS
  , reportSLn
  , VerboseKey  -- Required to avoid an Haddock warning.
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( when )
import Control.Monad.Trans ( MonadIO(liftIO) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible    ( Impossible (Impossible), throwImpossible )

import qualified Agda.Utils.Trie as Trie ( lookupPath )

import Agda.Utils.List ( wordsBy )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base ( getTOpt, T )
import Options    ( Options(optVerbose) )

#include "../undefined.h"

-----------------------------------------------------------------------------
-- Nice way to report things via the @--verbose@ option. Adapted from
-- @Agda.TypeChecking.Monad.Options@.

-- | Key for the @--verbose@ option.
type VerboseKey = String

-- Precondition: The level must be non-negative.
verboseS ∷ VerboseKey → Int → T () → T ()
verboseS k n action | n < 0     =  __IMPOSSIBLE__
                    | otherwise = do
  t ← getTOpt optVerbose
  let ks ∷ [String]
      ks = wordsBy (`elem` ".:") k

      m ∷ Int
      m = maximum $ 0 : Trie.lookupPath ks t
  when (n <= m) action

-- | Print debug information via the @--verbose@ option.
reportS ∷ VerboseKey → Int → String → T ()
reportS k n s = verboseS k n $ liftIO $ putStr (s ++ "\n")

-- | Print debug information via the @--verbose@ option.
reportSLn ∷ VerboseKey → Int → String → T ()
reportSLn k n s = verboseS k n $ liftIO $ putStrLn (s ++ "\n")
