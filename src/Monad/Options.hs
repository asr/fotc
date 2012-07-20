-----------------------------------------------------------------------------
-- |
-- Module      : Monad.Options
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Process the command line arguments.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Options ( processOptions ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( MonadError(throwError) )

import Data.List ( foldl' )

import System.Console.GetOpt ( ArgOrder(Permute) , getOpt )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base ( T )
import Options    ( defaultOptions, options, Options )

-----------------------------------------------------------------------------
-- | Processing the command-line 'Options'.
processOptions ∷ [String] → T (Options, String)
processOptions argv =
  case getOpt Permute options argv of
    ([], [], []) → return (defaultOptions, [])

    (o, files, []) → do
      let opts ∷ Options
          opts = foldl' (flip id) defaultOptions o

      case files of
        []       → return (opts, [])
        (x : []) → return (opts, x)
        _        → throwError "Only one input file allowed"

    (_, _, errs) → throwError $ init $ init $ unlines errs
