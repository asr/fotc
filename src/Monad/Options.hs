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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Options ( processOptions ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( Monad(return) )
import Control.Monad.Error ( MonadError(throwError) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Function ( ($), flip, id )
import Data.List     ( foldl', null, unlines )

import System.Console.GetOpt
  ( ArgOrder(Permute)
  , getOpt
  )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base ( T )

import Options
  ( defaultATPs
  , defaultOptions
  , options
  , Options(optATP)
  )

-----------------------------------------------------------------------------

processOptions ∷ [String] → T (Options, String)
processOptions argv =
  case getOpt Permute options argv of
    ([], [], []) → throwError "Missing input file (try --help)"

    (o, files, []) → do
      let opts ∷ Options
          opts = foldl' (flip id) defaultOptions o

          finalOpts ∷ Options
          finalOpts =
            if null (optATP opts)  -- No ATPs was chosen.
            then opts { optATP = defaultATPs }  -- We set up the defaults ATPs.
            else opts

      case files of
        []       → return (finalOpts, [])
        (x : []) → return (finalOpts, x)
        _        → throwError "Only one input file allowed"

    (_, _, errs) → throwError $ unlines errs
