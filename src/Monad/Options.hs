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

{-# LANGUAGE UnicodeSyntax #-}

module Monad.Options ( processOptions ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( throwError )
import Data.List           ( foldl' )
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
  , optATP
  , optHelp
  , options
  , Options
  )

-----------------------------------------------------------------------------

processOptions ∷ [String] → T (Options, String)
processOptions argv =
  case getOpt Permute options argv of
    ([], [], []) → return (defaultOptions { optHelp = True } , [])

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
