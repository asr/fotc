------------------------------------------------------------------------------
-- |
-- Module      : Monad.Environment
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Functions for initializing the translation monad environment.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Environment ( env )
where

------------------------------------------------------------------------------
-- Haskell imports

import System.Environment ( getArgs )

------------------------------------------------------------------------------
-- Local imports

import Options  ( Options, processOptions )
import Utils.IO ( die )

------------------------------------------------------------------------------
-- | The environment.
env ∷ IO Options
env = do
  args ← getArgs
  case processOptions args of
    Left err → die err
    Right o  → return o
