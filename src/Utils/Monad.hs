------------------------------------------------------------------------------
-- |
-- Module      : Utils.Monad
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities on monads.
------------------------------------------------------------------------------

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Monad ( unlessM, whenM ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( Monad((>>=)), unless, when )

import Data.Bool ( Bool )

------------------------------------------------------------------------------
-- | Lifted version of 'when'.
whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM p action = p >>= \b → when b action

-- | Lifted version of 'unless'.
unlessM ∷ Monad m ⇒ m Bool → m () → m ()
unlessM p action = p >>= \b → unless b action
