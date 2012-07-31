------------------------------------------------------------------------------
-- |
-- Module      : Utils.Monad
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Monads utilities
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Monad ( pair ) where

------------------------------------------------------------------------------
-- | Sequences a pair of monadic computations.
pair ∷ Monad m ⇒ m a → m b → m (a,b)
pair mx my = mx >>= \x → my >>= \y → return (x,y)
