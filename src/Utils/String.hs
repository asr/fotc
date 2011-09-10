{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- |
-- Module      : Utils.String
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'String'.
------------------------------------------------------------------------------

module Utils.String ( replace ) where

------------------------------------------------------------------------------
-- | Replace the first argument by the second one on the string.
replace ∷ Char → Char → String → String
replace _   _    []       = []
replace src dest (x : xs) =
  if src == x then dest : replace src dest xs else x : replace src dest xs
