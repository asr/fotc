------------------------------------------------------------------------------
-- |
-- Module      : Utils.String
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'String'.
------------------------------------------------------------------------------

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.String ( replace ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Char   ( Char )
import Data.Eq     ( Eq((==)) )
import Data.String ( String )

------------------------------------------------------------------------------
-- | Replace the first argument by the second one on the string.
replace ∷ Char → Char → String → String
replace _   _    []       = []
replace src dest (x : xs) =
  if src == x then dest : replace src dest xs else x : replace src dest xs
