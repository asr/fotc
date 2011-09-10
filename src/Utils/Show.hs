{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- |
-- Module      : Utils.Show
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'Show'.
------------------------------------------------------------------------------

module Utils.Show ( showListLn, showLn ) where

------------------------------------------------------------------------------

showLn ∷ Show a ⇒ a → String
showLn = (++ "\n") . show

-- | Show version on lists where the elements are separated by newline
-- characters.
showListLn ∷ Show a ⇒ [a] → String
showListLn xs = xs >>= showLn  -- From Autoproc.Procmail.
