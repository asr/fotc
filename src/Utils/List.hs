------------------------------------------------------------------------------
-- |
-- Module      : Utils.List
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities on lists.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.List ( duplicatesElements, nonDuplicate ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.List ( nub )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

#include "../undefined.h"

------------------------------------------------------------------------------
-- | Return 'True' if the elements of a list occur in ascending order.
isSorted ∷ (Ord a) ⇒ [a] → Bool
isSorted []           = True
isSorted [_]          = True
isSorted (x : y : xs) = x <= y && isSorted (y : xs)

-- | Return 'True' if there are not duplicate elements in the list.
nonDuplicate ∷ Eq a ⇒ [a] → Bool
nonDuplicate xs = xs == nub xs

-- | Return the duplicates elements of an ordered list.
duplicatesElements ∷ Ord a ⇒ [a] → [a]
duplicatesElements zs =
  if isSorted zs then nub (helper zs) else __IMPOSSIBLE__
  where
  helper ∷ Eq a ⇒ [a] → [a]
  helper []           = []
  helper [_]          = []
  helper (x : y : xs) = if x == y then x : helper (y : xs) else helper (y : xs)
