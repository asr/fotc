------------------------------------------------------------------------------
-- Utilities on lists
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.List ( duplicatesElements, myShowList, nonDuplicate ) where

-- Haskell imports
import Data.List ( nub )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
#include "../undefined.h"

------------------------------------------------------------------------------
-- | The function 'isSorted' returns 'True' if the elements of a list
-- occur in ascending order.
isSorted ∷ (Ord a) ⇒ [a] → Bool
isSorted []           = True
isSorted [_]          = True
isSorted (x : y : xs) = x <= y && isSorted (y : xs)

-- | The function 'nonDuplicate' returns 'True' if there are not
-- duplicate elements in the list.
nonDuplicate ∷ Eq a ⇒ [a] → Bool
nonDuplicate xs = xs == nub xs

-- | The function 'duplicatesElements' returns the duplicates elements
-- of an ordered list.
duplicatesElements ∷ Ord a ⇒ [a] → [a]
duplicatesElements zs =
  if isSorted zs then nub (helper zs) else __IMPOSSIBLE__
  where
    helper ∷ Eq a ⇒ [a] → [a]
    helper []           = []
    helper [_]          = []
    helper (x : y : xs) = if x == y
                          then x : helper (y : xs)
                          else helper (y : xs)

-- | Show version on lists where the elements are separated by newline
-- characters.
myShowList ∷ Show a => [a] → String
myShowList []       = []
myShowList (x : xs) = show x ++ "\n" ++ myShowList xs
