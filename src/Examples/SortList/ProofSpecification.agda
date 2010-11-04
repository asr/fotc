------------------------------------------------------------------------------
-- The program to sort a list satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, pp. 45).

-- R. M. Burstall. Proving properties of programs by structural
-- induction. The Computer Journal, 12(1):41–48, 1969.

module Examples.SortList.ProofSpecification where

open import LTC.Base

open import Examples.SortList.Closures.ListOrd using ( flatten-ListOrd )
open import Examples.SortList.Closures.Tree using ( makeTree-Tree )
open import Examples.SortList.Closures.TreeOrd using ( makeTree-TreeOrd )
open import Examples.SortList.SortList using ( ListOrd ; sort )

open import LTC.Data.Nat.List.Type using ( ListN )

------------------------------------------------------------------------------
-- The sort program generates an ordered list.
postulate
  sort-ListOrd : {is : D} → ListN is → ListOrd (sort is)
{-# ATP prove sort-ListOrd flatten-ListOrd makeTree-Tree makeTree-TreeOrd #-}
