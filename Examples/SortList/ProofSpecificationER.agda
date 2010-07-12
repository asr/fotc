------------------------------------------------------------------------------
-- The program to sort a list satisfies the specification
-- (using equational reasoning)
------------------------------------------------------------------------------

-- This module prove the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, pp. 45).

-- R. M. Burstall. Proving properties of programs by structural
-- induction. The Computer Journal, 12(1):41–48, 1969.

module Examples.SortList.ProofSpecificationER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.Closures.ListOrdER using ( flatten-ListOrd )
open import Examples.SortList.Closures.TreeER using ( makeTree-Tree )
open import Examples.SortList.Closures.TreeOrdER using ( makeTree-TreeOrd )
open import Examples.SortList.SortList

open import LTC.Data.Nat.List

------------------------------------------------------------------------------

sort-ListOrd : {is : D} → List is → ListOrd (sort is)
sort-ListOrd {is} Lis =
  subst (λ t → ListOrd t)
        refl
        (flatten-ListOrd (makeTree-Tree Lis) (makeTree-TreeOrd Lis))
