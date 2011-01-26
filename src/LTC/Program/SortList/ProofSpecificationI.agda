------------------------------------------------------------------------------
-- The program to sort a list satisfies the specification
------------------------------------------------------------------------------

-- This module prove the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, pp. 45).

-- R. M. Burstall. Proving properties of programs by structural
-- induction. The Computer Journal, 12(1):41–48, 1969.

module LTC.Program.SortList.ProofSpecificationI where

open import LTC.Base

open import LTC.Data.Nat.List.Type

open import LTC.Program.SortList.PropertiesI
open import LTC.Program.SortList.Properties.Closures.TreeI
open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Main theorem: The sort program generates a ordered list.
sort-OrdList : ∀ {is} → ListN is → OrdList (sort is)
sort-OrdList {is} Lis =
  subst (λ t → OrdList t)
        refl
        (flatten-OrdList (makeTree-Tree Lis) (makeTree-OrdTree Lis))
