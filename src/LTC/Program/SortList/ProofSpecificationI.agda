------------------------------------------------------------------------------
-- The program to sort a list satisfies the specification (using
-- equational reasoning)
------------------------------------------------------------------------------

-- This module prove the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, pp. 45).

-- R. M. Burstall. Proving properties of programs by structural
-- induction. The Computer Journal, 12(1):41–48, 1969.

module LTC.Program.SortList.ProofSpecificationI where

open import LTC.Base

open import LTC.Data.Nat.List.Type
  using ( ListN  -- The LTC list of natural numbers type.
        )

open import LTC.Program.SortList.Closures.ListOrdI using ( flatten-ListOrd )
open import LTC.Program.SortList.Closures.TreeI using ( makeTree-Tree )
open import LTC.Program.SortList.Closures.TreeOrdI using ( makeTree-TreeOrd )
open import LTC.Program.SortList.SortList using ( ListOrd ; sort )

-- TODO: These files are included but at the moment they are not requeried.
open import LTC.Program.SortList.Closures.ListI
open import LTC.Program.SortList.PropertiesI

------------------------------------------------------------------------------
-- The sort program generates a ordered list.
sort-ListOrd : {is : D} → ListN is → ListOrd (sort is)
sort-ListOrd {is} Lis =
  subst (λ t → ListOrd t)
        refl
        (flatten-ListOrd (makeTree-Tree Lis) (makeTree-TreeOrd Lis))
