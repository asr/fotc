------------------------------------------------------------------------------
-- The program to sort a list is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module prove the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall 1969, p. 45).

module FOTC.Program.SortList.CorrectnessProofI where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Program.SortList.PropertiesI
open import FOTC.Program.SortList.Properties.Totality.TreeI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Main theorem: The sort program generates an ordered list.
sortCorrect : ∀ {is} → ListN is → OrdList (sort is)
sortCorrect {is} Lis =
  subst OrdList
        refl
        (flatten-OrdList (makeTree-Tree Lis) (makeTree-OrdTree Lis))

------------------------------------------------------------------------------
-- References
--
-- Burstall, R. M. (1969). Proving properties of programs by
-- structural induction. The Computer Journal 12.1, pp. 41–48.
