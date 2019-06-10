------------------------------------------------------------------------------
-- The program to sort a list is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module prove the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall 1969, p. 45).

module Interactive.FOTC.Program.SortList.CorrectnessProof where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Program.SortList.Properties
open import Interactive.FOTC.Program.SortList.Properties.Totality.Tree
open import Interactive.FOTC.Program.SortList.SortList

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
