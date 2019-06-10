------------------------------------------------------------------------------
-- The program to sort a list is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, p. 45).

module Combined.FOTC.Program.SortList.CorrectnessProof where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.List.Type
open import Combined.FOTC.Program.SortList.Properties
open import Combined.FOTC.Program.SortList.Properties.Totality.Tree
open import Combined.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Main theorem: The sort program generates an ordered list.
postulate sortCorrect : ∀ {is} → ListN is → OrdList (sort is)
{-# ATP prove sortCorrect flatten-OrdList makeTree-Tree makeTree-OrdTree #-}

------------------------------------------------------------------------------
-- References
--
-- Burstall, R. M. (1969). Proving properties of programs by
-- structural induction. The Computer Journal 12.1, pp. 41–48.
