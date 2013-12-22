------------------------------------------------------------------------------
-- The program to sort a list is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of a program which sorts a list
-- by converting it into an ordered tree and then back to a list
-- (Burstall, 1969, p. 45).

module FOTC.Program.SortList.CorrectnessProofATP where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Program.SortList.PropertiesATP
open import FOTC.Program.SortList.Properties.Totality.TreeATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Main theorem: The sort program generates an ordered list.
postulate sortCorrect : ∀ {is} → ListN is → OrdList (sort is)
{-# ATP prove sortCorrect flatten-OrdList makeTree-Tree makeTree-OrdTree #-}

------------------------------------------------------------------------------
-- References
--
-- Burstall, R. M. (1969). Proving properties of programs by
-- structural induction. In: The Computer Journal 12.1, pp. 41–48.
