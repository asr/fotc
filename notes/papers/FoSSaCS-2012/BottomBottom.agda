-- Tested on 08 December 2011.

module BottomBottom where

open import Common.Universe
open import Common.Data.Empty
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.Inductive

postulate
  bot₁ : ⊥
  bot₂ : ⊥
{-# ATP prove bot₁ bot₂ #-}
{-# ATP prove bot₂ bot₁ #-}

-- $ agda2atp -isrc -inotes/papers/FoSSaCS-2012/  notes/papers/FoSSaCS-2012/BottomBottom.agda
-- Proving the conjecture in /tmp/BottomBottom.bot1_12.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom.bot1_12.tptp
-- Proving the conjecture in /tmp/BottomBottom.bot2_13.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom.bot2_13.tptp

