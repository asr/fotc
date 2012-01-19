-- Tested on 08 December 2011.

module BottomBottom where

open import Common.Universe
open import Common.Data.Empty

postulate bot₁ bot₂ : ⊥
{-# ATP prove bot₁ bot₂ #-}
{-# ATP prove bot₂ bot₁ #-}

-- $ agda2atp -i src -i notes/papers/FoSSaCS-2012/ notes/papers/FoSSaCS-2012/BottomBottom.agda
-- Proving the conjecture in /tmp/BottomBottom.bot1_8.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom.bot1_8.tptp
-- Proving the conjecture in /tmp/BottomBottom.bot2_8.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom.bot2_8.tptp
