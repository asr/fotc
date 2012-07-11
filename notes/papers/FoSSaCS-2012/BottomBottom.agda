{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 11 July 2012.

module BottomBottom where

open import Common.FOL.FOL

postulate bot₁ bot₂ : ⊥
{-# ATP prove bot₁ bot₂ #-}
{-# ATP prove bot₂ bot₁ #-}

-- $ agda2atp -i src -i notes/papers/FoSSaCS-2012/ notes/papers/FoSSaCS-2012/BottomBottom.agda
-- Proving the conjecture in /tmp/BottomBottom/10-bot1.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom/10-bot1.tptp
-- Proving the conjecture in /tmp/BottomBottom/10-bot2.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/BottomBottom/10-bot2.tptp
