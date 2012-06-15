{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 15 June 2012.

module BottomBottom where

open import Common.FOL.FOL

postulate bot₁ bot₂ : ⊥
{-# ATP prove bot₁ bot₂ #-}
{-# ATP prove bot₂ bot₁ #-}

-- $ agda2atp -i src -i notes/papers/FoSSaCS-2012/ notes/papers/FoSSaCS-2012/BottomBottom.agda
-- Proving the conjecture in /tmp/BottomBottom.bot1_7.tptp ...
-- E 1.5 Pussimbing proved the conjecture in /tmp/BottomBottom.bot1_7.tptp
-- Proving the conjecture in /tmp/BottomBottom.bot2_7.tptp ...
-- E 1.5 Pussimbing proved the conjecture in /tmp/BottomBottom.bot2_7.tptp
