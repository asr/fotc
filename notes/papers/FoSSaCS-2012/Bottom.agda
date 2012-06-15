{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 08 December 2011.

module Bottom where

open import Common.FOL.FOL-Eq

postulate bot : ⊥

postulate
  zero : D
  succ : D → D

postulate false : zero ≡ succ zero
{-# ATP prove false bot #-}

-- $ agda2atp -isrc -inotes/papers/FoSSaCS-2012/  notes/papers/FoSSaCS-2012/Bottom.agda
-- Proving the conjecture in /tmp/Bottom.false_13.tptp ...
-- E 1.5 Pussimbing proved the conjecture in /tmp/Bottom.false_13.tptp
