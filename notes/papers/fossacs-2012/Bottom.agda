{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Bottom where

open import Common.FOL.FOL-Eq

postulate bot : ⊥

postulate
  zero : D
  succ : D → D

postulate false : zero ≡ succ zero
{-# ATP prove false bot #-}

-- $ apia -isrc -inotes/papers/FoSSaCS-2012/  notes/papers/FoSSaCS-2012/Bottom.agda
-- Proving the conjecture in /tmp/Bottom/16-false.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/Bottom/16-false.tptp
