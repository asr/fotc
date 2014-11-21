------------------------------------------------------------------------------
-- Discussion about the inductive approach
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Peter: If you take away the proof objects (as you do when you go to
-- predicate logic) the K axiom doesn't give you any extra power.

module FOT.FOTC.InductiveApproach.ProofTerm where

open import FOTC.Base

------------------------------------------------------------------------------

foo : (∃ λ x → ∃ λ y → x ≡ y) → (∃ λ x → ∃ λ y → y ≡ x)
foo (x , .x , refl) = x , x , refl
