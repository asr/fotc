------------------------------------------------------------------------------
-- Properties related with the group commutator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.GroupTheory.Commutator.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.GroupTheory.Base
open import Interactive.GroupTheory.Commutator
open import Interactive.GroupTheory.Properties

------------------------------------------------------------------------------
-- Kurosh (1960), p. 99.
commutatorInverse : ∀ a b → [ a , b ] · [ b , a ] ≡ ε
commutatorInverse a b =
  a ⁻¹ · b ⁻¹ · a · b · (b ⁻¹ · a ⁻¹ · b · a)
    ≡⟨ assoc (a ⁻¹ · b ⁻¹ · a) b (b ⁻¹ · a ⁻¹ · b · a) ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · b · a))
    ≡⟨ ·-rightCong (·-rightCong (assoc (b ⁻¹ · a ⁻¹) b a)) ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · (b · a)))
    ≡⟨ ·-rightCong (·-rightCong (assoc (b ⁻¹) (a ⁻¹) (b · a))) ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · (a ⁻¹ · (b · a))))
    ≡⟨ ·-rightCong (sym (assoc b (b ⁻¹) (a ⁻¹ · (b · a)))) ⟩
  a ⁻¹ · b ⁻¹ · a · (b · b ⁻¹ · (a ⁻¹ · (b · a)))
    ≡⟨ ·-rightCong (·-leftCong (rightInverse b)) ⟩
  a ⁻¹ · b ⁻¹ · a · (ε · (a ⁻¹ · (b · a)))
    ≡⟨ ·-rightCong (leftIdentity (a ⁻¹ · (b · a))) ⟩
  a ⁻¹ · b ⁻¹ · a · (a ⁻¹ · (b · a))
    ≡⟨ assoc (a ⁻¹ · b ⁻¹) a (a ⁻¹ · (b · a)) ⟩
  a ⁻¹ · b ⁻¹ · (a · (a ⁻¹ · (b · a)))
    ≡⟨ ·-rightCong (sym (assoc a (a ⁻¹) (b · a))) ⟩
  a ⁻¹ · b ⁻¹ · (a · a ⁻¹ · (b · a))
    ≡⟨ ·-rightCong (·-leftCong (rightInverse a)) ⟩
  a ⁻¹ · b ⁻¹ · (ε · (b · a))
    ≡⟨ ·-rightCong (leftIdentity (b · a)) ⟩
  a ⁻¹ · b ⁻¹ · (b · a)
    ≡⟨ assoc (a ⁻¹) (b ⁻¹) (b · a) ⟩
  a ⁻¹ · (b ⁻¹ · (b · a))
     ≡⟨ ·-rightCong (sym (assoc (b ⁻¹) b a)) ⟩
  a ⁻¹ · ((b ⁻¹ · b) · a)
     ≡⟨ ·-rightCong (·-leftCong (leftInverse b)) ⟩
  a ⁻¹ · (ε · a)
     ≡⟨ ·-rightCong (leftIdentity a) ⟩
  a ⁻¹ · a
     ≡⟨ leftInverse a ⟩
  ε ∎

------------------------------------------------------------------------------
-- References
--
-- Kurosh, A. G. (1960). The Theory of Groups. 2nd
-- ed. Vol. 1. Translated and edited by K. A. Hirsch. Chelsea
-- Publising Company.
