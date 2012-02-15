------------------------------------------------------------------------------
-- Properties related with the group commutator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator.PropertiesI where

open import GroupTheory.Base
open import GroupTheory.Commutator
open import GroupTheory.PropertiesI
open import GroupTheory.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- From: A. G. Kurosh. The Theory of Groups, vol. 1. Chelsea Publising
-- Company, 2nd edition, 1960. p. 99.
commutatorInverse : ∀ a b → ⟦ a , b ⟧ · ⟦ b , a ⟧ ≡ ε
commutatorInverse a b =
  a ⁻¹ · b ⁻¹ · a · b · (b ⁻¹ · a ⁻¹ · b · a)
    ≡⟨ assoc (a ⁻¹ · b ⁻¹ · a) b (b ⁻¹ · a ⁻¹ · b · a) ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · b · a))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · b · a)) ≡
                    a ⁻¹ · b ⁻¹ · a · (b · t))
             (assoc (b ⁻¹ · a ⁻¹) b a)
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · (b · a)))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · a ⁻¹ · (b · a))) ≡
                    a ⁻¹ · b ⁻¹ · a · (b · t))
             (assoc (b ⁻¹) (a ⁻¹) (b · a))
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · (a ⁻¹ · (b · a))))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · a · (b · (b ⁻¹ · (a ⁻¹ · (b · a)))) ≡
                    a ⁻¹ · b ⁻¹ · a · t)
             (sym (assoc b (b ⁻¹) (a ⁻¹ · (b · a))))
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · a · (b · b ⁻¹ · (a ⁻¹ · (b · a)))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · a · (b · b ⁻¹ · (a ⁻¹ · (b · a))) ≡
                    a ⁻¹ · b ⁻¹ · a · (t · (a ⁻¹ · (b · a))))
             (rightInverse b)
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · a · (ε · (a ⁻¹ · (b · a)))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · a · (ε · (a ⁻¹ · (b · a))) ≡
                    a ⁻¹ · b ⁻¹ · a · t)
             (leftIdentity (a ⁻¹ · (b · a)))
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · a · (a ⁻¹ · (b · a))
    ≡⟨ assoc (a ⁻¹ · b ⁻¹) a (a ⁻¹ · (b · a)) ⟩
  a ⁻¹ · b ⁻¹ · (a · (a ⁻¹ · (b · a)))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · (a · (a ⁻¹ · (b · a))) ≡
                    a ⁻¹ · b ⁻¹ · t)
             (sym (assoc a (a ⁻¹) (b · a)))
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · (a · a ⁻¹ · (b · a))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · (a · a ⁻¹ · (b · a)) ≡
                    a ⁻¹ · b ⁻¹ · (t · (b · a)))
             (rightInverse a)
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · (ε · (b · a))
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · (ε · (b · a)) ≡
                    a ⁻¹ · b ⁻¹ · t)
             (leftIdentity (b · a))
             refl
    ⟩
  a ⁻¹ · b ⁻¹ · (b · a)
    ≡⟨ assoc (a ⁻¹) (b ⁻¹) (b · a) ⟩
  a ⁻¹ · (b ⁻¹ · (b · a))
     ≡⟨ ·-cong refl (sym (assoc (b ⁻¹) b a)) ⟩
  a ⁻¹ · ((b ⁻¹ · b) · a)
     ≡⟨ ·-cong refl (·-cong (leftInverse b) refl) ⟩
  a ⁻¹ · (ε · a)
     ≡⟨ ·-cong refl (leftIdentity a) ⟩
  a ⁻¹ · a
     ≡⟨ leftInverse a ⟩
  ε ∎
