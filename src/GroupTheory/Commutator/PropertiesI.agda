------------------------------------------------------------------------------
-- Properties related with the commutator operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Commutator.PropertiesI where

open import GroupTheory.Base
open import GroupTheory.Commutator
open import GroupTheory.PropertiesI
open import GroupTheory.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

⟦x,y⟧⟦y,x⟧≡ε : ∀ a b → ⟦ a , b ⟧ · ⟦ b , a ⟧ ≡ ε
⟦x,y⟧⟦y,x⟧≡ε a b =
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
    ≡⟨ subst (λ t → a ⁻¹ · b ⁻¹ · (b · a) ≡ t · (b · a))
             (sym (inverseDistribution b a))
             refl
    ⟩
  (b · a)⁻¹ · (b · a)
     ≡⟨ leftInverse (b · a) ⟩
  ε ∎
