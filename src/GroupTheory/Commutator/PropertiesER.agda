------------------------------------------------------------------------------
-- Properties related with the commutator operation
-- (using equational reasoning)
------------------------------------------------------------------------------

module GroupTheory.Commutator.PropertiesER where

open import GroupTheory.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

open import GroupTheory.Commutator using ( ⟦_,_⟧ )
open import GroupTheory.PropertiesER using ( inverseDistribution )

------------------------------------------------------------------------------

⟦x,y⟧⟦y,x⟧≡ε : ∀ a b → ⟦ a , b ⟧ ∙ ⟦ b , a ⟧ ≡ ε
⟦x,y⟧⟦y,x⟧≡ε a b =
  begin
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ b ∙ (b ⁻¹ ∙ a ⁻¹ ∙ b ∙ a)
      ≡⟨ assoc (a ⁻¹ ∙ b ⁻¹ ∙ a) b (b ⁻¹ ∙ a ⁻¹ ∙ b ∙ a) ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ a ⁻¹ ∙ b ∙ a))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ a ⁻¹ ∙ b ∙ a)) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ t))
               (assoc (b ⁻¹ ∙ a ⁻¹) b a)
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ a ⁻¹ ∙ (b ∙ a)))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ a ⁻¹ ∙ (b ∙ a))) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ t))
               (assoc (b ⁻¹) (a ⁻¹) (b ∙ a))
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ (a ⁻¹ ∙ (b ∙ a))))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ (b ⁻¹ ∙ (a ⁻¹ ∙ (b ∙ a)))) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ a ∙ t)
               (sym (assoc b (b ⁻¹) (a ⁻¹ ∙ (b ∙ a))))
               refl ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ b ⁻¹ ∙ (a ⁻¹ ∙ (b ∙ a)))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (b ∙ b ⁻¹ ∙ (a ⁻¹ ∙ (b ∙ a))) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (t ∙ (a ⁻¹ ∙ (b ∙ a))))
               (rightInverse b)
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (ε ∙ (a ⁻¹ ∙ (b ∙ a)))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (ε ∙ (a ⁻¹ ∙ (b ∙ a))) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ a ∙ t)
               (leftIdentity (a ⁻¹ ∙ (b ∙ a)))
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ a ∙ (a ⁻¹ ∙ (b ∙ a))
      ≡⟨ assoc (a ⁻¹ ∙ b ⁻¹) a (a ⁻¹ ∙ (b ∙ a)) ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ (a ∙ (a ⁻¹ ∙ (b ∙ a)))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ (a ∙ (a ⁻¹ ∙ (b ∙ a))) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ t)
               (sym (assoc a (a ⁻¹) (b ∙ a)))
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ (a ∙ a ⁻¹ ∙ (b ∙ a))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ (a ∙ a ⁻¹ ∙ (b ∙ a)) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ (t ∙ (b ∙ a)))
               (rightInverse a)
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ (ε ∙ (b ∙ a))
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ (ε ∙ (b ∙ a)) ≡
                      a ⁻¹ ∙ b ⁻¹ ∙ t)
               (leftIdentity (b ∙ a))
               refl
      ⟩
    a ⁻¹ ∙ b ⁻¹ ∙ (b ∙ a)
      ≡⟨ subst (λ t → a ⁻¹ ∙ b ⁻¹ ∙ (b ∙ a) ≡ t ∙ (b ∙ a))
               (sym (inverseDistribution b a))
               refl
      ⟩
    (b ∙ a)⁻¹ ∙ (b ∙ a)
      ≡⟨ leftInverse (b ∙ a) ⟩
    ε
  ∎
