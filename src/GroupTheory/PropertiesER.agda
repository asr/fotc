------------------------------------------------------------------------------
-- Group theory properties (using equational reasoning)
------------------------------------------------------------------------------

module GroupTheory.PropertiesER where

open import GroupTheory.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

------------------------------------------------------------------------------

leftCancellation : (x y z : G) → x ∙ y ≡ x ∙ z → y ≡ z
leftCancellation x y z x∙y≡x∙z =
  begin
    y              ≡⟨ sym (leftIdentity y) ⟩
    ε ∙ y          ≡⟨ subst (λ t → ε ∙ y ≡ t ∙ y) (sym (leftInverse x)) refl ⟩
    x ⁻¹ ∙ x ∙ y   ≡⟨ associativity (x ⁻¹) x y ⟩
    x ⁻¹ ∙ (x ∙ y) ≡⟨ subst (λ t → x ⁻¹ ∙ (x ∙ y) ≡ x ⁻¹ ∙ t) x∙y≡x∙z refl ⟩
    x ⁻¹ ∙ (x ∙ z) ≡⟨ sym (associativity (x ⁻¹) x z) ⟩
    x ⁻¹ ∙ x ∙ z   ≡⟨ subst (λ t → x ⁻¹ ∙ x ∙ z ≡ t ∙ z) (leftInverse x) refl ⟩
    ε ∙ z          ≡⟨ leftIdentity z ⟩
    z
  ∎
