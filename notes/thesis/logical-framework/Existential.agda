module Existential where

postulate
  D       : Set
  ∃       : (P : D → Set) → Set
  _,_     : {P : D → Set}(d : D) → P d → ∃ P
  ∃-proj₁ : {P : D → Set} → ∃ P → D
  ∃-proj₂ : {P : D → Set}(p : ∃ P) → P (∃-proj₁ p)

postulate P : D → D → Set

∃∀ : (∃ λ x → ∀ y → P x y) → ∀ y → ∃ λ x → P x y
∃∀ h y = ∃-proj₁ h , (∃-proj₂ h) y
