-- Tested on 30 November 2011.

module Existential where

postulate
  D       : Set
  ∃       : (P : D → Set) → Set
  _,_     : {P : D → Set}(x : D) → P x → ∃ P
  ∃-proj₁ : {P : D → Set} → ∃ P → D
  ∃-proj₂ : {P : D → Set}(p : ∃ P) → P (∃-proj₁ p)

syntax ∃ (λ x → e) = ∃[ x ] e

postulate P : D → D → Set

∃∀ : ∃[ x ](∀ y → P x y) → ∀ y → ∃[ x ] P x y
∃∀ h y = ∃-proj₁ h , (∃-proj₂ h) y
