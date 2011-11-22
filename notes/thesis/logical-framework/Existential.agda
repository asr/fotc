module Existential where

postulate
  D       : Set
  ∃       : (A : D → Set) → Set
  _,_     : {A : D → Set}(d : D) → A d → ∃ A
  ∃-proj₁ : {A : D → Set} → ∃ A → D
  ∃-proj₂ : {A : D → Set}(p : ∃ A) → A (∃-proj₁ p)
