module Existential where

postulate
  D       : Set
  ∃       : (P : D → Set) → Set
  _,_     : {P : D → Set}(d : D) → P d → ∃ P
  ∃-proj₁ : {P : D → Set} → ∃ P → D
  ∃-proj₂ : {P : D → Set}(p : ∃ P) → P (∃-proj₁ p)
