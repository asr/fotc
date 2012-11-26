module CombiningProofs.Eta where

postulate
  D   : Set
  ∃   : (A : D → Set) → Set
  _≡_ : D → D → Set

syntax ∃ (λ x → e) = ∃[ x ] e

postulate
  t₁ : ∀ d → ∃[ e ] d ≡ e
  t₂ : ∀ d → ∃ (_≡_ d)
