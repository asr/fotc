{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombiningProofs.Eta where

infix 7 _≡_
infix 5 ∃

postulate
  D   : Set
  ∃   : (A : D → Set) → Set
  _≡_ : D → D → Set

syntax ∃ (λ x → e) = ∃[ x ] e

postulate
  t₁ : ∀ d → ∃[ e ] d ≡ e
  t₂ : ∀ d → ∃ (_≡_ d)
