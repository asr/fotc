-- Tested with FOT on 16 February 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Existential where

module LF where
  postulate
    D       : Set
    ∃       : (A : D → Set) → Set
    _,_     : {A : D → Set}(x : D) → A x → ∃ A
    ∃-proj₁ : {A : D → Set} → ∃ A → D
    ∃-proj₂ : {A : D → Set}(a : ∃ A) → A (∃-proj₁ p)

  syntax ∃ (λ x → e) = ∃[ x ] e

  postulate A : D → D → Set

  ∃∀ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
  ∃∀ h y = ∃-proj₁ h , (∃-proj₂ h) y

module Inductive where

  open import Common.Universe
  open import Common.Data.Product

  postulate A : D → D → Set

  ∃∀-el : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
  ∃∀-el h y = ∃-proj₁ h , (∃-proj₂ h) y

  ∃∀ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
  ∃∀ (x , Ax) y = x , Ax y
