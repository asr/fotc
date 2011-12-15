-- Tested with Agda 2.3.1 on 15 December 2011.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Existential where

module LF where
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

module Inductive where

  open import Common.Universe
  open import Common.Data.Product

  postulate P : D → D → Set

  ∃∀-el : ∃[ x ](∀ y → P x y) → ∀ y → ∃[ x ] P x y
  ∃∀-el h y = ∃-proj₁ h , (∃-proj₂ h) y

  ∃∀ : ∃[ x ](∀ y → P x y) → ∀ y → ∃[ x ] P x y
  ∃∀ (x , Px) y = x , Px y
