{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.Common.FOL.Existential.Syntax where

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Relation.Binary.Core).
infix 7 _≡_

postulate
  D    : Set
  _≡_  : D → D → Set
  refl : ∀ {d} → d ≡ d
  d    : D

module ∃₁ where

  -- We add 3 to the fixities of the Agda standard library 0.8.1 (see
  -- Data/Product.agda, Data/Sum.agda and Relation/Nullary/Core.agda).
  infixr 7 _,_
  infix  5 ∃

  data ∃ (P : D → Set) : Set where
    _,_ : (x : D) → P x → ∃ P

  syntax ∃ (λ x → e)  = ∃[ x ] e

  t₁ : ∃ λ x → x ≡ x
  t₁ = d , refl

  t₂ : ∃[ x ] x ≡ x
  t₂ = d , refl

  t₃ : ∃ λ x → ∃ λ y → x ≡ y
  t₃ = d , d , refl

  t₄ : ∃[ x ] ∃[ y ] x ≡ y
  t₄ = d , d ,  refl

module ∃₂ where
  infixr 7 _,_,_

  data ∃₂ (P : D → D → Set) : Set where
    _,_,_ : (x y : D) → P x y → ∃₂ P

  -- Agda issue: 536
  -- syntax ∃₂ (λ x y → e) = ∃₂[ x , y ] e

  t₁ : ∃₂ λ x y → x ≡ y
  t₁ = d , d , refl
