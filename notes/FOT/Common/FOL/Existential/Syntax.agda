{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.Common.FOL.Existential.Syntax where

postulate
  D    : Set
  _≡_  : D → D → Set
  refl : ∀ {d} → d ≡ d
  d    : D

module ∃₁ where
  infixr 4 _,_

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
  infixr 4 _,_,_

  data ∃₂ (P : D → D → Set) : Set where
    _,_,_ : (x y : D) → P x y → ∃₂ P

  -- Agda issue: 536
  -- syntax ∃₂ (λ x y → e) = ∃₂[ x , y ] e

  t₁ : ∃₂ λ x y → x ≡ y
  t₁ = d , d , refl
