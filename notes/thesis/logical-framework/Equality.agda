{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Equality where

module LF where
  postulate
    D     : Set
    _≡_   : D → D → Set
    refl  : ∀ {x} → x ≡ x
    subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} h = subst (λ t → t ≡ x) h refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} h₁ h₂ = subst (_≡_ x) h₂ h₁

module Inductive where

  open import Common.FOL.FOL-Eq
  open import Common.FOL.Relation.Binary.EqReasoning

  sym-er : ∀ {x y} → x ≡ y → y ≡ x
  sym-er {x} h = subst (λ t → t ≡ x) h refl

  trans-er : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans-er {x} h₁ h₂ = subst (_≡_ x) h₂ h₁

  -- NB. The proofs of sym and trans by pattern matching are in the
  -- module Common.FOL.Relation.Binary.PropositionalEquality.
