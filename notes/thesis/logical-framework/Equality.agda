-- Tested with FOT on 02 March 2012.

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
  trans {z = z} h₁ h₂ = subst (λ t → t ≡ z) (sym h₁) h₂

module Inductive where

  import Common.FOL.Relation.Binary.PropositionalEquality
  open module Eq =
    Common.FOL.Relation.Binary.PropositionalEquality.Inductive public

  open import Common.FOL.FOL using ( D )

  sym-er : ∀ {x y} → x ≡ y → y ≡ x
  sym-er {x} h = subst (λ t → t ≡ x) h refl

  trans-er : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans-er {z = z} h₁ h₂ = subst (λ t → t ≡ z) (sym h₁) h₂

  -- NB. The proofs of sym and trans by pattern matching are in the
  -- module Common.FOL.Relation.Binary.PropositionalEquality.
