------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module is re-exported by (some) "base" modules.

module Common.FOL.Relation.Binary.PropositionalEquality where

open import Common.FOL.FOL using ( D )

------------------------------------------------------------------------------
-- The propositional equality via pattern matching.

module Inductive where
  -- We add 3 to the fixities of the standard library.
  infix 7 _≡_

  -- The identity type on the universe of discourse.
  data _≡_ (x : D) : D → Set where
    refl : x ≡ x

  -- Identity properties

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans refl h = h

  trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
  trans₂ refl refl h = h

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A refl Ax = Ax

  subst₂ : (A : D → D → Set) → ∀ {x₁ x₂ y₁ y₂} →
           x₁ ≡ y₁ → x₂ ≡ y₂ →
           A x₁ x₂ →
           A y₁ y₂
  subst₂ A refl refl Axs = Axs

  subst₃ : (A : D → D → D → Set) → ∀ {x₁ x₂ x₃ y₁ y₂ y₃} →
           x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ →
           A x₁ x₂ x₃ →
           A y₁ y₂ y₃
  subst₃ A refl refl refl Axs = Axs

  subst₄ : (A : D → D → D → D → Set) → ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄} →
           x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ →
           A x₁ x₂ x₃ x₄ →
           A y₁ y₂ y₃ y₄
  subst₄ A refl refl refl refl Axs = Axs

  cong : (f : D → D) → ∀ {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong₂ : (f : D → D → D) → ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
          f x₁ x₂ ≡ f y₁ y₂
  cong₂ f refl refl = refl

------------------------------------------------------------------------------
-- The propositional equality via its induction principle.

module NonInductive where

  -- We add 3 to the fixities of the standard library.
  infix 7 _≡_

  -- The identity type on the universe of discourse.
  postulate
    _≡_  : D → D → Set
    refl : ∀ {x} → x ≡ x
    J    : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y

  -- Identity properties

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} h = J (λ y' → y' ≡ x) h refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} h₁ h₂ = J (λ y' → x ≡ y') h₂ h₁

  trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
  trans₂ h₁ h₂ h₃ = trans (trans h₁ h₂) h₃

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst = J

  subst₂ : (A : D → D → Set) → ∀ {x₁ x₂ y₁ y₂} →
           x₁ ≡ y₁ → x₂ ≡ y₂ →
           A x₁ x₂ →
           A y₁ y₂
  subst₂ A {x₁} {x₂} {y₁} {y₂} h₁ h₂ h₃ =
    subst (λ y₁' → A y₁' y₂) h₁ (subst (λ y₂' → A x₁ y₂') h₂ h₃)

  cong : (f : D → D) → ∀ {x y} → x ≡ y → f x ≡ f y
  cong f {x} h = subst (λ x' → f x ≡ f x') h refl

  cong₂ : (f : D → D → D) → ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
          f x₁ x₂ ≡ f y₁ y₂
  cong₂ f {x₁} {x₂} {y₁} {y₂} h₁ h₂ =
    subst (λ x₁' → f x₁ x₂ ≡ f x₁' y₂)
          h₁
          (subst (λ x₂' → f x₁ x₂ ≡ f x₁ x₂') h₂ refl)
