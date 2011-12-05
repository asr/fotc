------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

-- This module is re-exported by (some) "base" modules.

module Common.Relation.Binary.PropositionalEquality where

open import Common.Universe using ( D )

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
  trans refl y≡z = y≡z

  trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
  trans₂ refl refl y≡z = y≡z

  subst : ∀ (P : D → Set) {x y} → x ≡ y → P x → P y
  subst P refl Px = Px

  subst₂ : ∀ (P : D → D → Set) {x₁ x₂ y₁ y₂} →
           x₁ ≡ y₁ → x₂ ≡ y₂ →
           P x₁ x₂ →
           P y₁ y₂
  subst₂ P refl refl Pxs = Pxs

  subst₃ : ∀ (P : D → D → D → Set) {x₁ x₂ x₃ y₁ y₂ y₃} →
           x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ →
           P x₁ x₂ x₃ →
           P y₁ y₂ y₃
  subst₃ P refl refl refl Pxs = Pxs

  subst₄ : ∀ (P : D → D → D → D → Set) {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄} →
           x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ →
           P x₁ x₂ x₃ x₄ →
           P y₁ y₂ y₃ y₄
  subst₄ P refl refl refl refl Pxs = Pxs

  cong : ∀ (f : D → D) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong₂ : ∀ (f : D → D → D) {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
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
    J    : ∀ (P : D → Set) {x y} → x ≡ y → P x → P y

  -- Identity properties

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} x≡y = J (λ y' → y' ≡ x) x≡y refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} {z = z} x≡y = J (λ y' → y' ≡ z → x ≡ z) x≡y (λ pr → pr)

  trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
  trans₂ w≡x x≡y y≡z = trans (trans w≡x x≡y) y≡z

  subst : ∀ (P : D → Set) {x y} → x ≡ y → P x → P y
  subst = J

  subst₂ : ∀ (P : D → D → Set) {x₁ x₂ y₁ y₂} →
           x₁ ≡ y₁ → x₂ ≡ y₂ →
           P x₁ x₂ →
           P y₁ y₂
  subst₂ P {x₁} {x₂} {y₁} {y₂} x₁≡y₁ x₂≡y₂ Px₁x₂ =
    subst (λ y₁' → P y₁' y₂)
          x₁≡y₁
          (subst (λ y₂' → P x₁ y₂') x₂≡y₂ Px₁x₂)

  cong : ∀ (f : D → D) {x y} → x ≡ y → f x ≡ f y
  cong f {x} x≡y = subst (λ x' → f x ≡ f x') x≡y refl

  cong₂ : ∀ (f : D → D → D) {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
          f x₁ x₂ ≡ f y₁ y₂
  cong₂ f {x₁} {x₂} {y₁} {y₂} x₁≡y₁ x₂≡y₂ =
    subst (λ x₁' → f x₁ x₂ ≡ f x₁' y₂)
          x₁≡y₁
          (subst (λ x₂' → f x₁ x₂ ≡ f x₁ x₂') x₂≡y₂ refl)
