------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module is re-exported by (some) "base" modules.

module Common.FOL.Relation.Binary.PropositionalEquality where

open import Common.FOL.FOL using ( D )

-- We add 3 to the fixities of the standard library.
infix 7 _≡_

------------------------------------------------------------------------------
-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Elimination rule.
subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
subst A refl Ax = Ax

-- Identity properties

sym : ∀ {x y} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans refl h = h

trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
trans₂ refl refl h = h

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
