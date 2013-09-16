------------------------------------------------------------------------------
-- Propositional equality on inductive PA
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This file contains some definitions which are reexported by
-- PA.Inductive.Base.

module PA.Inductive.Relation.Binary.PropositionalEquality where

open import Common.FOL.FOL using ( ¬_ )
open import PA.Inductive.Base.Core

-- We add 3 to the fixities of the standard library.
infix 7 _≡_ _≢_

------------------------------------------------------------------------------
-- The identity type on PA.
data _≡_ (x : M) : M → Set where
  refl : x ≡ x

-- Inequality.
_≢_ : M → M → Set
x ≢ y = ¬ x ≡ y
{-# ATP definition _≢_ #-}

-- Identity properties

sym : ∀ {x y} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans refl h = h

subst : (A : M → Set) → ∀ {x y} → x ≡ y → A x → A y
subst A refl Ax = Ax

cong : (f : M → M) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : (f : M → M → M) → ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
        f x₁ x₂ ≡ f y₁ y₂
cong₂ f refl refl = refl
