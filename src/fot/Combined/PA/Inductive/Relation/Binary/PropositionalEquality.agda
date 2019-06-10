------------------------------------------------------------------------------
-- Propositional equality on inductive PA
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This file contains some definitions which are reexported by
-- Combined.PA.Inductive.Base.

module Combined.PA.Inductive.Relation.Binary.PropositionalEquality where

open import Common.FOL.FOL using ( ¬_ )
open import Combined.PA.Inductive.Base.Core

infix 4 _≡_ _≢_

------------------------------------------------------------------------------
-- The identity type on PA.
data _≡_ (x : ℕ) : ℕ → Set where
  refl : x ≡ x

-- Inequality.
_≢_ : ℕ → ℕ → Set
x ≢ y = ¬ x ≡ y
{-# ATP definition _≢_ #-}

-- Identity properties

sym : ∀ {x y} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans refl h = h

subst : (A : ℕ → Set) → ∀ {x y} → x ≡ y → A x → A y
subst A refl Ax = Ax

cong : (f : ℕ → ℕ) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : (f : ℕ → ℕ → ℕ) → ∀ {x x' y y'} → x ≡ y → x' ≡ y' → f x x' ≡ f y y'
cong₂ f refl refl = refl
