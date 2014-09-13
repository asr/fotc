------------------------------------------------------------------------------
-- Propositional equality without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module
  FOT.Common.FOL.Relation.Binary.PropositionalEquality.NoPatternMatchingOnRefl
  where

open import Common.FOL.FOL using ( D )

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Relation/Binary/Core.agda).
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
sym {x} h = subst (λ y' → y' ≡ x) h refl

trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans {x} h₁ h₂ = subst (_≡_ x) h₂ h₁

trans₂ : ∀ {w x y z} → w ≡ x → x ≡ y → y ≡ z → w ≡ z
trans₂ h₁ h₂ h₃ = trans (trans h₁ h₂) h₃

subst₂ : (A : D → D → Set) → ∀ {x₁ x₂ y₁ y₂} →
         x₁ ≡ y₁ → x₂ ≡ y₂ →
         A x₁ x₂ →
         A y₁ y₂
subst₂ A {x₁} {x₂} {y₁} {y₂} h₁ h₂ h₃ =
  subst (λ y₁' → A y₁' y₂) h₁ (subst (A x₁) h₂ h₃)

cong : (f : D → D) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f {x} h = subst (λ x' → f x ≡ f x') h refl

cong₂ : (f : D → D → D) → ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ →
        f x₁ x₂ ≡ f y₁ y₂
cong₂ f {x₁} {x₂} {y₁} {y₂} h₁ h₂ =
  subst (λ x₁' → f x₁ x₂ ≡ f x₁' y₂)
        h₁
        (subst (λ x₂' → f x₁ x₂ ≡ f x₁ x₂') h₂ refl)
