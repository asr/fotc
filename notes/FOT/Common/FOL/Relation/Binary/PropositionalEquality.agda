------------------------------------------------------------------------------
-- Postulated propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 11 June 2012.

module FOT.Common.FOL.Relation.Binary.PropositionalEquality where

-- We add 3 to the fixities of the standard library.
infix 7 _≡_

------------------------------------------------------------------------------

-- The identity type on the universe of discourse.
postulate
  D    : Set
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
