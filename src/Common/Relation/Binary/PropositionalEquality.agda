------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

-- This module is re-exported by (some) "base" modules.

module Common.Relation.Binary.PropositionalEquality where

open import Common.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infix 7 _≡_

------------------------------------------------------------------------------
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

subst : ∀ {x y} (P : D → Set) → x ≡ y → P x → P y
subst P refl Px = Px

subst₂ : ∀ {x₁ x₂ y₁ y₂} (P : D → D → Set) →
         x₁ ≡ y₁ → x₂ ≡ y₂ →
         P x₁ x₂ →
         P y₁ y₂
subst₂ P refl refl Pxs = Pxs

subst₃ : ∀ {x₁ x₂ x₃ y₁ y₂ y₃} (P : D → D → D → Set) →
         x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ →
         P x₁ x₂ x₃ →
         P y₁ y₂ y₃
subst₃ P refl refl refl Pxs = Pxs

subst₄ : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄} (P : D → D → D → D → Set) →
         x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ →
         P x₁ x₂ x₃ x₄ →
         P y₁ y₂ y₃ y₄
subst₄ P refl refl refl refl Pxs = Pxs

cong : ∀ {x y} (f : D → D) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {x₁ x₂ y₁ y₂} (f : D → D → D) → x₁ ≡ y₁ → x₂ ≡ y₂ → f x₁ x₂ ≡ f y₁ y₂
cong₂ f refl refl = refl
