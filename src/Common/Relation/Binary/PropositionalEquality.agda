------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

module Common.Relation.Binary.PropositionalEquality where

open import Common.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infix  7 _≡_

------------------------------------------------------------------------------
-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Identity properties

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px

subst₂ : (P : D → D → Set){x₁ x₂ y₁ y₂ : D} → x₁ ≡ y₁ → x₂ ≡ y₂ → P x₁ x₂ →
         P y₁ y₂
subst₂ P refl refl Px₁x₂ = Px₁x₂

subst₄ : (P : D → D → D → D → Set){x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : D} →
         x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ → P x₁ x₂ x₃ x₄ →
         P y₁ y₂ y₃ y₄
subst₄ P refl refl refl refl Px₁x₂x₃x₄ = Px₁x₂x₃x₄
