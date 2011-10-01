------------------------------------------------------------------------------
-- The identity type
------------------------------------------------------------------------------

-- We can prove the properties of equality used in the formalization
-- of FOTC, from refl and J.

module IdentityType where

infix 7 _≡_

postulate
  D    : Set
  _≡_  : D → D → Set
  refl : ∀ {x} → x ≡ x
  J    : (C : ∀ x y → x ≡ y → Set) →
         (∀ x → (C x x refl)) →
         ∀ x y → (c : x ≡ y) → C x y c

-- From Thorsten's slides: A short history of equality.
sym : ∀ {x y} → x ≡ y → y ≡ x
sym {x} {y} = J (λ x' y' _ → y' ≡ x') (λ x' → refl) x y

-- From Thorsten's slides: A short history of equality.
trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans {x} {y} {z} = J (λ x' y' _ → y' ≡ z → x' ≡ z) (λ x' pr → pr) x y

subst : ∀ {x} {y} → (P : D → Set) → x ≡ y → P x → P y
subst {x} {y} P x≡y = J (λ x' y' _ → P x' → P y') (λ x' pr → pr) x y x≡y
