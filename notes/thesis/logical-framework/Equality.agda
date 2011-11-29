module Equality where

postulate
  D     : Set
  _≡_   : D → D → Set
  refl  : ∀ {x} → x ≡ x
  subst : ∀ (P : D → Set) {x y} → x ≡ y → P x → P y

sym : ∀ {x y} → x ≡ y → y ≡ x
sym {x} h = subst (λ t → t ≡ x) h refl

trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
trans {z = z} h₁ h₂ = subst (λ t → t ≡ z) (sym h₁) h₂
