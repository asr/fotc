module Equality where

module LF where
  postulate
    D     : Set
    _≡_   : D → D → Set
    refl  : ∀ {x} → x ≡ x
    subst : ∀ (P : D → Set) {x y} → x ≡ y → P x → P y

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} h = subst (λ t → t ≡ x) h refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {z = z} h₁ h₂ = subst (λ t → t ≡ z) (sym h₁) h₂

module Inductive where

  import Common.Relation.Binary.PropositionalEquality
  open module Eq =
    Common.Relation.Binary.PropositionalEquality.Inductive public

  open import Common.Universe

  sym-er : ∀ {x y} → x ≡ y → y ≡ x
  sym-er {x} h = subst (λ t → t ≡ x) h refl

  trans-er : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans-er {z = z} h₁ h₂ = subst (λ t → t ≡ z) (sym h₁) h₂

  -- NB. The proofs of sym and trans by pattern matching are in the
  -- module Common.Relation.Binary.PropositionalEquality.
