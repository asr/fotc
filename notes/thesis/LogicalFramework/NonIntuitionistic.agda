{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LogicalFramework.NonIntuitionistic where

postulate
  ⊥      : Set
  ⊥-elim : {A : Set} → ⊥ → A

-- Disjunction.
postulate
  _∨_   : Set → Set → Set
  inj₁  : {A B : Set} → A → A ∨ B
  inj₂  : {A B : Set} → B → A ∨ B
  case  : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C

-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A

-- The principle of indirect proof (proof by contradiction).
¬-elim : ∀ {A} → (¬ A → ⊥) → A
¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a))  pem
