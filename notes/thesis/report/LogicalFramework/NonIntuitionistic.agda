{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

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

-- Conjunction.
postulate
  _∧_     : Set → Set → Set
  _,_     : {A B : Set} → A → B → A ∧ B
  ∧-proj₁ : {A B : Set} → A ∧ B → A
  ∧-proj₂ : {A B : Set} → A ∧ B → B

-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥

module pem→¬-elim where

  -- The principle of the excluded middle.
  postulate pem : ∀ {A} → A ∨ ¬ A

  -- The principle of indirect proof (proof by contradiction).
  ¬-elim : ∀ {A} → (¬ A → ⊥) → A
  ¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

module ¬-elim→pem where

  -- The principle of indirect proof (proof by contradiction).
  postulate ¬-elim : ∀ {A} → (¬ A → ⊥) → A

  helper₁ : {A : Set} → ¬ (A ∨ ¬ A) → ¬ A ∧ ¬ ¬ A
  helper₁ h = (λ a → h (inj₁ a)) , (λ ¬a → h (inj₂ ¬a))

  helper₂ : {A : Set} → ¬ A ∧ ¬ ¬ A → ⊥
  helper₂ h = ∧-proj₂ h (∧-proj₁ h)

  helper₃ : {A : Set} → ¬ (A ∨ ¬ A) → ⊥
  helper₃ h = helper₂ (helper₁ h)

  -- The principle of the excluded middle.
  pem : ∀ {A} → A ∨ ¬ A
  pem = ¬-elim helper₃
