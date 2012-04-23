-- Tested with the development version of Agda on 23 April 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module NonIntuitionistic where

postulate
  ⊥      : Set
  ⊥-elim : {A : Set} → ⊥ → A

-- Disjunction.
postulate
  _∨_   : Set → Set → Set
  inj₁  : {A B : Set} → A → A ∨ B
  inj₂  : {A B : Set} → B → A ∨ B
  [_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C

-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A

-- The principle of indirect proof (proof by contradiction).
¬-elim : ∀ {A} → (¬ A → ⊥) → A
¬-elim h = [ (λ a → a) , (λ ¬a → ⊥-elim (h ¬a)) ] pem
