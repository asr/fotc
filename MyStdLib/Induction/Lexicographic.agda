------------------------------------------------------------------------------
-- The Lexicographic order is a well-founded order
------------------------------------------------------------------------------

module MyStdLib.Induction.Lexicographic
  {A B : Set}
  (RelA : A → A → Set)
  (RelB : B → B → Set) where

open import MyStdLib.Data.Product
open import MyStdLib.Induction.WellFounded

------------------------------------------------------------------------------

-- Adapted from the standard library

data LT₂ : A × B → A × B → Set where
  left  : {x₁ x₂ : A}{y₁ y₂ : B} → (x₁<x₂ : RelA x₁ x₂) →
          LT₂ (x₁ , y₁) (x₂ , y₂)
  right : {x : A}{y₁ y₂ : B} → (y₁<y₂ : RelB y₁ y₂) → LT₂ (x , y₁) (x , y₂)

postulate
  wellFoundedLexi : WellFounded RelA → WellFounded RelB → WellFounded LT₂
