------------------------------------------------------------------------------
-- Testing records
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Record where

postulate
  D  : Set
  P₁ : D → Set
  P₂ : D → D → Set

record P (a b : D) : Set where
  constructor is
  field
    property₁ : P₁ a
    property₂ : P₂ a b
{-# ATP axiom is #-}

postulate
  p₁ : ∀ a → P₁ a
  p₂ : ∀ a b → P₂ a b
{-# ATP axiom p₁ #-}
{-# ATP axiom p₂ #-}

thm₁ : ∀ a b → P a b
thm₁ a b = is (p₁ a) (p₂ a b)

postulate thm₂ : ∀ a b → P a b
{-# ATP prove thm₂ #-}
