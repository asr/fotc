------------------------------------------------------------------------------
-- Testing the erasing of proof terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module ProofTerm4 where

postulate
  D      : Set
  _≡_    : D → D → Set
  SomeP  : D → D → D → D → Set

-- We can erase proof terms of type D → ... → D → Set
foo : ∀ m₁ m₂ m₃ m₄ → SomeP m₁ m₂ m₃ m₄ → m₁ ≡ m₁
foo m₁ m₂ m₃ m₄ h = bar m₁
  where
  postulate bar : ∀ m → m ≡ m
  {-# ATP prove bar #-}
