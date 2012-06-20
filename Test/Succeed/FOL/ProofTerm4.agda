------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.ProofTerm4 where

postulate
  D              : Set
  _≡_            : D → D → Set
  SomePredicate  : D → D → D → D → Set

-- We can erase proof terms of type SomePredicate where the type of
-- SomePredicate is
--
-- SomePredicate : D → ... → D → Set.
foo : ∀ m₁ m₂ m₃ m₄ → SomePredicate m₁ m₂ m₃ m₄ → m₁ ≡ m₁
foo m₁ m₂ m₃ m₄ h = bar m₁
  where
  postulate bar : ∀ m → m ≡ m
  {-# ATP prove bar #-}
