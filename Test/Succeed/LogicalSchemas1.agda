------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.LogicalSchemas1 where

postulate
  D   : Set
  _≡_ : D → D → Set

postulate f₁-refl : (f₁ : D → D)(x : D) → f₁ x ≡ f₁ x
{-# ATP prove f₁-refl #-}
