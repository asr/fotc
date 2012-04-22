------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.LogicalSchemas2 where

postulate
  D   : Set
  _≡_ : D → D → Set

postulate f₂-refl : (f₂ : D → D → D)(x y : D) → f₂ x y ≡ f₂ x y
{-# ATP prove f₂-refl #-}
