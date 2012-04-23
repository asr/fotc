------------------------------------------------------------------------------
-- Testing Agda internal terms: Var Nat Args
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The following conjecture uses the internal Agda term @Var Nat Args@
-- where @Args@ ≠ ∅.

module Test.Succeed.AgdaInternalTerms.Var2 where

postulate
  D   : Set
  _≡_ : D → D → Set

-- TODO: 2012-02-23. Are we using Koen's approach in the translation?
postulate f-refl : (f : D → D) → ∀ x → f x ≡ f x
{-# ATP prove f-refl #-}
