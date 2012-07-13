------------------------------------------------------------------------------
-- Testing Agda internal term: @Var Nat Args@ when @Args ≠ []@
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-functions #-}
{-# OPTIONS --without-K #-}

module NonFOL.AgdaInternalTerms.VarNonEmptyArgumentsTerm where

postulate
  D   : Set
  _≡_ : D → D → Set

-- TODO: 2012-04-29. Are we using Koen's approach in the translation?
postulate f-refl : (f : D → D) → ∀ x → f x ≡ f x
{-# ATP prove f-refl #-}
