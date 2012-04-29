------------------------------------------------------------------------------
-- Testing the translation of FOL universal quantified function terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Requires option @--non-fol-term-quantification@.

module Test.Succeed.NonFOL.UniversalQuantifiedFunctionTerms where

postulate
  D   : Set
  _≡_ : D → D → Set

-- N.B. The test for @f : D → D@ is in
-- Test.Succeed.NonFOL.AgdaInternalTerms.VarNonEmptyArguments.
postulate f-refl : (f : D → D → D → D) → ∀ x y z → f x y z ≡ f x y z
{-# ATP prove f-refl #-}
