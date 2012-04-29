------------------------------------------------------------------------------
-- Testing Agda internal terms: @Var Nat Args@ when @Args = []@
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Requires option --non-fol-propositional-function@.

module Test.Succeed.NonFOL.AgdaInternalTerms.VarEmptyArguments where

postulate D : Set

-- TODO: 2012-04-29. Are we using Koen's approach in the translation?
postulate id : (P : D → Set)(x : D) → P x → P x
{-# ATP prove id #-}
