------------------------------------------------------------------------------
-- Testing Agda internal terms: @Var Nat Args@ when @Args = []@
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.AgdaInternalTerms.VarEmptyArguments where

postulate D : Set

-- TODO: 2012-04-29. Are we using Koen's approach in the translation?
postulate id : (P : D → Set)(x : D) → P x → P x
{-# ATP prove id #-}
