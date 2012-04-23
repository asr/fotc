------------------------------------------------------------------------------
-- Testing Agda internal terms: Var Nat Args
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The following conjecture uses the internal Agda term @Var Nat Args@
-- where @Args@ ≠ ∅.

module Test.Succeed.AgdaInternalTerms.Var1 where

postulate D : Set

-- TODO: 2012-02-23. Are we using Koen's approach in the translation?
postulate id : (P : D → Set)(x : D) → P x → P x
{-# ATP prove id #-}
