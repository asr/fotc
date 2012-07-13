------------------------------------------------------------------------------
-- Testing Agda internal terms: @Var Nat Args@ when @Args = []@
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-propositional-functions #-}
{-# OPTIONS --without-K #-}

module NonFOL.AgdaInternalTerms.VarEmptyArgumentsTerm where

postulate D : Set

-- TODO: 2012-04-29. Are we using Koen's approach in the translation?
postulate id : (P : D → Set)(x : D) → P x → P x
{-# ATP prove id #-}
