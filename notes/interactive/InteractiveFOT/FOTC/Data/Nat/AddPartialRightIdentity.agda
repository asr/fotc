------------------------------------------------------------------------------
-- Reasoning partially about functions
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas     #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- We cannot reasoning partially about partial functions intended to
-- operate in total values.

module InteractiveFOT.FOTC.Data.Nat.AddPartialRightIdentity where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat

------------------------------------------------------------------------------

-- How proceed?
+-partialRightIdentity : ∀ n → n + zero ≡ n
+-partialRightIdentity n = {!!}
