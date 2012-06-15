------------------------------------------------------------------------------
-- Reasoning partially about functions
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We cannot reasoning partially about partial functions intended to
-- operate in total values.

module FOT.FOTC.Data.Nat.AddPartialRightIdentity where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

-- How proceed?
+-partialRightIdentity : ∀ n → n + zero ≡ n
+-partialRightIdentity n = {!!}
