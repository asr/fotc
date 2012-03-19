------------------------------------------------------------------------------
-- Reasoning partially about functions
------------------------------------------------------------------------------

-- We cannot reasoning partially about partial functions intended to
-- operate in total values.

-- Tested with FOT on 19 March 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FOTC.Data.Nat.AddPartialRightIdentity where

open import FOTC.Base
open import FOTC.Data.Nat

-- How proceed?
+-partialRightIdentity : ∀ n → n + zero ≡ n
+-partialRightIdentity n = {!!}
