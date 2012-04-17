------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0.Properties where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.By0

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ n → succ₁ n ∣ zero
S∣0 n = zero , zN , sym (*-0x (succ₁ n))

-- 0 divides 0.
0∣0 : zero ∣ zero
0∣0 = zero , zN , sym (*-0x zero)
