------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility.By0.Properties where

open import FOTC.Base
open import FOTC.Base.Properties

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.By0

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ n ∣ zero
S∣0 {n} Nn = zero , zN , sym (*-0x (succ n))

-- 0 divides 0.
0∣0 : zero ∣ zero
0∣0 = zero , zN , sym (*-0x zero)
