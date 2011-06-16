------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility.NotBy0.Properties where

open import FOTC.Base
open import FOTC.Base.Properties

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ n ∣ zero
S∣0 {n} Nn = ¬S≡0 , zero , zN , sym (*-0x (succ n))

-- 0 doesn't divide any number.
0∤x : ∀ {d} → ¬ (zero ∣ d)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
