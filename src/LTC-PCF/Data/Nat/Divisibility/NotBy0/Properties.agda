------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.NotBy0

------------------------------------------------------------------------------
-- 0 doesn't divide any number.
0∤x : ∀ {d} → ¬ (zero ∣ d)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
