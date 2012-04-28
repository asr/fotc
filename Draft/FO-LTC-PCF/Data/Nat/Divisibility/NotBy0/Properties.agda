------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties where

open import Common.Function

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0

------------------------------------------------------------------------------
-- 0 doesn't divide any number.
0∤x : ∀ {n} → ¬ (zero ∣ n)
0∤x (0≢0 , _) = ⊥-elim $ 0≢0 refl
