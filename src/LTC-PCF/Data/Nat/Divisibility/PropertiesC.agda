------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Divisibility.PropertiesC where

open import LTC.Base
open import LTC.Base.PropertiesC using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat.Divisibility using ( _∣_ )

------------------------------------------------------------------------------
-- 0 doesn't divide any number.
0∤x : {d : D} → ¬ (zero ∣ d)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
