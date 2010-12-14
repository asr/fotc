------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC.Data.Nat.Divisibility.PropertiesC where

open import LTC.Base
open import LTC.Base.PropertiesC using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import LTC.Data.Nat
  using ( *-0x
        ; N ; zN  -- The LTC natural numbers type.
        )
open import LTC.Data.Nat.Divisibility using ( _∣_ )

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : {n : D} → N n → succ n ∣ zero
S∣0 {n} Nn = ¬S≡0 , zero , zN , sym (*-0x (succ n))

-- 0 doesn't divide any number.
0∤x : {d : D} → ¬ (zero ∣ d)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
