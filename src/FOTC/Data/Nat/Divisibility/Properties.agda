------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility.Properties where

open import FOTC.Base
open import FOTC.Base.Properties using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat
  using ( *-0x
        ; N ; zN  -- The FOTC natural numbers type.
        )
open import FOTC.Data.Nat.Divisibility using ( _∣_ )

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ n ∣ zero
S∣0 {n} Nn = ¬S≡0 , zero , zN , sym (*-0x (succ n))

-- 0 doesn't divide any number.
0∤x : ∀ {d} → ¬ (zero ∣ d)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
