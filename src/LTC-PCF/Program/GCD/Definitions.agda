------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.Definitions where

open import LTC-PCF.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )

open import LTC-PCF.Data.Nat.Divisibility using ( _∣_ )
open import LTC-PCF.Data.Nat.Inequalities using ( LE )

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD m n d = (d ∣ m) ∧ (d ∣ n)
{-# ATP definition CD #-}

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible a b gcd = ∀ c → N c → CD a b c → c ∣ gcd
{-# ATP definition Divisible #-}

-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD a b gcd = ∀ c → N c → CD a b c → LE c gcd

¬x≡0∧y≡0 : D → D → Set
¬x≡0∧y≡0 d e = ¬ (d ≡ zero ∧ e ≡ zero)
