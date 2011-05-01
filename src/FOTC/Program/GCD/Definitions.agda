------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

module FOTC.Program.GCD.Definitions where

open import FOTC.Base

open import FOTC.Data.Nat.Divisibility using ( _∣_ )
open import FOTC.Data.Nat.Inequalities using ( LE )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC natural numbers type.
        )

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD d₁ d₂ cd = cd ∣ d₁ ∧ cd ∣ d₂
{-# ATP definition CD #-}

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible d₁ d₂ gcd = ∀ cd → N cd → CD d₁ d₂ cd → cd ∣ gcd
{-# ATP definition Divisible #-}

-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD d₁ d₂ gcd = ∀ cd → N cd → CD d₁ d₂ cd → LE cd gcd

x≠0≠y : D → D → Set
x≠0≠y d e = ¬ (d ≡ zero ∧ e ≡ zero)
