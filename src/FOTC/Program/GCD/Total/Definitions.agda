------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

module FOTC.Program.GCD.Total.Definitions where

open import FOTC.Base

open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD d₁ d₂ cd = cd ∣ d₁ ∧ cd ∣ d₂
{-# ATP definition CD #-}

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible d₁ d₂ gcd = ∀ cd → N cd → CD d₁ d₂ cd → cd ∣ gcd
{-# ATP definition Divisible #-}
