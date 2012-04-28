------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Program.GCD.Partial.Definitions where

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities
open import Draft.FO-LTC-PCF.Data.Nat.Type

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

x≢0≢y : D → D → Set
x≢0≢y d e = ¬ (d ≡ zero ∧ e ≡ zero)
