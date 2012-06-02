------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Total.Definitions where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.By0
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Type

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD d₁ d₂ cd = cd ∣ d₁ ∧ cd ∣ d₂

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible d₁ d₂ gcd = ∀ cd → N cd → CD d₁ d₂ cd → cd ∣ gcd
