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
CD m n cd = cd ∣ m ∧ cd ∣ n

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible m n gcd = ∀ cd → N cd → CD m n cd → cd ∣ gcd
