------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.Definitions where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD m n cd = cd ∣ m ∧ cd ∣ n
{-# ATP definition CD #-}

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible m n gcd = ∀ cd → N cd → CD m n cd → cd ∣ gcd
{-# ATP definition Divisible #-}

-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD m n gcd = ∀ cd → N cd → CD m n cd → cd ≤ gcd
{-# ATP definition GACD #-}

-- Greatest common divisor.
GCD : D → D → D → Set
GCD m n gcd = CD m n gcd ∧ GACD m n gcd
{-# ATP definition GCD #-}

x≢0≢y : D → D → Set
x≢0≢y m n = ¬ (m ≡ zero ∧ n ≡ zero)
{-# ATP definition x≢0≢y #-}
