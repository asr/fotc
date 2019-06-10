------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.GCD.Partial.Definitions where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Divisibility.NotBy0
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Common divisor.
CD : D → D → D → Set
CD m n cd = cd ∣ m ∧ cd ∣ n

-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible m n gcd = ∀ cd → N cd → CD m n cd → cd ∣ gcd

-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD m n gcd = ∀ cd → N cd → CD m n cd → cd ≤ gcd

-- Greatest common divisor specification
gcdSpec : D → D → D → Set
gcdSpec m n gcd = CD m n gcd ∧ GACD m n gcd

x≢0≢y : D → D → Set
x≢0≢y m n = ¬ (m ≡ zero ∧ n ≡ zero)
