------------------------------------------------------------------------------
-- Common stuff used by the gcd example
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.GCD.Total.Definitions where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.By0
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

-- Greatest common divisor specification.

-- The gcd is a common divisor and the gcd is divided by any common
-- divisor, thefore the gcd is the greatest common divisor
-- according to the partial order _∣_.
gcdSpec : D → D → D → Set
gcdSpec m n gcd = CD m n gcd ∧ Divisible m n gcd
{-# ATP definition gcdSpec #-}
