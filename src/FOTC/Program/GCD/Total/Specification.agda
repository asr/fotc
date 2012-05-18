------------------------------------------------------------------------------
-- The gcd (parametric) specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Total.Definitions
open import FOTC.Program.GCD.Total.GCD

module FOTC.Program.GCD.Total.Specification
  (gcd-CD        : ∀ {m n} → N m → N n → CD m n (gcd m n))
  (gcd-Divisible : ∀ {m n} → N m → N n → Divisible m n (gcd m n))
  where

------------------------------------------------------------------------------
-- Greatest common divisor.
record GCD (a b gcd : D) : Set where
  constructor is
  field
    -- The gcd is a common divisor.
    commonDivisor : CD a b gcd

    -- The gcd is divided by any common divisor, thefore the gcd is the
    -- greatest common divisor according to the partial order _∣_.
    greatest : Divisible a b gcd

-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
gcd-GCD Nm Nn = is (gcd-CD Nm Nn) (gcd-Divisible Nm Nn)
