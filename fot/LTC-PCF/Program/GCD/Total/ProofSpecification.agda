------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Total.ProofSpecification where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Type
open import LTC-PCF.Program.GCD.Total.CommonDivisor using ( gcd-CD )
open import LTC-PCF.Program.GCD.Total.Definitions using ( GCD )
open import LTC-PCF.Program.GCD.Total.Divisible using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
gcd-GCD Nm Nn = gcd-CD Nm Nn , gcd-Divisible Nm Nn
