------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Total.ProofSpecificationI where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Type
open import LTC-PCF.Program.GCD.Total.CommonDivisorI using ( gcd-CD )
open import LTC-PCF.Program.GCD.Total.DivisibleI using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.Total.GCD using ( gcd )

open import LTC-PCF.Program.GCD.Total.TotalityI using ( gcd-N )

import LTC-PCF.Program.GCD.Total.Specification
open module SpecificationI =
  LTC-PCF.Program.GCD.Total.Specification gcd-CD gcd-Divisible
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
