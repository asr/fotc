------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Partial.ProofSpecificationI where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI
  using ( x∣Sy→x≤Sy )
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Program.GCD.Partial.CommonDivisorI using ( gcd-CD )
open import LTC-PCF.Program.GCD.Partial.Definitions using ( x≢0≢y )
open import LTC-PCF.Program.GCD.Partial.DivisibleI using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.Partial.GCD using ( gcd )

import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open module GreatestAnyCommonDivisorI =
  LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor x∣Sy→x≤Sy
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.Partial.TotalityI using ( gcd-N )

import LTC-PCF.Program.GCD.Partial.Specification
open module SpecificationI =
  LTC-PCF.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≢0≢y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
