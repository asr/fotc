------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC-PCF.Program.GCD.Partial.ProofSpecificationATP where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
  using ( x∣Sy→x≤Sy )
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Program.GCD.Partial.CommonDivisorATP using ( gcd-CD )
open import LTC-PCF.Program.GCD.Partial.Definitions using ( x≢0≢y )
open import LTC-PCF.Program.GCD.Partial.DivisibleATP using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.Partial.GCD using ( gcd )

import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open module GreatestAnyCommonDivisorATP =
  LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor x∣Sy→x≤Sy
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.Partial.TotalityATP using ( gcd-N )

import LTC-PCF.Program.GCD.Partial.Specification
open module SpecificationATP =
  LTC-PCF.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≢0≢y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
