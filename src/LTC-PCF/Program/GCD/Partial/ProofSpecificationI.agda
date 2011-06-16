------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Partial.ProofSpecificationI where

open import LTC-PCF.Base

open import FOTC.Data.Nat.Type

open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI
  using ( x∣Sy→x≤Sy )

open import LTC-PCF.Program.GCD.Partial.Definitions using ( x≠0≠y )
open import LTC-PCF.Program.GCD.Partial.GCD using ( gcd )
open import LTC-PCF.Program.GCD.Partial.IsCommonDivisorI using ( gcd-CD )
open import LTC-PCF.Program.GCD.Partial.IsDivisibleI using ( gcd-Divisible )

import LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorI =
  LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor x∣Sy→x≤Sy
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.Partial.TotalityI using ( gcd-N )

import LTC-PCF.Program.GCD.Partial.Specification
open module SpecificationI =
  LTC-PCF.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
