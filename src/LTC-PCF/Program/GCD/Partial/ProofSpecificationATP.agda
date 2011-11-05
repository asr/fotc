------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC-PCF.Program.GCD.Partial.ProofSpecificationATP where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
  using ( x∣Sy→x≤Sy )
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Program.GCD.Partial.Definitions using ( x≠0≠y )
open import LTC-PCF.Program.GCD.Partial.GCD using ( gcd )
open import LTC-PCF.Program.GCD.Partial.IsCommonDivisorATP using ( gcd-CD )
open import LTC-PCF.Program.GCD.Partial.IsDivisibleATP using ( gcd-Divisible )

import LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorATP =
  LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor x∣Sy→x≤Sy
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.Partial.TotalityATP using ( gcd-N )

import LTC-PCF.Program.GCD.Partial.Specification
open module SpecificationATP =
  LTC-PCF.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
