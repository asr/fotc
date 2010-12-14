------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC.Program.GCD.ProofSpecificationATP where

open import LTC.Base

open import LTC.Data.Nat.Divisibility.PropertiesATP using ( x∣S→x≤S )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC list of natural numbers type.
        )

open import LTC.Program.GCD.Definitions using ( ¬x≡0∧y≡0 )
open import LTC.Program.GCD.GCD using ( gcd )
open import LTC.Program.GCD.IsCommonDivisorATP using ( gcd-CD )
open import LTC.Program.GCD.IsDivisibleATP using ( gcd-Divisible )

import LTC.Program.GCD.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorATP =
  LTC.Program.GCD.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import LTC.Program.GCD.IsN-ATP using ( gcd-N )

import LTC.Program.GCD.Specification
open module SpecificationATP =
  LTC.Program.GCD.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The 'gcd' is the GCD.
gcd-GCD : {m n : D} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
