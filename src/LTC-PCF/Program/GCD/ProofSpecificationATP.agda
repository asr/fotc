------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC-PCF.Program.GCD.ProofSpecificationATP where

open import LTC-PCF.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The LTC list of natural numbers type.
        )

open import LTC-PCF.Data.Nat.Divisibility.PropertiesATP using ( x∣S→x≤S )

open import LTC-PCF.Program.GCD.Definitions using ( ¬x≡0∧y≡0 )
open import LTC-PCF.Program.GCD.GCD using ( gcd )
open import LTC-PCF.Program.GCD.IsCommonDivisorATP using ( gcd-CD )
open import LTC-PCF.Program.GCD.IsDivisibleATP using ( gcd-Divisible )

import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorATP =
  LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.IsN-ATP using ( gcd-N )

import LTC-PCF.Program.GCD.Specification
open module SpecificationATP =
  LTC-PCF.Program.GCD.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The 'gcd' is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
