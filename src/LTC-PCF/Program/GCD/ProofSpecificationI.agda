------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.ProofSpecificationI where

open import LTC-PCF.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The LTC list of natural numbers type.
        )

open import LTC-PCF.Data.Nat.Divisibility.PropertiesI using ( x∣S→x≤S )

open import LTC-PCF.Program.GCD.Definitions using ( ¬x≡0∧y≡0 )
open import LTC-PCF.Program.GCD.GCD using ( gcd )
open import LTC-PCF.Program.GCD.IsCommonDivisorI using ( gcd-CD )
open import LTC-PCF.Program.GCD.IsDivisibleI using ( gcd-Divisible )

import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorI =
  LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.IsN-I using ( gcd-N )

import LTC-PCF.Program.GCD.Specification
open module SpecificationI =
  LTC-PCF.Program.GCD.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The 'gcd' is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
