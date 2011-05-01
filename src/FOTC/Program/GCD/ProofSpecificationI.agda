------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module FOTC.Program.GCD.ProofSpecificationI where

open import FOTC.Base

open import FOTC.Data.Nat.Divisibility.PropertiesI using ( x∣S→x≤S )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC list of natural numbers type.
        )

open import FOTC.Program.GCD.Definitions using ( x≠0≠y )
open import FOTC.Program.GCD.GCD using ( gcd )
open import FOTC.Program.GCD.IsCommonDivisorI using ( gcd-CD )
open import FOTC.Program.GCD.IsDivisibleI using ( gcd-Divisible )

import FOTC.Program.GCD.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorI =
  FOTC.Program.GCD.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import FOTC.Program.GCD.TotalityI using ( gcd-N )

import FOTC.Program.GCD.Specification
open module SpecificationI =
  FOTC.Program.GCD.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The 'gcd' is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
