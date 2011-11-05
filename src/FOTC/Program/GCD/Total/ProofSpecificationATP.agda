------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.GCD.Total.ProofSpecificationATP where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP using ( x∣Sy→x≤Sy )
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Total.GCD using ( gcd )
open import FOTC.Program.GCD.Total.IsCommonDivisorATP using ( gcd-CD )
open import FOTC.Program.GCD.Total.IsDivisibleATP using ( gcd-Divisible )

open import FOTC.Program.GCD.Total.TotalityATP using ( gcd-N )

import FOTC.Program.GCD.Total.Specification
open module SpecificationATP =
  FOTC.Program.GCD.Total.Specification gcd-N gcd-CD gcd-Divisible
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
