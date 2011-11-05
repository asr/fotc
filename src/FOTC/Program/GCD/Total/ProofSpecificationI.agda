------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module FOTC.Program.GCD.Total.ProofSpecificationI where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI using ( x∣Sy→x≤Sy )
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Total.GCD using ( gcd )
open import FOTC.Program.GCD.Total.IsCommonDivisorI using ( gcd-CD )
open import FOTC.Program.GCD.Total.IsDivisibleI using ( gcd-Divisible )

open import FOTC.Program.GCD.Total.TotalityI using ( gcd-N )

import FOTC.Program.GCD.Total.Specification
open module SpecificationI =
  FOTC.Program.GCD.Total.Specification gcd-N gcd-CD gcd-Divisible
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
