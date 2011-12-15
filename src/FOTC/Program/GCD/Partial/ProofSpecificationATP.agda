------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.GCD.Partial.ProofSpecificationATP where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP using ( x∣S→x≤S )
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Partial.Definitions using ( x≠0≠y )
open import FOTC.Program.GCD.Partial.GCD using ( gcd )
open import FOTC.Program.GCD.Partial.IsCommonDivisorATP using ( gcd-CD )
open import FOTC.Program.GCD.Partial.IsDivisibleATP using ( gcd-Divisible )

import FOTC.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorATP =
  FOTC.Program.GCD.Partial.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import FOTC.Program.GCD.Partial.TotalityATP using ( gcd-N )

import FOTC.Program.GCD.Partial.Specification
open module SpecificationATP =
  FOTC.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-ATP )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-ATP
