------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module FOTC.Program.GCD.Partial.ProofSpecificationI where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI using ( x∣S→x≤S )
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Partial.Definitions using ( x≠0≠y )
open import FOTC.Program.GCD.Partial.GCD using ( gcd )
open import FOTC.Program.GCD.Partial.IsCommonDivisorI using ( gcd-CD )
open import FOTC.Program.GCD.Partial.IsDivisibleI using ( gcd-Divisible )

import FOTC.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open module IsGreatestAnyCommonDivisorI =
  FOTC.Program.GCD.Partial.IsGreatestAnyCommonDivisor x∣S→x≤S
  using ( gcd-GACD )

open import FOTC.Program.GCD.Partial.TotalityI using ( gcd-N )

import FOTC.Program.GCD.Partial.Specification
open module SpecificationI =
  FOTC.Program.GCD.Partial.Specification gcd-N gcd-CD gcd-Divisible gcd-GACD
  renaming ( gcd-GCD to gcd-GCD-I )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD = gcd-GCD-I
