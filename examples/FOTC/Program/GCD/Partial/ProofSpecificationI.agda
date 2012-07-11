------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module FOTC.Program.GCD.Partial.ProofSpecificationI where

open import FOTC.Base
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI
  using ( 0∤x ; x∣S→x≤S )
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Partial.CommonDivisorI using ( gcd-CD )
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.DivisibleI using ( gcd-Divisible )
open import FOTC.Program.GCD.Partial.GCD using ( gcd )

import FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open module GreatestAnyCommonDivisorI =
  FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor x∣S→x≤S 0∤x
  using ( gcd-GACD )

open import FOTC.Program.GCD.Partial.TotalityI using ( gcd-N )

------------------------------------------------------------------------------
-- The gcd is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≢0≢y m n → GCD m n (gcd m n)
gcd-GCD Nm Nn m≢0≢n = gcd-CD Nm Nn m≢0≢n
                    , gcd-GACD (gcd-N Nm Nn m≢0≢n)
                               (gcd-CD Nm Nn m≢0≢n)
                               (gcd-Divisible Nm Nn m≢0≢n)
