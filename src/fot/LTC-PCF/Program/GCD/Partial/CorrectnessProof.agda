------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Partial.CorrectnessProof where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
  using ( 0∤x ; x∣S→x≤S )
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Program.GCD.Partial.CommonDivisor using ( gcd-CD )
open import LTC-PCF.Program.GCD.Partial.Definitions using ( x≢0≢y ; gcdSpec )
open import LTC-PCF.Program.GCD.Partial.Divisible using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.Partial.GCD using ( gcd )

import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open module GreatestAnyCommonDivisor =
  LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor x∣S→x≤S 0∤x
  using ( gcd-GACD )

open import LTC-PCF.Program.GCD.Partial.Totality using ( gcd-N )

------------------------------------------------------------------------------
-- The gcd is correct
gcdCorrect : ∀ {m n} → N m → N n → x≢0≢y m n → gcdSpec m n (gcd m n)
gcdCorrect Nm Nn m≢0≢n = gcd-CD Nm Nn m≢0≢n
                         , gcd-GACD (gcd-N Nm Nn m≢0≢n)
                                    (gcd-CD Nm Nn m≢0≢n)
                                    (gcd-Divisible Nm Nn m≢0≢n)
