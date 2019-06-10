------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module Combined.FOTC.Program.GCD.Partial.CorrectnessProof where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.Divisibility.NotBy0.Properties using ( 0∤x ; x∣S→x≤S )
open import Combined.FOTC.Data.Nat.Type
open import Combined.FOTC.Program.GCD.Partial.CommonDivisor using ( gcdCD )
open import Combined.FOTC.Program.GCD.Partial.Definitions using ( x≢0≢y ; gcdSpec )
open import Combined.FOTC.Program.GCD.Partial.Divisible using ( gcdDivisible )
open import Combined.FOTC.Program.GCD.Partial.GCD using ( gcd )

import Combined.FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open module GreatestAnyCommonDivisorATP =
  Combined.FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor x∣S→x≤S 0∤x
  using ( gcdGACD )

open import Combined.FOTC.Program.GCD.Partial.Totality using ( gcd-N )

------------------------------------------------------------------------------
-- The gcd is correct.
postulate gcdCorrect : ∀ {m n} → N m → N n → x≢0≢y m n → gcdSpec m n (gcd m n)
{-# ATP prove gcdCorrect gcdCD gcdGACD gcd-N gcdDivisible #-}
