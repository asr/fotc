------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.Total.CorrectnessProof where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Type
open import LTC-PCF.Program.GCD.Total.CommonDivisor using ( gcdCD )
open import LTC-PCF.Program.GCD.Total.Definitions using ( gcdSpec )
open import LTC-PCF.Program.GCD.Total.Divisible using ( gcdDivisible )
open import LTC-PCF.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is correct.
gcdCorrect : ∀ {m n} → N m → N n → gcdSpec m n (gcd m n)
gcdCorrect Nm Nn = gcdCD Nm Nn , gcdDivisible Nm Nn
