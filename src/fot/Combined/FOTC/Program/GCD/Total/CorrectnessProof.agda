------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module Combined.FOTC.Program.GCD.Total.CorrectnessProof where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.Type
open import Combined.FOTC.Program.GCD.Total.CommonDivisor using ( gcdCD )
open import Combined.FOTC.Program.GCD.Total.Definitions using ( gcdSpec )
open import Combined.FOTC.Program.GCD.Total.Divisible using ( gcdDivisible )
open import Combined.FOTC.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is correct.
postulate gcdCorrect : ∀ {m n} → N m → N n → gcdSpec m n (gcd m n)
{-# ATP prove gcdCorrect gcdCD gcdDivisible #-}
