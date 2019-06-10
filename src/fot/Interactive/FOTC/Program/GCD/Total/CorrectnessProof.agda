------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module Interactive.FOTC.Program.GCD.Total.CorrectnessProof where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.GCD.Total.CommonDivisor using ( gcdCD )
open import Interactive.FOTC.Program.GCD.Total.Definitions using ( gcdSpec )
open import Interactive.FOTC.Program.GCD.Total.Divisible using ( gcdDivisible )
open import Interactive.FOTC.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is correct.
gcdCorrect : ∀ {m n} → N m → N n → gcdSpec m n (gcd m n)
gcdCorrect Nm Nn = gcdCD Nm Nn , gcdDivisible Nm Nn
