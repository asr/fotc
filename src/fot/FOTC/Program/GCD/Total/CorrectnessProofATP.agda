------------------------------------------------------------------------------
-- The gcd program is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.GCD.Total.CorrectnessProofATP where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Total.CommonDivisorATP using ( gcdCD )
open import FOTC.Program.GCD.Total.Definitions using ( gcdSpec )
open import FOTC.Program.GCD.Total.DivisibleATP using ( gcdDivisible )
open import FOTC.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is correct.
postulate gcdCorrect : ∀ {m n} → N m → N n → gcdSpec m n (gcd m n)
{-# ATP prove gcdCorrect gcdCD gcdDivisible #-}
