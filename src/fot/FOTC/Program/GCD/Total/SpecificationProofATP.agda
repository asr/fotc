------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.GCD.Total.SpecificationProofATP where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Program.GCD.Total.CommonDivisorATP using ( gcd-CD )
open import FOTC.Program.GCD.Total.Definitions using (GCD)
open import FOTC.Program.GCD.Total.DivisibleATP using ( gcd-Divisible )
open import FOTC.Program.GCD.Total.GCD using ( gcd )

------------------------------------------------------------------------------
-- The gcd is the GCD.
postulate gcd-GCD : ∀ {m n} → N m → N n → GCD m n (gcd m n)
{-# ATP prove gcd-GCD gcd-CD gcd-Divisible #-}
