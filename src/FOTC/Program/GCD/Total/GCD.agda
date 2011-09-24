------------------------------------------------------------------------------
-- Definition of the gcd of two natural numbers using the Euclid's algorithm
------------------------------------------------------------------------------

module FOTC.Program.GCD.Total.GCD where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- In GHC HEAD (7.1.20110615) the gcd is a total function, i.e. gcd 0 0 = 0.

postulate
  gcd    : D → D → D
  gcd-eq : ∀ m n → gcd m n ≡
                   if (isZero n)
                      then m
                      else (if (isZero m)
                               then n
                               else (if (m > n)
                                        then gcd (m ∸ n) n
                                        else gcd m (n ∸ m)))
{-# ATP axiom gcd-eq #-}
