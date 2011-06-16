------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
-- using the Euclid's algorithm
------------------------------------------------------------------------------

module FOTC.Program.GCD.Partial.GCD where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- In GHC 7.0.3 the gcd is a partial function, i.e. gcd 0 0 = undefined.

postulate
  gcd    : D → D → D
  gcd-eq : ∀ m n → gcd m n ≡
                   if (isZero n)
                      then (if (isZero m)
                               then loop
                               else m)
                      else (if (isZero m)
                               then n
                               else (if (m > n)
                                        then gcd (m ∸ n) n
                                        else gcd m (n ∸ m)))
{-# ATP axiom gcd-eq #-}
