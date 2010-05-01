------------------------------------------------------------------------------
-- Specification of the Euclid's algorithm for calculate the greatest
-- common divisor of two natural numbers
------------------------------------------------------------------------------

module Examples.GCD-ER where

open import LTC.Minimal

open import Examples.GCD.Equations
open import Examples.GCD.IsCommonDivisorER
open import Examples.GCD.IsDivisibleER
open import Examples.GCD.IsGreatestAnyCommonDivisorER
open import Examples.GCD.IsN-ER

open import LTC.Data.N

-----------------------------------------------------------------------
-- The 'gcd' is the GCD.
-----------------------------------------------------------------------

-- Greatest commun divisor.

record GCD (a b gcd : D) : Set where
    field
      -- The gcd is a common divisor.
      commonDivisor : CD a b gcd

      -- Greatest that any common divisor.
      greatest : GACD a b gcd

gcd-GCD : {m n : D} → N m → N n → ¬ ((m ≡ zero) ∧ (n ≡ zero)) →
           GCD m n (gcd m n)
gcd-GCD Nm Nn m≠0≠n =
  record { commonDivisor = gcd-CD Nm Nn m≠0≠n
         ; greatest      = gcd-GACD (gcd-N Nm Nn m≠0≠n)
                                    (gcd-CD Nm Nn m≠0≠n)
                                    (gcd-Divisible Nm Nn m≠0≠n)
         }
