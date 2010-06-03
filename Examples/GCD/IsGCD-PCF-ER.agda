------------------------------------------------------------------------------
-- Specification of the Euclid's algorithm for calculate the greatest
-- common divisor of two natural numbers
------------------------------------------------------------------------------

module Examples.GCD.IsGCD-PCF-ER where

open import LTC.Minimal

open import Examples.GCD-PCF
open import Examples.GCD.IsCommonDivisorPCF-ER
open import Examples.GCD.IsDivisiblePCF-ER
open import Examples.GCD.IsGreatestAnyCommonDivisorPCF-ER
open import Examples.GCD.IsN-PCF-ER
open import Examples.GCD.Types

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

gcd-GCD : {m n : D} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD Nm Nn m≠0≠n =
  record { commonDivisor = gcd-CD Nm Nn m≠0≠n
         ; greatest      = gcd-GACD (gcd-N Nm Nn m≠0≠n)
                                    (gcd-CD Nm Nn m≠0≠n)
                                    (gcd-Divisible Nm Nn m≠0≠n)
         }
