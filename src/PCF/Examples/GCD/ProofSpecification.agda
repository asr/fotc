------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module PCF.Examples.GCD.ProofSpecification where

open import LTC.Base

open import PCF.Examples.GCD.GCD using ( ¬x≡0∧y≡0 ; gcd )
open import PCF.Examples.GCD.IsCommonDivisor using ( CD ; gcd-CD )
open import PCF.Examples.GCD.IsDivisible using ( gcd-Divisible )
open import PCF.Examples.GCD.IsGreatestAnyCommonDivisor
  using ( GACD ; gcd-GACD )
open import PCF.Examples.GCD.IsN using ( gcd-N )

open import PCF.LTC.Data.Nat
  using ( N  -- The LTC natural numbers type.
        )

------------------------------------------------------------------------------
-- Greatest commun divisor.
record GCD (a b gcd : D) : Set where
  constructor is
  field
    -- The gcd is a common divisor.
    commonDivisor : CD a b gcd

    -- Greatest that any common divisor.
    greatest : GACD a b gcd

-- The 'gcd' is the GCD.
gcd-GCD : {m n : D} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD Nm Nn m≠0≠n = is (gcd-CD Nm Nn m≠0≠n)
                         (gcd-GACD (gcd-N Nm Nn m≠0≠n)
                                   (gcd-CD Nm Nn m≠0≠n)
                                   (gcd-Divisible Nm Nn m≠0≠n))
