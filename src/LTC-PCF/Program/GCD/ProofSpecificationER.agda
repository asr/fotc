------------------------------------------------------------------------------
-- The gcd program satisfies the specification (using equational reasoning)
------------------------------------------------------------------------------

-- TODO: This module is called ProofSpecificationER, but it not used ER.

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.ProofSpecificationER where

open import LTC.Base

open import LTC-PCF.Data.Nat
  using ( N  -- The LTC natural numbers type.
        )

open import LTC-PCF.Program.GCD.GCD using ( ¬x≡0∧y≡0 ; gcd )
open import LTC-PCF.Program.GCD.IsCommonDivisorER using ( CD ; gcd-CD )
open import LTC-PCF.Program.GCD.IsDivisibleER using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisorER
  using ( GACD ; gcd-GACD )
open import LTC-PCF.Program.GCD.IsN-ER using ( gcd-N )

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
