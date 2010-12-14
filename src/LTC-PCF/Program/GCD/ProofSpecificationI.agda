------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module LTC-PCF.Program.GCD.ProofSpecificationI where

open import LTC.Base

open import LTC-PCF.Data.Nat
  using ( N  -- The LTC natural numbers type.
        )

open import LTC-PCF.Program.GCD.GCD using ( ¬x≡0∧y≡0 ; gcd )
open import LTC-PCF.Program.GCD.IsCommonDivisorI using ( CD ; gcd-CD )
open import LTC-PCF.Program.GCD.IsDivisibleI using ( gcd-Divisible )
open import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisorI
  using ( GACD ; gcd-GACD )
open import LTC-PCF.Program.GCD.IsN-I using ( gcd-N )

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
