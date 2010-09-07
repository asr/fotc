------------------------------------------------------------------------------
-- The gcd program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the gcd program using
-- the Euclid's algorithm.

module Examples.GCD.ProofSpecification where

open import LTC.Minimal

open import Examples.GCD.GCD using ( gcd )
open import Examples.GCD.IsCommonDivisor using ( CD ; gcd-CD )
open import Examples.GCD.IsDivisible using ( gcd-Divisible )
open import Examples.GCD.IsGreatestAnyCommonDivisor using ( GACD ; gcd-GACD )
open import Examples.GCD.IsN using ( gcd-N )
open import Examples.GCD.Types using ( ¬x≡0∧y≡0 )

open import LTC.Data.Nat.Type using ( N )

-----------------------------------------------------------------------
-- The 'gcd' is the GCD

-- Greatest commun divisor
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
