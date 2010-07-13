------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module Examples.GCD-PCF.EquationsPCF where

open import LTC.Minimal

open import Examples.GCD-PCF.GCD-PCF
open import LTC.Data.NatPCF
open import LTC.Data.NatPCF.InequalitiesPCF

------------------------------------------------------------------------------

postulate
  gcd-00 : gcd zero zero ≡ error
{-# ATP prove gcd-00 #-}

postulate
 gcd-S0 : (n : D) → gcd (succ n) zero ≡ succ n
{-# ATP prove gcd-S0 #-}

postulate
  gcd-0S : (n : D) → gcd zero (succ n) ≡ succ n
{-# ATP prove gcd-0S #-}

-- TODO: Neither Equinox nor Eprove prove the theorems gcd-S>S and
-- gcd-S≤S. They was proved using on-line Vampire.

postulate
  gcd-S>S : (m n : D) → GT (succ m) (succ n) →
             gcd (succ m) (succ n) ≡ gcd (succ m - succ n) (succ n)
{-# ATP prove gcd-S>S #-}

postulate
  gcd-S≤S : (m n : D) → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n - succ m)
{-# ATP prove gcd-S≤S #-}
