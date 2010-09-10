------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module Examples.GCD-PCF.EquationsPCF where

open import LTC.Minimal

open import Examples.GCD-PCF.GCD-PCF
open import LTC-PCF.DataPCF.NatPCF
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF

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

postulate
  gcd-S>S : (m n : D) → GT (succ m) (succ n) →
             gcd (succ m) (succ n) ≡ gcd (succ m - succ n) (succ n)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
-- E 1.2 no-success due to timeout (180).
-- The postulate was proved using on-line Vampire.
-- TODO: To find an ATP for to prove this postulate
-- {-# ATP prove gcd-S>S #-}

postulate
  gcd-S≤S : (m n : D) → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n - succ m)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
-- E 1.2 no-success due to timeout (180).
-- The postulate was proved using on-line Vampire.
-- TODO: To find an ATP for to prove this postulate
-- {-# ATP prove gcd-S≤S #-}
