------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP

open import LTC-PCF.Program.GCD.GCD

------------------------------------------------------------------------------

postulate
  gcd-00 : gcd zero zero ≡ error
-- E 1.2: CPU time limit exceeded (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove gcd-00 #-}

postulate
 gcd-S0 : ∀ n → gcd (succ n) zero ≡ succ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-S0 #-}

postulate
  gcd-0S : ∀ n → gcd zero (succ n) ≡ succ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-0S #-}

postulate
  gcd-S>S : ∀ m n → GT (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)
-- E 1.2: CPU time limit exceeded (180 sec).
-- E 1.2: CPU time limit exceeded (300 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 300 sec).
{-# ATP prove gcd-S>S #-}

-- Because we define LE on terms of LT, we need the extra hypotheses
-- N m and N n.
postulate
  gcd-S≤S : ∀ {m n} → N m → N n → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)
{-# ATP prove gcd-S≤S x≤y→x≯y #-}
