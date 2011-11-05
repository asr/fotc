------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.Partial.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

open import LTC-PCF.Loop

open import LTC-PCF.Program.GCD.Partial.GCD

------------------------------------------------------------------------------

postulate gcd-00 : gcd zero zero ≡ loop
-- E 1.2: CPU time limit exceeded (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove gcd-00 #-}

postulate gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-S0 #-}

postulate gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-0S #-}

postulate
  gcd-S>S : ∀ m n → GT (succ₁ m) (succ₁ n) →
            gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
-- E 1.2: CPU time limit exceeded (180 sec).
-- E 1.2: CPU time limit exceeded (300 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 300 sec).
{-# ATP prove gcd-S>S #-}

postulate
  gcd-S≯S : ∀ {m n} → NGT (succ₁ m) (succ₁ n) →
            gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
{-# ATP prove gcd-S≯S #-}
