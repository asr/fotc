------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module FOTC.Program.GCD.EquationsATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

open import FOTC.Program.GCD.GCD

------------------------------------------------------------------------------
-- NB. These equations are not used by the ATPs. They use the official
-- equation.
private
  postulate
    gcd-S0  : ∀ n → gcd (succ n) zero ≡ succ n

    gcd-0S  : ∀ n → gcd zero (succ n) ≡ succ n

    gcd-S>S : ∀ m n → GT (succ m) (succ n) →
              gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)

    gcd-S≯S : ∀ m n → NGT (succ m) (succ n) →
              gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)
  {-# ATP prove gcd-S0 #-}
  {-# ATP prove gcd-0S #-}
  {-# ATP prove gcd-S>S #-}
  {-# ATP prove gcd-S≯S #-}
