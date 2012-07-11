------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.EquationsATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.GCD.Partial.GCD

------------------------------------------------------------------------------
-- NB. These equations are not used by the ATPs. They use the official
-- equation.
private
  postulate
    gcd-00  : gcd zero zero ≡ loop

    gcd-S0  : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n

    gcd-0S  : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n

    gcd-S>S : ∀ m n → GT (succ₁ m) (succ₁ n) →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)

    gcd-S≯S : ∀ m n → NGT (succ₁ m) (succ₁ n) →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
  {-# ATP prove gcd-00 #-}
  {-# ATP prove gcd-S0 #-}
  {-# ATP prove gcd-0S #-}
  {-# ATP prove gcd-S>S #-}
  {-# ATP prove gcd-S≯S #-}
