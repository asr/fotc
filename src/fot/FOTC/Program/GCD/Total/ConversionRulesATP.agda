------------------------------------------------------------------------------
-- Conversion rules for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Total.ConversionRulesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.GCD.Total.GCD

------------------------------------------------------------------------------
-- NB. These equations are not used by the ATPs. They use the official
-- equation.
private
  postulate gcd-00 : gcd zero zero ≡ zero
  {-# ATP prove gcd-00 #-}

  postulate gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
  {-# ATP prove gcd-S0 #-}

  postulate gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
  {-# ATP prove gcd-0S #-}

  postulate
    gcd-S>S : ∀ m n → GT (succ₁ m) (succ₁ n) →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
  {-# ATP prove gcd-S>S #-}

  postulate
    gcd-S≯S : ∀ m n → NGT (succ₁ m) (succ₁ n) →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
  {-# ATP prove gcd-S≯S #-}
