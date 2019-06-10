------------------------------------------------------------------------------
-- Conversion rules for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.GCD.Total.ConversionRules where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Program.GCD.Total.GCD

------------------------------------------------------------------------------
-- NB. These conversion rules are not used by the ATPs. They use the
-- official equation.
private
  postulate gcd-00 : gcd zero zero ≡ zero
  {-# ATP prove gcd-00 #-}

  postulate gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
  {-# ATP prove gcd-S0 #-}

  postulate gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
  {-# ATP prove gcd-0S #-}

  postulate
    gcd-S>S : ∀ m n → succ₁ m > succ₁ n →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
  {-# ATP prove gcd-S>S #-}

  postulate
    gcd-S≯S : ∀ m n → succ₁ m ≯ succ₁ n →
              gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
  {-# ATP prove gcd-S≯S #-}
