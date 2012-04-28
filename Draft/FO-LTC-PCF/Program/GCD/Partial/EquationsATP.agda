------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Program.GCD.Partial.EquationsATP where

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities
open import Draft.FO-LTC-PCF.Loop
open import Draft.FO-LTC-PCF.Program.GCD.Partial.GCD

------------------------------------------------------------------------------

postulate gcd-00 : gcd zero zero ≡ loop
{-# ATP prove gcd-00 #-}

postulate gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
{-# ATP prove gcd-S0 #-}

postulate gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
{-# ATP prove gcd-0S #-}

-- 2012-02-23: Only Vampire 0.6 (revision 903) proved the theorem (180 sec).
postulate
  gcd-S>S : ∀ m n → GT (succ₁ m) (succ₁ n) →
            gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
{-# ATP prove gcd-S>S #-}

postulate
  gcd-S≯S : ∀ {m n} → NGT (succ₁ m) (succ₁ n) →
            gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
{-# ATP prove gcd-S≯S #-}
