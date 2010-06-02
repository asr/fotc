------------------------------------------------------------------------------
-- Equations for the gcd
------------------------------------------------------------------------------

module Examples.GCD.EquationsPCF where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

------------------------------------------------------------------------------

postulate
  gcd : D → D → D

  gcd-00 : gcd zero zero ≡ error

  gcd-S0 : (n : D) → gcd (succ n) zero ≡ succ n

  gcd-0S : (n : D) → gcd zero (succ n) ≡ succ n

  gcd-S>S : (m n : D) → GT (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m - succ n) (succ n)

  gcd-S≤S : (m n : D) → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n - succ m)

{-# ATP axiom gcd-00 #-}
{-# ATP axiom gcd-S0 #-}
{-# ATP axiom gcd-0S #-}
{-# ATP axiom gcd-S>S #-}
{-# ATP axiom gcd-S≤S #-}
