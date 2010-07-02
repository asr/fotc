------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
------------------------------------------------------------------------------

module Examples.GCD where

open import LTC.Minimal

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities

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
