------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
-- using the Euclid's algorithm
------------------------------------------------------------------------------

module Examples.GCD.GCD where

open import LTC.Base

open import LTC.Data.Nat using ( _-_ )
open import LTC.Data.Nat.Inequalities using ( GT ; LE )

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

------------------------------------------------------------------------------
-- Common functions used by the gcd example

¬x≡0∧y≡0 : D → D → Set
¬x≡0∧y≡0 d e = ¬ (d ≡ zero ∧ e ≡ zero)
