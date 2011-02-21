------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
-- using the Euclid's algorithm
------------------------------------------------------------------------------

module FOTC.Program.GCD.GCD where

open import FOTC.Base

open import FOTC.Data.Nat using ( _∸_ )
open import FOTC.Data.Nat.Inequalities using ( GT ; LE )

------------------------------------------------------------------------------

postulate
  gcd     : D → D → D

  gcd-00  : gcd zero zero ≡ error

  gcd-S0  : ∀ n → gcd (succ n) zero ≡ succ n

  gcd-0S  : ∀ n → gcd zero (succ n) ≡ succ n

  gcd-S>S : ∀ m n → GT (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)

  gcd-S≤S : ∀ m n → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)

{-# ATP axiom gcd-00 #-}
{-# ATP axiom gcd-S0 #-}
{-# ATP axiom gcd-0S #-}
{-# ATP axiom gcd-S>S #-}
{-# ATP axiom gcd-S≤S #-}
