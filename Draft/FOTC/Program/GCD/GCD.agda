{-# OPTIONS --no-termination-check #-}

module Draft.FOTC.Program.GCD.GCD where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

postulate
  loop : D

gcd : D → D → D
gcd m n = if (isZero m)
             then (if (isZero n)
                      then loop
                      else n)
             else (if (isZero n)
                       then m
                       else (if (m > n)
                                then gcd (m ∸ n) n
                                else gcd m (n ∸ n)))
{-# ATP hint gcd #-}

postulate
  gcd-S0  : ∀ n → gcd (succ n) zero ≡ succ n

  gcd-0S  : ∀ n → gcd zero (succ n) ≡ succ n

  gcd-S>S : ∀ m n → GT (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)

  gcd-S≯S : ∀ m n → NGT (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)

-- {-# ATP prove gcd-S0 #-}
{-# ATP prove gcd-0S #-}
-- {-# ATP axiom gcd-S>S #-}
-- {-# ATP axiom gcd-S≯S #-}
