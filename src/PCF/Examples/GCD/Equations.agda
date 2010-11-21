------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module PCF.Examples.GCD.Equations where

open import LTC.Base

open import PCF.Examples.GCD.GCD using ( gcd )

open import PCF.LTC.Data.Nat using ( _-_ )
open import PCF.LTC.Data.Nat.Inequalities using ( GT ; LE )

------------------------------------------------------------------------------

postulate
  gcd-00 : gcd zero zero ≡ error
{-# ATP prove gcd-00 #-}

postulate
 gcd-S0 : (n : D) → gcd (succ n) zero ≡ succ n
{-# ATP prove gcd-S0 #-}

postulate
  gcd-0S : (n : D) → gcd zero (succ n) ≡ succ n
{-# ATP prove gcd-0S #-}

postulate
  gcd-S>S : (m n : D) → GT (succ m) (succ n) →
             gcd (succ m) (succ n) ≡ gcd (succ m - succ n) (succ n)
-- E 1.2 no-success due to timeout (300 sec).
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (300 sec).
-- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
-- The postulate was proved using on-line Vampire.
-- TODO: To find an ATP for to prove this postulate
-- {-# ATP prove gcd-S>S #-}

postulate
  gcd-S≤S : (m n : D) → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n - succ m)
-- E 1.2 no-success due to timeout (300 sec).
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (300 sec).
-- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
-- The postulate was proved using on-line Vampire.
-- TODO: To find an ATP for to prove this postulate
-- {-# ATP prove gcd-S≤S #-}
