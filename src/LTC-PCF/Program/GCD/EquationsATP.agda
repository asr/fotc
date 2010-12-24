------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.EquationsATP where

open import LTC.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat
  using ( _∸_
        ; N ; sN -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Inequalities using ( GT ; LE )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP using ( x≤y→x≯y )

open import LTC-PCF.Program.GCD.GCD using ( gcd )

------------------------------------------------------------------------------

postulate
  gcd-00 : gcd zero zero ≡ error
-- E 1.2: CPU time limit exceeded (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove gcd-00 #-}

postulate
 gcd-S0 : (n : D) → gcd (succ n) zero ≡ succ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-S0 #-}

postulate
  gcd-0S : (n : D) → gcd zero (succ n) ≡ succ n
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove gcd-0S #-}

postulate
  gcd-S>S : (m n : D) → GT (succ m) (succ n) →
             gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)
-- E 1.2: CPU time limit exceeded (180 sec).
-- E 1.2: CPU time limit exceeded (300 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 300 sec).
{-# ATP prove gcd-S>S #-}

postulate
  gcd-S≤S : {m n : D} → N m → N n → LE (succ m) (succ n) →
            gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)
-- E 1.2: CPU time limit exceeded (180 sec).
-- E 1.2: CPU time limit exceeded (300 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 300 sec).
-- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 180 sec).
-- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 300 sec).
-- A old version of the postulate was proved using on-line Vampire.
-- TODO: To find an ATP for to prove this postulate
-- {-# ATP prove gcd-S≤S #-}
