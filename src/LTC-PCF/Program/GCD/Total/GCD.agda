------------------------------------------------------------------------------
-- Definition of the gcd of two natural numbers using the Euclid's algorithm
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Total.GCD where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Loop

------------------------------------------------------------------------------
-- In GHC ≥ 7.2.1 the gcd is a total function, i.e. gcd 0 0 = 0.

-- Instead of defining gcdh : ((D → D → D) → (D → D → D)) → D → D → D,
-- we use the LTC-PCF λ-abstraction and application to avoid use a
-- polymorphic fixed-point operator.

gcdh : D → D
gcdh g = lam (λ m → lam (λ n →
           if (iszero₁ n)
              then (if (iszero₁ m)
                       then zero
                       else m)
              else (if (iszero₁ m)
                       then n
                       else (if (m > n)
                                then g · (m ∸ n) · n
                                else g · m · (n ∸ m)))))

gcd : D → D → D
gcd m n = fix gcdh · m · n

