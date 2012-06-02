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

-- Instead of define gcdh : ((D → D → D) → (D → D → D)) → D → D → D,
-- we use the LTC-PCF λ-abstraction and application to avoid use a
-- polymorphic fixed-point operator.

gcdh : D → D
gcdh g = lam (λ d → lam (λ e →
           if (iszero₁ e)
              then (if (iszero₁ d)
                       then zero
                       else d)
              else (if (iszero₁ d)
                       then e
                       else (if (d > e)
                                then g · (d ∸ e) · e
                                else g · d · (e ∸ d)))))

gcd : D → D → D
gcd d e = fix gcdh · d · e
