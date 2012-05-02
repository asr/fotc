------------------------------------------------------------------------------
-- Definition of the gcd of two natural numbers using the Euclid's algorithm
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Partial.GCD where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Loop

------------------------------------------------------------------------------
-- In GHC ≤ 7.0.4 the gcd is a partial function, i.e. gcd 0 0 = undefined.

-- Instead of define gcdh : ((D → D → D) → (D → D → D)) → D → D → D,
-- we use the LTC-PCF abstraction lam and application _·_ to avoid use
-- a polymorphic fixed-point operator.

gcdh : D → D
gcdh g = lam (λ d → lam (λ e →
           if (iszero₁ e)
              then (if (iszero₁ d)
                       then loop
                       else d)
              else (if (iszero₁ d)
                       then e
                       else (if (d > e)
                                then g · (d ∸ e) · e
                                else g · d · (e ∸ d)))))

gcd : D → D → D
gcd d e = fix gcdh · d · e
