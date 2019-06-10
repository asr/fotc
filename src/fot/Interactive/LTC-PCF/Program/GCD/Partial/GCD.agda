------------------------------------------------------------------------------
-- Definition of the gcd of two natural numbers using the Euclid's algorithm
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Program.GCD.Partial.GCD where

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Data.Nat
open import Interactive.LTC-PCF.Data.Nat.Inequalities
open import Interactive.LTC-PCF.Loop

------------------------------------------------------------------------------
-- In GHC ≤ 7.0.4 the gcd is a partial function, i.e. gcd 0 0 = undefined.

-- Let T = D → D → D be a type. Instead of defining gcdh : T → T, we
-- use the Interactive.LTC-PCF.λ-abstraction and application to avoid use a
-- polymorphic fixed-point operator.

gcdh : D → D
gcdh g = lam (λ m → lam (λ n →
           if (iszero₁ n)
             then (if (iszero₁ m) then error else m)
             else (if (iszero₁ m)
                     then n
                     else (if (gt m n)
                             then g · (m ∸ n) · n
                             else g · m · (n ∸ m)))))

gcd : D → D → D
gcd m n = fix gcdh · m · n
