------------------------------------------------------------------------------
-- Definition of the gcd of two natural numbers using the Euclid's algorithm
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.GCD.Partial.GCD where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Loop
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- In GHC ≤ 7.0.4 the gcd is a partial function, i.e. gcd 0 0 = undefined.

postulate
  gcd    : D → D → D
  gcd-eq : ∀ m n → gcd m n ≡
           (if (iszero₁ n)
              then (if (iszero₁ m)
                      then error
                      else m)
              else (if (iszero₁ m)
                      then n
                      else (if (gt m n)
                              then gcd (m ∸ n) n
                              else gcd m (n ∸ m))))
