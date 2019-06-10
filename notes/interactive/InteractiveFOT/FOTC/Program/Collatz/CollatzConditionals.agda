------------------------------------------------------------------------------
-- The Collatz function: A function without a termination proof
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Program.Collatz.CollatzConditionals where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------
-- The Collatz function.
postulate
  collatz    : D → D
  collatz-eq : ∀ n → collatz n ≡
                     (if (iszero₁ n)
                        then 1'
                        else (if (iszero₁ (pred₁ n))
                                then 1'
                                else (if (even n)
                                        then collatz (div n 2')
                                        else collatz (3' * n + 1'))))
