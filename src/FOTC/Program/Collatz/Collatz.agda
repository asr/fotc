------------------------------------------------------------------------------
-- The Collatz function: A function without a termination proof
------------------------------------------------------------------------------

module FOTC.Program.Collatz.Collatz where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------
-- The Collatz function.
postulate
  collatz    : D → D
  collatz-eq : ∀ n → collatz n ≡
                     if (iszero₁ n)
                        then one
                        else (if (iszero₁ (pred₁ n))
                                 then one
                                 else (if (even n)
                                          then collatz (n / two)
                                          else collatz (three * n + one)))
{-# ATP axiom collatz-eq #-}
