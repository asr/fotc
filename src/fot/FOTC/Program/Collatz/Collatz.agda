------------------------------------------------------------------------------
-- The Collatz function: A function without a termination proof
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.Collatz where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------
-- The Collatz function.
postulate
  collatz         : D → D
  collatz-0       : collatz 0' ≡ 1'
  collatz-1       : collatz 1' ≡ 1'
  collatz-even    : ∀ {n} → Even (succ₁ (succ₁ n)) →
                    collatz (succ₁ (succ₁ n)) ≡
                      collatz (div (succ₁ (succ₁ n)) 2')
  collatz-noteven : ∀ {n} → NotEven (succ₁ (succ₁ n)) →
                    collatz (succ₁ (succ₁ n)) ≡
                      collatz (3' * (succ₁ (succ₁ n)) + 1')
{-# ATP axiom collatz-0 collatz-1 collatz-even collatz-noteven #-}
