------------------------------------------------------------------------------
-- The Collatz function: A function without a termination proof
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Collatz.Collatz where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.UnaryNumbers
open import Combined.FOTC.Program.Collatz.Data.Nat

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
{-# ATP axioms collatz-0 collatz-1 collatz-even collatz-noteven #-}
