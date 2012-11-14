------------------------------------------------------------------------------
-- Conversion rules for the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.ConversionRulesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------
-- Conversion rules for the Collatz function.
postulate
  collatz-0       : collatz zero ≡ [1]
  collatz-1       : collatz [1]  ≡ [1]
  collatz-even    : ∀ {n} → Even (succ₁ (succ₁ n)) →
                    collatz (succ₁ (succ₁ n)) ≡ collatz ((succ₁ (succ₁ n)) / [2])
  collatz-noteven : ∀ {n} → NotEven (succ₁ (succ₁ n)) →
                    collatz (succ₁ (succ₁ n)) ≡
                    collatz ([3] * (succ₁ (succ₁ n)) + [1])
{-# ATP prove collatz-0 #-}
{-# ATP prove collatz-1 #-}
{-# ATP prove collatz-even #-}
{-# ATP prove collatz-noteven #-}
