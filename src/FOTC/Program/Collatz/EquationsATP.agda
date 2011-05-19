------------------------------------------------------------------------------
-- Equations for the Collatz function
------------------------------------------------------------------------------

module FOTC.Program.Collatz.EquationsATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------
-- Equations for the Collatz function.
postulate
  collatz-0       : collatz zero ≡ one
  collatz-1       : collatz one  ≡ one
  collatz-even    : ∀ {n} → Even (succ (succ n)) →
                    collatz (succ (succ n)) ≡ collatz ((succ (succ n)) / two)
  collatz-noteven : ∀ {n} → NotEven (succ (succ n)) →
                    collatz (succ (succ n)) ≡
                    collatz (three * (succ (succ n)) + one)
{-# ATP prove collatz-0 #-}
{-# ATP prove collatz-1 #-}
{-# ATP prove collatz-even #-}
{-# ATP prove collatz-noteven #-}
