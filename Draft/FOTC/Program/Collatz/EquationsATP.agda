------------------------------------------------------------------------------
-- Equations for the Collatz function
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.EquationsATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

postulate
  collatz-even    : ∀ {n} → GT n one → Even n →
                    collatz n ≡ collatz (n / two)
-- The ATPs cannot prove this equation.
{-# ATP prove collatz-even #-}
