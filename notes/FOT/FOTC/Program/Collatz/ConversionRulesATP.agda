------------------------------------------------------------------------------
-- Conversion rules for the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Collatz.ConversionRulesATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

postulate
  collatz-even : ∀ {n} → n > [1] → Even n → collatz n ≡ collatz (div n [2])
-- The ATPs cannot prove this equation.
-- {-# ATP prove collatz-even #-}
