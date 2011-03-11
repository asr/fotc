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
  collatz      : D → D
  collatz-0    :                  collatz zero ≡ one
  collatz-1    :                  collatz one  ≡ one
  collatz-even : ∀ {n} → Even n → collatz n    ≡ collatz (n / two)
  collatz-odd  : ∀ {n} → Odd n →  collatz n    ≡ collatz (three * n + one)
{-# ATP axiom collatz-0 #-}
{-# ATP axiom collatz-1 #-}
{-# ATP axiom collatz-even #-}
{-# ATP axiom collatz-odd #-}
