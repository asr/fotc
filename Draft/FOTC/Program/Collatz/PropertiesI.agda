------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

open import Draft.FOTC.Program.Collatz.Collatz
open import Draft.FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

postulate
  collatz-2^x : ∀ {n} → N n → ∃D (λ k → n ≡ two ^ k → collatz n ≡ one)
