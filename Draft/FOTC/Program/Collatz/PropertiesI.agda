------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

open import Draft.FOTC.Program.Collatz.Collatz
open import Draft.FOTC.Program.Collatz.Data.Nat
open import Draft.FOTC.Program.Collatz.Data.Nat.PropertiesI

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → ∃D (λ k → N k ∧ n ≡ two ^ k) → collatz n ≡ one
collatz-2^x zN _ = collatz-0
collatz-2^x (sN {n} Nn) (.zero , zN , Sn≡2^0) =
  subst (λ t → collatz t ≡ one)
        (cong succ (sym (Sx≡2^0→x≡0 Nn Sn≡2^0)))
        collatz-1
collatz-2^x (sN {n} Nn) (.(succ k) , sN {k} Nk , Sn≡2^k+1) =
  begin
    collatz (succ n)
      ≡⟨ cong collatz Sn≡2^k+1 ⟩
    collatz (two ^ (succ k))
      ≡⟨ collatz-even (2^x-Even k) ⟩
    collatz ((two ^ (succ k)) / two)
      ≡⟨ cong collatz (2^[x+1]/2≡x Nk) ⟩
    collatz (two ^ k)
      ≡⟨ collatz-2^x (^-N (sN (sN zN)) Nk) (k , Nk , refl) ⟩
    one
  ∎
