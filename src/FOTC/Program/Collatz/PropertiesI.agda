------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

module FOTC.Program.Collatz.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityI

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesI
open import FOTC.Program.Collatz.EquationsI

open import FOTC.Relation.Binary.EqReasoning hiding ( prf )

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → ∃ (λ k → N k ∧ n ≡ two ^ k) → collatz n ≡ one
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
      ≡⟨ cong collatz prf ⟩
    collatz (succ (succ ((two ^ (succ k)) ∸ two)))
      ≡⟨ collatz-even (x-Even→SSx-Even (∸-N (^-N 2-N (sN Nk)) 2-N)
                      (∸-Even (^-N 2-N (sN Nk)) 2-N (2^[x+1]-Even Nk)
                              (x-Even→SSx-Even zN even-0)))
      ⟩
    collatz ((succ (succ ((two ^ (succ k)) ∸ two))) / two)
      ≡⟨ cong collatz
              (subst (λ t → succ (succ (two ^ succ k ∸ two)) / two ≡ t / two)
                     (sym prf)
                     refl)
              ⟩
    collatz ((two ^ (succ k)) / two)
      ≡⟨ cong collatz (2^[x+1]/2≡2^x Nk) ⟩
    collatz (two ^ k)
      ≡⟨ collatz-2^x (^-N 2-N Nk) (k , Nk , refl) ⟩
    one
  ∎
  where
  prf : two ^ succ k ≡ succ (succ (two ^ succ k ∸ two))
  prf = (+∸2 (^-N 2-N (sN Nk)) (2^x≠0 (sN Nk)) (2^[x+1]≠1 Nk))
