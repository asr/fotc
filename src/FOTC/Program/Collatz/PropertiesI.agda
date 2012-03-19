------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityI
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesI
open import FOTC.Program.Collatz.EquationsI

------------------------------------------------------------------------------

collatz-2^x : ∀ {n} → N n → (∃[ k ] N k ∧ n ≡ two ^ k) → collatz n ≡ one
collatz-2^x zN _ = collatz-0
collatz-2^x (sN {n} Nn) (.zero , zN , Sn≡2^0) =
  subst (λ t → collatz t ≡ one)
        (cong succ₁ (sym (Sx≡2^0→x≡0 Nn Sn≡2^0)))
        collatz-1
collatz-2^x (sN {n} Nn) (.(succ₁ k) , sN {k} Nk , Sn≡2^k+1) =
  collatz (succ₁ n)
    ≡⟨ cong collatz Sn≡2^k+1 ⟩
  collatz (two ^ (succ₁ k))
    ≡⟨ cong collatz prf ⟩
  collatz (succ₁ (succ₁ ((two ^ (succ₁ k)) ∸ two)))
    ≡⟨ collatz-even (x-Even→SSx-Even (∸-N (^-N 2-N (sN Nk)) 2-N)
                    (∸-Even (^-N 2-N (sN Nk)) 2-N (2^[x+1]-Even Nk)
                            (x-Even→SSx-Even zN even-0)))
    ⟩
  collatz ((succ₁ (succ₁ ((two ^ (succ₁ k)) ∸ two))) / two)
    ≡⟨ cong collatz
            (subst (λ t → succ₁ (succ₁ (two ^ succ₁ k ∸ two)) / two ≡ t / two)
                   (sym prf)
                   refl)
            ⟩
  collatz ((two ^ (succ₁ k)) / two)
    ≡⟨ cong collatz (2^[x+1]/2≡2^x Nk) ⟩
  collatz (two ^ k)
    ≡⟨ collatz-2^x (^-N 2-N Nk) (k , Nk , refl) ⟩
  one ∎
  where
  prf : two ^ succ₁ k ≡ succ₁ (succ₁ (two ^ succ₁ k ∸ two))
  prf = +∸2 (^-N 2-N (sN Nk)) (2^x≢0 (sN Nk)) (2^[x+1]≢1 Nk)
