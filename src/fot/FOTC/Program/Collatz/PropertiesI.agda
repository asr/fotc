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
open import FOTC.Program.Collatz.ConversionRulesI
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.PropertiesI

------------------------------------------------------------------------------

collatzCong : ∀ {m n} → m ≡ n → collatz m ≡ collatz n
collatzCong refl = refl

collatz-2^x : ∀ {n} → N n → (∃[ k ] N k ∧ n ≡ [2] ^ k) → collatz n ≡ [1]
collatz-2^x nzero _ = collatz-0
collatz-2^x (nsucc {n} Nn) (.zero , nzero , Sn≡2^0) =
  subst (λ t → collatz t ≡ [1])
        (succCong (sym (Sx≡2^0→x≡0 Nn Sn≡2^0)))
        collatz-1
collatz-2^x (nsucc {n} Nn) (.(succ₁ k) , nsucc {k} Nk , Sn≡2^k+1) =
  collatz (succ₁ n)
    ≡⟨ collatzCong Sn≡2^k+1 ⟩
  collatz ([2] ^ (succ₁ k))
    ≡⟨ collatzCong prf ⟩
  collatz (succ₁ (succ₁ (([2] ^ (succ₁ k)) ∸ [2])))
    ≡⟨ collatz-even (x-Even→SSx-Even (∸-N (^-N 2-N (nsucc Nk)) 2-N)
                    (∸-Even (^-N 2-N (nsucc Nk)) 2-N (2^[x+1]-Even Nk)
                            (x-Even→SSx-Even nzero even-0)))
    ⟩
  collatz ((succ₁ (succ₁ (([2] ^ (succ₁ k)) ∸ [2]))) / [2])
    ≡⟨ collatzCong (/-leftCong (sym prf)) ⟩
  collatz (([2] ^ (succ₁ k)) / [2])
    ≡⟨ collatzCong (2^[x+1]/2≡2^x Nk) ⟩
  collatz ([2] ^ k)
    ≡⟨ collatz-2^x (^-N 2-N Nk) (k , Nk , refl) ⟩
  [1] ∎
  where
  prf : [2] ^ succ₁ k ≡ succ₁ (succ₁ ([2] ^ succ₁ k ∸ [2]))
  prf = +∸2 (^-N 2-N (nsucc Nk)) (2^x≢0 (nsucc Nk)) (2^[x+1]≢1 Nk)
