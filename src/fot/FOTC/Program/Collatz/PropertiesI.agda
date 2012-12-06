------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
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

helper : ∀ {n} → N n → collatz ([2] ^ succ₁ n) ≡ collatz ([2] ^ n)
helper nzero =
  collatz ([2] ^ [1])   ≡⟨ collatzCong (x^1≡x 2-N) ⟩
  collatz [2]           ≡⟨ collatz-even 2-Even ⟩
  collatz (div [2] [2]) ≡⟨ collatzCong (div-x-x≡1 2-N S≢0) ⟩
  collatz ([1])         ≡⟨ collatzCong (sym (^-0 [2])) ⟩
  collatz ([2] ^ [0])   ∎

helper (nsucc {n} Nn) =
  collatz ([2] ^ succ₁ (succ₁ n))
    ≡⟨ collatzCong prf ⟩
  collatz (succ₁ (succ₁ ([2] ^ succ₁ (succ₁ n) ∸ [2])))
    ≡⟨ collatz-even (x-Even→SSx-Even
                       (∸-N (^-N 2-N (nsucc (nsucc Nn))) 2-N)
                       (∸-Even (^-N 2-N (nsucc (nsucc Nn))) 2-N
                               (2^[x+1]-Even (nsucc Nn)) 2-Even)) ⟩
  collatz (div (succ₁ (succ₁ (([2] ^ succ₁ (succ₁ n)) ∸ [2]))) [2])
    ≡⟨ collatzCong (divLeftCong (sym prf)) ⟩
  collatz (div ([2] ^ succ₁ (succ₁ n)) [2])
    ≡⟨ collatzCong (div-2^[x+1]-2≡2^x (nsucc Nn)) ⟩
  collatz ([2] ^ succ₁ n) ∎
  where
  prf : [2] ^ succ₁ (succ₁ n) ≡ succ₁ (succ₁ ([2] ^ succ₁ (succ₁ n) ∸ [2]))
  prf = (+∸2 (^-N 2-N (nsucc (nsucc Nn)))
             (2^x≢0 (nsucc (nsucc Nn)))
             (2^[x+1]≢1 (nsucc Nn)))

collatz-2^x : ∀ {n} → N n → (∃[ k ] N k ∧ n ≡ [2] ^ k) → collatz n ≡ [1]
collatz-2^x {n} Nn (.zero , nzero , h) =
  collatz n           ≡⟨ collatzCong h ⟩
  collatz ([2] ^ [0]) ≡⟨ collatzCong (^-0 [2]) ⟩
  collatz [1]         ≡⟨ collatz-1 ⟩
  [1]                 ∎

collatz-2^x {n} Nn (.(succ₁ k) , nsucc {k} Nk , h) =
  collatz n               ≡⟨ collatzCong h ⟩
  collatz ([2] ^ succ₁ k) ≡⟨ helper Nk ⟩
  collatz ([2] ^ k)       ≡⟨ collatz-2^x (^-N 2-N Nk) (k , (Nk , refl)) ⟩
  [1]                     ∎
