------------------------------------------------------------------------------
-- Properties of the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Collatz.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Properties
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Properties
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Totality
open import Interactive.FOTC.Program.Collatz.Collatz
open import Interactive.FOTC.Program.Collatz.Data.Nat
open import Interactive.FOTC.Program.Collatz.Data.Nat.Properties

------------------------------------------------------------------------------

collatzCong : ∀ {m n} → m ≡ n → collatz m ≡ collatz n
collatzCong refl = refl

helper : ∀ {n} → N n → collatz (2' ^ succ₁ n) ≡ collatz (2' ^ n)
helper nzero =
  collatz (2' ^ 1')   ≡⟨ collatzCong (x^1≡x 2-N) ⟩
  collatz 2'          ≡⟨ collatz-even 2-Even ⟩
  collatz (div 2' 2') ≡⟨ collatzCong (div-x-x≡1 2-N S≢0) ⟩
  collatz (1')        ≡⟨ collatzCong (sym (^-0 2')) ⟩
  collatz (2' ^ 0')   ∎

helper (nsucc {n} Nn) =
  collatz (2' ^ succ₁ (succ₁ n))
    ≡⟨ collatzCong prf ⟩
  collatz (succ₁ (succ₁ (2' ^ succ₁ (succ₁ n) ∸ 2')))
    ≡⟨ collatz-even (x-Even→SSx-Even
                       (∸-N (^-N 2-N (nsucc (nsucc Nn))) 2-N)
                       (∸-Even (^-N 2-N (nsucc (nsucc Nn))) 2-N
                               (2^[x+1]-Even (nsucc Nn)) 2-Even)) ⟩
  collatz (div (succ₁ (succ₁ ((2' ^ succ₁ (succ₁ n)) ∸ 2'))) 2')
    ≡⟨ collatzCong (divLeftCong (sym prf)) ⟩
  collatz (div (2' ^ succ₁ (succ₁ n)) 2')
    ≡⟨ collatzCong (div-2^[x+1]-2≡2^x (nsucc Nn)) ⟩
  collatz (2' ^ succ₁ n) ∎
  where
  prf : 2' ^ succ₁ (succ₁ n) ≡ succ₁ (succ₁ (2' ^ succ₁ (succ₁ n) ∸ 2'))
  prf = (+∸2 (^-N 2-N (nsucc (nsucc Nn)))
             (2^x≢0 (nsucc (nsucc Nn)))
             (2^[x+1]≢1 (nsucc Nn)))

collatz-2^x : ∀ {n} → N n → collatz (2' ^ n) ≡ 1'
collatz-2^x nzero =
  collatz (2' ^ 0') ≡⟨ collatzCong (^-0 2') ⟩
  collatz 1'        ≡⟨ collatz-1 ⟩
  1'                ∎

collatz-2^x (nsucc {n} Nn) =
  collatz (2' ^ succ₁ n) ≡⟨ helper Nn ⟩
  collatz (2' ^ n)       ≡⟨ collatz-2^x Nn ⟩
  1'                     ∎
