------------------------------------------------------------------------------
-- Conversion rules for the Collatz function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.ConversionRulesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

private
  -- The steps

  -- Initially, the equation collatz-eq is used.

  collatz-s₁ : D → D
  collatz-s₁ n = if (iszero₁ n)
                    then one
                    else (if (iszero₁ (pred₁ n))
                             then one
                             else (if (even n)
                                      then collatz (n / two)
                                      else collatz (three * n + one)))

  -- First if_then_else_ iszero₁ n = b.
  collatz-s₂ : D → D → D
  collatz-s₂ n b = if b
                      then one
                      else (if (iszero₁ (pred₁ n))
                               then one
                               else (if (even n)
                                        then collatz (n / two)
                                        else collatz (three * n + one)))

  -- First if_then_else_ when if true ....
  collatz-s₃ : D → D
  collatz-s₃ n = one

  -- First if_then_else_ when if false ....
  collatz-s₄ : D → D
  collatz-s₄ n = if (iszero₁ (pred₁ n))
                    then one
                    else (if (even n)
                             then collatz (n / two)
                             else collatz (three * n + one))

  -- Second if_then_else_ iszero₁ (pred₁ n) = b.
  collatz-s₅ : D → D → D
  collatz-s₅ n b = if b
                      then one
                      else (if (even n)
                               then collatz (n / two)
                               else collatz (three * n + one))

  -- Second if_then_else_ when if true ....
  collatz-s₆ : D → D
  collatz-s₆ n = one

  -- Second if_then_else_ when if false ....
  collatz-s₇ : D → D
  collatz-s₇ n = if (even n)
                    then collatz (n / two)
                    else collatz (three * n + one)

  -- Third if_then_else_ even n b.
  collatz-s₈ : D → D → D
  collatz-s₈ n b = if b
                      then collatz (n / two)
                      else collatz (three * n + one)

  -- Third if_then_else_ when if true ....
  collatz-s₉ : D → D
  collatz-s₉ n = collatz (n / two)

  -- Third if_then_else_ when if false ....
  collatz-s₁₀ : D → D
  collatz-s₁₀ n = collatz (three * n + one)

  ----------------------------------------------------------------------------
  -- The execution steps

  proof₀₋₁ : ∀ n → collatz n ≡ collatz-s₁ n
  proof₀₋₁ n = collatz-eq n

  proof₁₋₂ : ∀ {n b} → iszero₁ n ≡ b → collatz-s₁ n ≡ collatz-s₂ n b
  proof₁₋₂ {n} {b} h = subst (λ x → collatz-s₂ n x ≡ collatz-s₂ n b)
                             (sym h)
                             refl

  proof₂₋₃ : ∀ n → collatz-s₂ n true ≡ collatz-s₃ n
  proof₂₋₃ n = if-true (collatz-s₃ n)

  proof₂₋₄ : ∀ n → collatz-s₂ n false ≡ collatz-s₄ n
  proof₂₋₄ n = if-false (collatz-s₄ n)

  proof₄₋₅ : ∀ {n b} → iszero₁ (pred₁ n) ≡ b → collatz-s₄ n ≡ collatz-s₅ n b
  proof₄₋₅ {n} {b} h = subst (λ x → collatz-s₅ n x ≡ collatz-s₅ n b)
                             (sym h)
                             refl

  proof₅₋₆ : ∀ n → collatz-s₅ n true ≡ collatz-s₆ n
  proof₅₋₆ n = if-true (collatz-s₆ n)

  proof₅₋₇ : ∀ n → collatz-s₅ n false ≡ collatz-s₇ n
  proof₅₋₇ n = if-false (collatz-s₇ n)

  proof₇₋₈ : ∀ {n b} → even n ≡ b → collatz-s₇ n ≡ collatz-s₈ n b
  proof₇₋₈ {n} {b} h = subst (λ x → collatz-s₈ n x ≡ collatz-s₈ n b)
                             (sym h)
                             refl

  proof₈₋₉ : ∀ n → collatz-s₈ n true ≡ collatz-s₉ n
  proof₈₋₉ n = if-true (collatz-s₉ n)

  proof₈₋₁₀ : ∀ n → collatz-s₈ n false ≡ collatz-s₁₀ n
  proof₈₋₁₀ n = if-false (collatz-s₁₀ n)

------------------------------------------------------------------------------
-- Conversion rules for the Collatz function

collatz-0 : collatz zero ≡ one
collatz-0 =
  collatz    zero      ≡⟨ proof₀₋₁ zero ⟩
  collatz-s₁ zero      ≡⟨ proof₁₋₂ iszero-0 ⟩
  collatz-s₂ zero true ≡⟨ proof₂₋₃ zero ⟩
  one                  ∎

collatz-1 : collatz one  ≡ one
collatz-1 =
  collatz one
    ≡⟨ proof₀₋₁ one ⟩
  collatz-s₁ one
    ≡⟨ proof₁₋₂ (iszero-S zero) ⟩
  collatz-s₂ one false
    ≡⟨ proof₂₋₄ one  ⟩
  collatz-s₄ one
    ≡⟨ proof₄₋₅ (subst (λ x → iszero₁ x ≡ true) (sym (pred-S zero)) iszero-0) ⟩
  collatz-s₅ one true
    ≡⟨ proof₅₋₆ one ⟩
  one ∎

collatz-even : ∀ {n} → Even (succ₁ (succ₁ n)) →
               collatz (succ₁ (succ₁ n)) ≡ collatz ((succ₁ (succ₁ n)) / two)
collatz-even {n} h =
  collatz (succ₁ (succ₁ n))
    ≡⟨ proof₀₋₁ (succ₁ (succ₁ n)) ⟩
  collatz-s₁ (succ₁ (succ₁ n))
    ≡⟨ proof₁₋₂ (iszero-S (succ₁ n)) ⟩
  collatz-s₂ (succ₁ (succ₁ n)) false
    ≡⟨ proof₂₋₄ (succ₁ (succ₁ n)) ⟩
  collatz-s₄ (succ₁ (succ₁ n))
    ≡⟨ proof₄₋₅ (subst (λ x → iszero₁ x ≡ false)
                       (sym (pred-S (succ₁ n)))
                       (iszero-S n))
    ⟩
  collatz-s₅ (succ₁ (succ₁ n)) false
    ≡⟨ proof₅₋₇ (succ₁ (succ₁ n)) ⟩
  collatz-s₇ (succ₁ (succ₁ n))
    ≡⟨ proof₇₋₈ h ⟩
  collatz-s₈ (succ₁ (succ₁ n)) true
    ≡⟨ proof₈₋₉ (succ₁ (succ₁ n)) ⟩
  collatz ((succ₁ (succ₁ n)) / two) ∎

collatz-noteven : ∀ {n} → NotEven (succ₁ (succ₁ n)) →
                  collatz (succ₁ (succ₁ n)) ≡
                  collatz (three * (succ₁ (succ₁ n)) + one)
collatz-noteven {n} h =
  collatz (succ₁ (succ₁ n))
    ≡⟨ proof₀₋₁ (succ₁ (succ₁ n)) ⟩
  collatz-s₁ (succ₁ (succ₁ n))
    ≡⟨ proof₁₋₂ (iszero-S (succ₁ n)) ⟩
  collatz-s₂ (succ₁ (succ₁ n)) false
    ≡⟨ proof₂₋₄ (succ₁ (succ₁ n)) ⟩
  collatz-s₄ (succ₁ (succ₁ n))
    ≡⟨ proof₄₋₅ (subst (λ x → iszero₁ x ≡ false)
                       (sym (pred-S (succ₁ n)))
                       (iszero-S n))
    ⟩
  collatz-s₅ (succ₁ (succ₁ n)) false
    ≡⟨ proof₅₋₇ (succ₁ (succ₁ n)) ⟩
  collatz-s₇ (succ₁ (succ₁ n))
    ≡⟨ proof₇₋₈ h ⟩
  collatz-s₈ (succ₁ (succ₁ n)) false
    ≡⟨ proof₈₋₁₀ (succ₁ (succ₁ n)) ⟩
  collatz (three * (succ₁ (succ₁ n)) + one) ∎