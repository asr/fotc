------------------------------------------------------------------------------
-- Equations for the Collatz function
------------------------------------------------------------------------------

module FOTC.Program.Collatz.EquationsI where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Data.Nat

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

private
  -- The steps

  -- Initially, the equation collatz-eq is used.

  collatz-s₁ : D → D
  collatz-s₁ n = if (isZero n)
                    then one
                    else (if (isZero (pred n))
                             then one
                             else (if (even n)
                                      then collatz (n / two)
                                      else collatz (three * n + one)))

  -- Conversion (first if_then_else) 'isZero n = b'.
  collatz-s₂ : D → D → D
  collatz-s₂ n b = if b
                      then one
                      else (if (isZero (pred n))
                               then one
                               else (if (even n)
                                        then collatz (n / two)
                                        else collatz (three * n + one)))

  -- Conversion first if_then_else when 'if true ...'.
  collatz-s₃ : D → D
  collatz-s₃ n = one

  -- Conversion first if_then_else when 'if false ...'.
  collatz-s₄ : D → D
  collatz-s₄ n = if (isZero (pred n))
                    then one
                    else (if (even n)
                             then collatz (n / two)
                             else collatz (three * n + one))

  -- Conversion (second if_then_else) 'isZero (pred n) = b'.
  collatz-s₅ : D → D → D
  collatz-s₅ n b = if b
                      then one
                      else (if (even n)
                               then collatz (n / two)
                               else collatz (three * n + one))

  -- Conversion second if_then_else when 'if true ...'.
  collatz-s₆ : D → D
  collatz-s₆ n = one

  -- Conversion second if_then_else when 'if false ...'.
  collatz-s₇ : D → D
  collatz-s₇ n = if (even n)
                    then collatz (n / two)
                    else collatz (three * n + one)

  -- Conversion (third if_then_else) 'even n b'.
  collatz-s₈ : D → D → D
  collatz-s₈ n b = if b
                      then collatz (n / two)
                      else collatz (three * n + one)

  -- Conversion third if_then_else when 'if true ...'.
  collatz-s₉ : D → D
  collatz-s₉ n = collatz (n / two)

  -- Conversion third if_then_else when 'if false ...'.
  collatz-s₁₀ : D → D
  collatz-s₁₀ n = collatz (three * n + one)

  ----------------------------------------------------------------------------
  -- The execution steps

  -- Application of the equation collatz-eq.
  proof₀₋₁ : ∀ n → collatz n ≡ collatz-s₁ n
  proof₀₋₁ n = collatz-eq n

  -- Conversion (first if_then_else) 'isZero n = b' using that proof.
  proof₁₋₂ : ∀ {n} {b} → isZero n ≡ b → collatz-s₁ n ≡ collatz-s₂ n b
  proof₁₋₂ {n} {b} h = subst (λ x → collatz-s₂ n x ≡ collatz-s₂ n b)
                             (sym h)
                             refl

  -- Conversion first if_then_else when 'if true ...' using if-true.
  proof₂₋₃ : ∀ n → collatz-s₂ n true ≡ collatz-s₃ n
  proof₂₋₃ n = if-true (collatz-s₃ n)

  -- Conversion first if_then_else when 'if true ...' using if-false.
  proof₂₋₄ : ∀ n → collatz-s₂ n false ≡ collatz-s₄ n
  proof₂₋₄ n = if-false (collatz-s₄ n)

  -- Conversion (second if_then_else) 'isZero (pred n) = b' using that proof.
  proof₄₋₅ : ∀ {n} {b} → isZero (pred n) ≡ b → collatz-s₄ n ≡ collatz-s₅ n b
  proof₄₋₅ {n} {b} h = subst (λ x → collatz-s₅ n x ≡ collatz-s₅ n b)
                             (sym h)
                             refl

  -- Conversion second if_then_else when 'if true ...' using if-true.
  proof₅₋₆ : ∀ n → collatz-s₅ n true ≡ collatz-s₆ n
  proof₅₋₆ n = if-true (collatz-s₆ n)

  -- Conversion second if_then_else when 'if false ...' using if-false.
  proof₅₋₇ : ∀ n → collatz-s₅ n false ≡ collatz-s₇ n
  proof₅₋₇ n = if-false (collatz-s₇ n)

  -- Conversion (third if_then_else) 'even n = b' using that proof.
  proof₇₋₈ : ∀ {n} {b} → even n ≡ b → collatz-s₇ n ≡ collatz-s₈ n b
  proof₇₋₈ {n} {b} h = subst (λ x → collatz-s₈ n x ≡ collatz-s₈ n b)
                             (sym h)
                             refl

  -- Conversion third if_then_else when 'if true ...' using if-true.
  proof₈₋₉ : ∀ n → collatz-s₈ n true ≡ collatz-s₉ n
  proof₈₋₉ n = if-true (collatz-s₉ n)

  -- Conversion third if_then_else when 'if false ...' using if-false.
  proof₈₋₁₀ : ∀ n → collatz-s₈ n false ≡ collatz-s₁₀ n
  proof₈₋₁₀ n = if-false (collatz-s₁₀ n)

------------------------------------------------------------------------------
-- Equations for the Collatz function

collatz-0 : collatz zero ≡ one
collatz-0 =
  begin
    collatz    zero      ≡⟨ proof₀₋₁ zero ⟩
    collatz-s₁ zero      ≡⟨ proof₁₋₂ isZero-0 ⟩
    collatz-s₂ zero true ≡⟨ proof₂₋₃ zero ⟩
    one
  ∎

collatz-1 : collatz one  ≡ one
collatz-1 =
  begin
    collatz    one       ≡⟨ proof₀₋₁ one ⟩
    collatz-s₁ one       ≡⟨ proof₁₋₂ (isZero-S zero) ⟩
    collatz-s₂ one false ≡⟨ proof₂₋₄ one ⟩
    collatz-s₄ one       ≡⟨ proof₄₋₅ (subst (λ x → isZero x ≡ true)
                                                   (sym (pred-S zero))
                                                   isZero-0
                                            )
                         ⟩
    collatz-s₅ one true ≡⟨ proof₅₋₆ one ⟩
    one
  ∎

collatz-even : ∀ {n} → Even (succ (succ n)) →
               collatz (succ (succ n)) ≡ collatz ((succ (succ n)) / two)
collatz-even {n} h =
  begin
    collatz    (succ (succ n))       ≡⟨ proof₀₋₁ (succ (succ n)) ⟩
    collatz-s₁ (succ (succ n))       ≡⟨ proof₁₋₂ (isZero-S (succ n)) ⟩
    collatz-s₂ (succ (succ n)) false ≡⟨ proof₂₋₄ (succ (succ n)) ⟩
    collatz-s₄ (succ (succ n))       ≡⟨ proof₄₋₅ (subst (λ x → isZero x ≡ false)
                                                        (sym (pred-S (succ n)))
                                                        (isZero-S n)
                                                 )
                                     ⟩
    collatz-s₅ (succ (succ n)) false ≡⟨ proof₅₋₇ (succ (succ n)) ⟩
    collatz-s₇ (succ (succ n))       ≡⟨ proof₇₋₈ h ⟩
    collatz-s₈ (succ (succ n)) true  ≡⟨ proof₈₋₉ (succ (succ n)) ⟩
    collatz ((succ (succ n)) / two)
  ∎

collatz-noteven : ∀ {n} → NotEven (succ (succ n)) →
                  collatz (succ (succ n)) ≡
                  collatz (three * (succ (succ n)) + one)
collatz-noteven {n} h =
  begin
    collatz    (succ (succ n))       ≡⟨ proof₀₋₁ (succ (succ n)) ⟩
    collatz-s₁ (succ (succ n))       ≡⟨ proof₁₋₂ (isZero-S (succ n)) ⟩
    collatz-s₂ (succ (succ n)) false ≡⟨ proof₂₋₄ (succ (succ n)) ⟩
    collatz-s₄ (succ (succ n))       ≡⟨ proof₄₋₅ (subst (λ x → isZero x ≡ false)
                                                        (sym (pred-S (succ n)))
                                                        (isZero-S n)
                                                 )
                                     ⟩
    collatz-s₅ (succ (succ n)) false ≡⟨ proof₅₋₇ (succ (succ n)) ⟩
    collatz-s₇ (succ (succ n))       ≡⟨ proof₇₋₈ h ⟩
    collatz-s₈ (succ (succ n)) false ≡⟨ proof₈₋₁₀ (succ (succ n)) ⟩
    collatz (three * (succ (succ n)) + one)
  ∎
