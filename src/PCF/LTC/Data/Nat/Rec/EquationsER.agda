------------------------------------------------------------------------------
-- Conversion rules for the recursive operator rec (using equational reasoning)
------------------------------------------------------------------------------

module PCF.LTC.Data.Nat.Rec.EquationsER where

open import LTC.Base

open import Common.Function using ( _$_ )
open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

open import PCF.LTC.Data.Nat.Rec using ( rec ; rech )

----------------------------------------------------------------------------

-- Note: This module was written for the version of gcd using the
-- lambda abstractions, but we can use it with the version of gcd
-- using super-combinators.

private
  -- We follow the same methodology used in
  -- PCF.Examples.GCD.EquationsER (see it for the documentation).

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the conversion rule fix-f is applied.
  rec-s₁ : D → D → D → D
  rec-s₁ n a f =  rech (fix rech) ∙ n ∙ a ∙ f

  -- First argument application.
  rec-s₂ : D → D
  rec-s₂ n = lam (λ a → lam (λ f →
                    (if (isZero n)
                        then a
                        else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f))))

  -- Second argument application.
  rec-s₃ : D → D → D
  rec-s₃ n a = lam (λ f →
                   (if (isZero n)
                       then a
                       else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)))

  -- Third argument application.
  rec-s₄ : D → D → D → D
  rec-s₄ n a f = if (isZero n)
                     then a
                     else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction 'isZero n == b'.
  rec-s₅ : D → D → D → D → D
  rec-s₅ n a f b = if b
                      then a
                      else f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction of 'isZero n == true'
  -- It should be
  -- rec-s₆ : D → D → D → D
  -- rec-s₆ n a f = a
  -- but we do not give a name to this step.

  -- Reduction 'isZero n == false'.
  rec-s₆ : D → D → D → D
  rec-s₆ n a f = f ∙ (pred n) ∙ ((fix rech) ∙ (pred n) ∙ a ∙ f)

  -- Reduction 'pred (succ n) == n'.
  rec-s₇ : D → D → D → D
  rec-s₇ n a f = f ∙ n ∙ ((fix rech) ∙ n ∙ a ∙ f)

  ----------------------------------------------------------------------------
  -- The execution steps

  -- We follow the same methodology used in Inductive.GCD.Equations
  -- (see it for the documentation).

  -- Application of the conversion rule fix-f.
  proof₀₋₁ : (n a f : D) → fix rech ∙ n ∙ a ∙ f ≡ rec-s₁ n a f
  proof₀₋₁ n a f = subst (λ x → x ∙ n ∙ a ∙ f ≡
                                rech (fix rech) ∙ n ∙ a ∙ f )
                         (sym (fix-f rech))
                         refl

  -- Application of the first argument.
  proof₁₋₂ : (n a f : D) → rec-s₁ n a f ≡ rec-s₂ n ∙ a ∙ f
  proof₁₋₂ n a f = subst (λ x → x ∙ a ∙ f ≡ rec-s₂ n ∙ a ∙ f)
                         (sym (beta rec-s₂ n))
                         refl

  -- Application of the second argument.
  proof₂₋₃ : (n a f : D) → rec-s₂ n ∙ a ∙ f ≡ rec-s₃ n a ∙ f
  proof₂₋₃ n a f = subst (λ x → x ∙ f ≡ rec-s₃ n a ∙ f)
                         (sym (beta (rec-s₃ n) a))
                         refl

  -- Application of the third argument.
  proof₃₋₄ : (n a f : D) → rec-s₃ n a ∙ f ≡ rec-s₄ n a f
  proof₃₋₄ n a f = beta (rec-s₄ n a) f

  -- Cases 'isZero n == b' using that proof.
  proof₄₋₅ : (n a f b : D) → isZero n ≡ b → rec-s₄ n a f ≡ rec-s₅ n a f b
  proof₄₋₅ n a f b prf = subst (λ x → rec-s₅ n a f x ≡ rec-s₅ n a f b)
                               (sym prf)
                               refl

  -- Reduction of 'if true ...' using the conversion rule if-true.
  proof₅₊ : (n a f : D) → rec-s₅ n a f true ≡ a
  proof₅₊ n a f = if-true a

   -- Reduction of 'if false ...' using the conversion rule if-false.
  proof₅₋₆ : (n a f : D) → rec-s₅ n a f false ≡ rec-s₆ n a f
  proof₅₋₆ n a f = if-false (rec-s₆ n a f)

  -- Reduction 'pred (succ n) == n' using the conversion rule pred-S.
  proof₆₋₇ : (n a f : D) → rec-s₆ (succ n) a f ≡ rec-s₇ n a f
  proof₆₋₇ n a f = subst (λ x → rec-s₇ x a f ≡ rec-s₇ n a f)
                         (sym (pred-S n))
                         refl

------------------------------------------------------------------------------
-- The conversion rules for rec.

rec-0 : (a : D){f : D} → rec zero a f ≡ a
rec-0 a {f} =
  begin
    (fix rech ∙ zero ∙ a ∙ f) ≡⟨ proof₀₋₁ zero a f ⟩
    rec-s₁ zero a f           ≡⟨ proof₁₋₂ zero a f ⟩
    rec-s₂ zero ∙ a ∙ f       ≡⟨ proof₂₋₃ zero a f ⟩
    rec-s₃ zero a ∙ f         ≡⟨ proof₃₋₄ zero a f ⟩
    rec-s₄ zero a f           ≡⟨ proof₄₋₅ zero a f true isZero-0 ⟩
    rec-s₅ zero a f true      ≡⟨ proof₅₊ zero a f ⟩
    a
  ∎

rec-S : (n a f : D) → rec (succ n) a f ≡ f ∙ n ∙ (rec n a f)
rec-S n a f =
  begin
    (fix rech ∙ (succ n) ∙ a ∙ f) ≡⟨ proof₀₋₁ (succ n) a f ⟩
    rec-s₁ (succ n) a f           ≡⟨ proof₁₋₂ (succ n) a f ⟩
    rec-s₂ (succ n) ∙ a ∙ f       ≡⟨ proof₂₋₃ (succ n) a f ⟩
    rec-s₃ (succ n) a ∙ f         ≡⟨ proof₃₋₄ (succ n) a f ⟩
    rec-s₄ (succ n) a f           ≡⟨ proof₄₋₅ (succ n) a f false (isZero-S n) ⟩
    rec-s₅ (succ n) a f false     ≡⟨ proof₅₋₆ (succ n) a f ⟩
    rec-s₆ (succ n) a f           ≡⟨ proof₆₋₇ n a f ⟩
    rec-s₇ n a f
  ∎
