------------------------------------------------------------------------------
-- Subtraction using the fixed-point operator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.LTC-PCF.Data.Nat.SubtractionFixedPointOperator where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties

-- We add 3 to the fixities of the standard library.
infixl 9 _∸_

------------------------------------------------------------------------------
-- Subtraction's definition

∸-helper : D → D
∸-helper f = lam (λ m → lam (λ n →
               if (iszero₁ n)
                 then m
                 else if (iszero₁ m)
                        then zero
                        else f · pred₁ m · pred₁ n))

_∸_ : D → D → D
_∸_ m n = fix ∸-helper · m · n

------------------------------------------------------------------------------
-- Conversion rules from the Agda standard library without use induction.

private
  ----------------------------------------------------------------------------
  -- The steps

  -- See doc in LTC-PCF.Program.GCD.Total.Equations.

  -- Initially, the conversion rule fix-eq is applied.
  ∸-s₁ : D → D → D
  ∸-s₁ m n = ∸-helper (fix ∸-helper) · m · n

  -- First argument application.
  ∸-s₂ : D → D
  ∸-s₂ m = lam (λ n →
               if (iszero₁ n)
                 then m
                 else if (iszero₁ m)
                        then zero
                        else fix ∸-helper · pred₁ m · pred₁ n)

  -- Second argument application.
  ∸-s₃ : D → D → D
  ∸-s₃ m n = if (iszero₁ n)
               then m
               else if (iszero₁ m)
                      then zero
                      else fix ∸-helper · pred₁ m · pred₁ n

  -- First if_then_else_ iszero₁ n = b.
  ∸-s₄ : D → D → D → D
  ∸-s₄ m n b = if b
                 then m
                 else if (iszero₁ m)
                        then zero
                        else fix ∸-helper · pred₁ m · pred₁ n

  -- First if_then_else_ when if true ...
  ∸-s₅ : D → D
  ∸-s₅ m = m

  -- First if_then_else_ when if false ...
  ∸-s₆ : D → D → D
  ∸-s₆ m n = if (iszero₁ m)
               then zero
               else fix ∸-helper · pred₁ m · pred₁ n

  -- Second if_then_else_ iszero₁ m = b.
  ∸-s₇ : D → D → D → D
  ∸-s₇ m n b = if b then zero else fix ∸-helper · pred₁ m · pred₁ n

  -- Second if_then_else_ when if true ...
  ∸-s₈ : D
  ∸-s₈ = zero

  -- Second if_then_else_ when if false ...
  ∸-s₉ : D → D → D
  ∸-s₉ m n = fix ∸-helper · pred₁ m · pred₁ n

  ----------------------------------------------------------------------------
  -- Congruence properties

  ∸-s₄Cong₃ : ∀ {m n b₁ b₂} → b₁ ≡ b₂ → ∸-s₄ m n b₁ ≡ ∸-s₄ m n b₂
  ∸-s₄Cong₃ refl = refl

  ∸-s₇Cong₃ : ∀ {m n b₁ b₂} → b₁ ≡ b₂ → ∸-s₇ m n b₁ ≡ ∸-s₇ m n b₂
  ∸-s₇Cong₃ refl = refl

  ----------------------------------------------------------------------------
  -- The execution steps

  -- See doc in LTC-PCF.Program.GCD.Total.Equations.

  proof₀₋₁ : ∀ m n → fix ∸-helper · m · n ≡ ∸-s₁ m n
  proof₀₋₁ m n = subst (λ x → x · m · n ≡ ∸-helper (fix ∸-helper) · m · n)
                       (sym (fix-eq ∸-helper))
                       refl

  proof₁₋₂ : ∀ m n → ∸-s₁ m n ≡ ∸-s₂ m · n
  proof₁₋₂ m n = subst (λ x → x · n ≡ ∸-s₂ m · n)
                       (sym (beta ∸-s₂ m))
                       refl

  proof₂₋₃ : ∀ m n → ∸-s₂ m · n ≡ ∸-s₃ m n
  proof₂₋₃ m n = beta (∸-s₃ m) n

  proof₃₋₄ : ∀ m n b → iszero₁ n ≡ b → ∸-s₃ m n ≡ ∸-s₄ m n b
  proof₃₋₄ m n b = ∸-s₄Cong₃

  proof₄₊ : ∀ m n → ∸-s₄ m n true ≡ ∸-s₅ m
  proof₄₊ m _ = if-true (∸-s₅ m)

  proof₄₋₆ : ∀ m n → ∸-s₄ m n false ≡ ∸-s₆ m n
  proof₄₋₆ m n = if-false (∸-s₆ m n)

  proof₆₋₇ : ∀ m n b → iszero₁ m ≡ b → ∸-s₆ m n ≡ ∸-s₇ m n b
  proof₆₋₇ m n b = ∸-s₇Cong₃

  proof₇₊ : ∀ m n → ∸-s₇ m n true ≡ ∸-s₈
  proof₇₊ m n = if-true ∸-s₈

  proof₇₋₉ : ∀ m n → ∸-s₇ m n false ≡ ∸-s₉ m n
  proof₇₋₉ m n = if-false (∸-s₉ m n)

------------------------------------------------------------------------------
-- The equations for subtraction

∸-x0 : ∀ n → n ∸ zero ≡ n
∸-x0 n =
  n ∸ zero         ≡⟨ proof₀₋₁ n zero ⟩
  ∸-s₁ n zero      ≡⟨ proof₁₋₂ n zero ⟩
  ∸-s₂ n · zero    ≡⟨ proof₂₋₃ n zero ⟩
  ∸-s₃ n zero      ≡⟨ proof₃₋₄ n zero true iszero-0 ⟩
  ∸-s₄ n zero true ≡⟨ proof₄₊ n zero ⟩
  n                ∎

∸-0S : ∀ n → zero ∸ succ₁ n ≡ zero
∸-0S n =
  zero ∸ succ₁ n            ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
  ∸-s₁ zero (succ₁ n)       ≡⟨ proof₁₋₂ zero (succ₁ n) ⟩
  ∸-s₂ zero · (succ₁ n)     ≡⟨ proof₂₋₃ zero (succ₁ n) ⟩
  ∸-s₃ zero (succ₁ n)       ≡⟨ proof₃₋₄ zero (succ₁ n) false (iszero-S n) ⟩
  ∸-s₄ zero (succ₁ n) false ≡⟨ proof₄₋₆ zero (succ₁ n) ⟩
  ∸-s₆ zero (succ₁ n)       ≡⟨ proof₆₋₇ zero (succ₁ n) true iszero-0 ⟩
  ∸-s₇ zero (succ₁ n) true  ≡⟨ proof₇₊  zero (succ₁ n) ⟩
  zero                      ∎

∸-SS : ∀ m n → succ₁ m ∸ succ₁ n ≡ m ∸ n
∸-SS m n =
  succ₁ m ∸ succ₁ n
    ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  ∸-s₁ (succ₁ m) (succ₁ n)
    ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
  ∸-s₂ (succ₁ m) · (succ₁ n)
    ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
  ∸-s₃ (succ₁ m) (succ₁ n)
    ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  ∸-s₄ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₄₋₆ (succ₁ m) (succ₁ n) ⟩
  ∸-s₆ (succ₁ m) (succ₁ n)
    ≡⟨ proof₆₋₇ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  ∸-s₇ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₇₋₉ (succ₁ m) (succ₁ n) ⟩
  fix ∸-helper · pred₁ (succ₁ m) · pred₁ (succ₁ n)
    ≡⟨ ·-rightCong (pred-S n) ⟩
  fix ∸-helper · pred₁ (succ₁ m) · n
    ≡⟨ ·-leftCong (·-rightCong (pred-S m)) ⟩
  fix ∸-helper · m · n ∎
