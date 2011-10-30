------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.Partial.EquationsI where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

open import LTC-PCF.Fix
open import LTC-PCF.Fix.Properties

open import LTC-PCF.Program.GCD.Partial.GCD

open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- Note: This module was written for the version of gcd using the
-- lambda abstractions, but we can use it with the version of gcd
-- using super-combinators.

private
  -- Before to prove some properties for 'gcd i j' it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (gcd-s₁,
  -- gcd-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q
  -- (e.g proof₂₋₃ : ∀ m n → gcd-s₂ m n → gcd-s₃ m n).

  -- The functions gcd-00, gcd-S0, gcd-0S, gcd-Sm>Sn and gcd-Sm≯Sn
  -- show the use of the states gcd-s₁, gcd-s₂, ..., and the proofs
  -- associated with the execution steps.

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the conversion rule fix-f is applied.
  gcd-s₁ : D → D → D
  gcd-s₁ m n = gcdh (fix₁ gcdh) · m · n

  -- First argument application.
  gcd-s₂ : D → D
  gcd-s₂ m = lam (λ n →
                    if (iszero₁ n)
                       then (if (iszero₁ m)
                                then loop
                                else m)
                       else (if (iszero₁ m)
                                then n
                                else (if (m > n)
                                         then fix₁ gcdh · (m ∸ n) · n
                                         else fix₁ gcdh · m · (n ∸ m))))

  -- Second argument application.
  gcd-s₃ : D → D → D
  gcd-s₃ m n = if (iszero₁ n)
                  then (if (iszero₁ m)
                           then loop
                           else m)
                  else (if (iszero₁ m)
                           then n
                           else (if (m > n)
                                    then fix₁ gcdh · (m ∸ n) · n
                                    else fix₁ gcdh · m · (n ∸ m)))

  -- Conversion (first if_then_else) 'iszero₁ n = b'.
  gcd-s₄ : D → D → D → D
  gcd-s₄ m n b = if b
                    then (if (iszero₁ m)
                             then loop
                             else m)
                    else (if (iszero₁ m)
                             then n
                             else (if (m > n)
                                      then fix₁ gcdh · (m ∸ n) · n
                                      else fix₁ gcdh · m · (n ∸ m)))

  -- Conversion first if_then_else when 'if true ...'.
  gcd-s₅ : D → D
  gcd-s₅ m  = if (iszero₁ m) then loop else m

  -- Conversion first if_then_else when 'if false ...'.
  gcd-s₆ : D → D → D
  gcd-s₆ m n = if (iszero₁ m)
                  then n
                  else (if (m > n)
                           then fix₁ gcdh · (m ∸ n) · n
                           else fix₁ gcdh · m · (n ∸ m))

  -- Conversion (second if_then_else) 'iszero₁ m = b'.
  gcd-s₇ : D → D → D
  gcd-s₇ m b = if b then loop else m

  -- Conversion (third if_then_else) 'iszero₁ m = b'.
  gcd-s₈ : D → D → D → D
  gcd-s₈ m n b = if b
                    then n
                    else (if (m > n)
                             then fix₁ gcdh · (m ∸ n) · n
                             else fix₁ gcdh · m · (n ∸ m))

  -- Conversion third if_then_else, when 'if false ...'.
  gcd-s₉ : D → D → D
  gcd-s₉ m n = if (m > n)
                   then fix₁ gcdh · (m ∸ n) · n
                   else fix₁ gcdh · m · (n ∸ m)

  -- Conversion (fourth if_then_else) 'gt m n = b'.
  gcd-s₁₀ : D → D → D → D
  gcd-s₁₀ m n b = if b
                     then fix₁ gcdh · (m ∸ n) · n
                     else fix₁ gcdh · m · (n ∸ m)

  ----------------------------------------------------------------------------
  -- The execution steps

  {-
  To prove the execution steps
  (e.g. proof₃₋₄ : ∀ m n → gcd-s₃ m n → gcd_s₄ m n),
  we usually need to prove that

                         C [m] ≡ C [n] (1)

  given that
                             m ≡ n,    (2)

  where (2) is a conversion rule usually.
  We prove (1) using

  subst : ∀ {x y} (D : A → Set) → x ≡ y → P x → P y

  where
   P is given by λ m → C [m ] ≡ C [n],
   x ≡ y is given n ≡ m (actually, we use sym (m ≡ n)), and
   P x is given by C [n] ≡ C [n] (i.e. refl).
  -}

  -- Application of the conversion rule fix-f.
  proof₀₋₁ : ∀ m n → fix₁ gcdh · m · n ≡ gcd-s₁ m n
  proof₀₋₁ m n = subst (λ x → x · m · n ≡ gcdh (fix₁ gcdh) · m · n)
                       (sym (fix-f gcdh))
                       refl

  -- Application of the first argument.
  proof₁₋₂ : ∀ m n → gcd-s₁ m n ≡ gcd-s₂ m · n
  proof₁₋₂ m n = subst (λ x → x · n ≡ gcd-s₂ m · n)
                       (sym (beta gcd-s₂ m))
                       refl

  -- Second argument application.
  proof₂₋₃ : ∀ m n → gcd-s₂ m · n ≡ gcd-s₃ m n
  proof₂₋₃ m n  = beta (gcd-s₃ m) n

  -- Conversion (first if_then_else) 'iszero₁ n = b' using that proof.
  proof₃₋₄ : ∀ m n b → iszero₁ n ≡ b → gcd-s₃ m n ≡ gcd-s₄ m n b
  proof₃₋₄ m n b h = subst (λ x → gcd-s₄ m n x ≡ gcd-s₄ m n b)
                           (sym h)
                           refl

  -- Conversion first if_then_else when 'if true ...' using if-true.
  proof₄₋₅ : ∀ m n → gcd-s₄ m n true ≡ gcd-s₅ m
  proof₄₋₅ m _ = if-true (gcd-s₅ m)

  -- Conversion first if_then_else when 'if false ...' using if-false.
  proof₄₋₆ : ∀ m n → gcd-s₄ m n false ≡ gcd-s₆ m n
  proof₄₋₆ m n = if-false (gcd-s₆ m n)

  -- -- Conversion (second if_then_else) 'iszero₁ m = b' using that proof.
  proof₅₋₇ : ∀ m b → iszero₁ m ≡ b → gcd-s₅ m ≡ gcd-s₇ m b
  proof₅₋₇ m b h = subst (λ x → gcd-s₇ m x ≡ gcd-s₇ m b)
                         (sym h)
                         refl

  -- Conversion (third if_then_else) 'iszero₁ m = b' using that proof.
  proof₆₋₈ : ∀ m n b → iszero₁ m ≡ b → gcd-s₆ m n ≡ gcd-s₈ m n b
  proof₆₋₈ m n b h = subst (λ x → gcd-s₈ m n x ≡ gcd-s₈ m n b)
                           (sym h)
                           refl

  -- Conversion second if_then_else when 'if true ...' using if-true.
  proof₇₊ : ∀ m → gcd-s₇ m true ≡ loop
  proof₇₊ _ = if-true loop

  -- Conversion second if_then_else when 'if false ...' using if-false.
  proof₇₋ : ∀ m → gcd-s₇ m false ≡ m
  proof₇₋ m = if-false m

  -- Conversion third if_then_else when 'if true ...' using if-true.
  proof₈₊ : ∀ m n → gcd-s₈ m n true ≡ n
  proof₈₊ _ n = if-true n

  -- Conversion third if_then_else when 'if false ...' using if-false.
  proof₈₋₉ : ∀ m n → gcd-s₈ m n false ≡ gcd-s₉ m n
  proof₈₋₉ m n = if-false (gcd-s₉ m n)

  -- Conversion (fourth if_then_else) 'gt m n = b' using that proof.
  proof₉₋₁₀ : ∀ m n b → m > n ≡ b → gcd-s₉ m n ≡ gcd-s₁₀ m n b
  proof₉₋₁₀ m n b h = subst (λ x → gcd-s₁₀ m n x ≡ gcd-s₁₀ m n b)
                            (sym h)
                            refl

  -- Conversion fourth if_then_else when 'if true ...' using if-true.
  proof₁₀₊ : ∀ m n → gcd-s₁₀ m n true ≡ fix₁ gcdh · (m ∸ n) · n
  proof₁₀₊ m n = if-true (fix₁ gcdh · (m ∸ n) · n)

  -- Conversion fourth if_then_else when 'if was ...' using if-false.
  proof₁₀₋ : ∀ m n → gcd-s₁₀ m n false ≡ fix₁ gcdh · m · (n ∸ m)
  proof₁₀₋ m n = if-false (fix₁ gcdh · m · (n ∸ m))

------------------------------------------------------------------------------
-- The five equations for gcd

-- First equation.
-- We do not use this equation for reasoning about gcd.
gcd-00 : gcd zero zero ≡ loop
gcd-00 =
  begin
    gcd zero zero         ≡⟨ proof₀₋₁ zero zero ⟩
    gcd-s₁ zero zero      ≡⟨ proof₁₋₂ zero zero ⟩
    gcd-s₂ zero · zero    ≡⟨ proof₂₋₃ zero zero ⟩
    gcd-s₃ zero zero      ≡⟨ proof₃₋₄ zero zero true iszero-0 ⟩
    gcd-s₄ zero zero true ≡⟨ proof₄₋₅ zero zero ⟩
    gcd-s₅ zero           ≡⟨ proof₅₋₇ zero true iszero-0 ⟩
    gcd-s₇ zero true      ≡⟨ proof₇₊  zero ⟩
    loop
  ∎

-- Second equation.
gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
gcd-S0 n =
  begin
    gcd (succ₁ n) zero         ≡⟨ proof₀₋₁ (succ₁ n) zero ⟩
    gcd-s₁ (succ₁ n) zero      ≡⟨ proof₁₋₂ (succ₁ n) zero ⟩
    gcd-s₂ (succ₁ n) · zero    ≡⟨ proof₂₋₃ (succ₁ n) zero ⟩
    gcd-s₃ (succ₁ n) zero      ≡⟨ proof₃₋₄ (succ₁ n) zero true iszero-0 ⟩
    gcd-s₄ (succ₁ n) zero true ≡⟨ proof₄₋₅ (succ₁ n) zero ⟩
    gcd-s₅ (succ₁ n)           ≡⟨ proof₅₋₇ (succ₁ n) false (iszero-S n) ⟩
    gcd-s₇ (succ₁ n) false     ≡⟨ proof₇₋  (succ₁ n) ⟩
    succ₁ n
  ∎

-- Third equation.
gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
gcd-0S n =
  begin
    gcd zero (succ₁ n)          ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
    gcd-s₁ zero (succ₁ n)       ≡⟨ proof₁₋₂ zero (succ₁ n) ⟩
    gcd-s₂ zero · (succ₁ n)     ≡⟨ proof₂₋₃ zero (succ₁ n) ⟩
    gcd-s₃ zero (succ₁ n)       ≡⟨ proof₃₋₄ zero (succ₁ n) false (iszero-S n) ⟩
    gcd-s₄ zero (succ₁ n) false ≡⟨ proof₄₋₆ zero (succ₁ n) ⟩
    gcd-s₆ zero (succ₁ n)       ≡⟨ proof₆₋₈ zero (succ₁ n) true iszero-0 ⟩
    gcd-s₈ zero (succ₁ n) true  ≡⟨ proof₈₊  zero (succ₁ n) ⟩
    succ₁ n
  ∎

-- Fourth equation.
gcd-S>S : ∀ m n → GT (succ₁ m) (succ₁ n) →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)

gcd-S>S m n Sm>Sn =
  begin
    gcd (succ₁ m) (succ₁ n)          ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
    gcd-s₁ (succ₁ m) (succ₁ n)       ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
    gcd-s₂ (succ₁ m) · (succ₁ n)     ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
    gcd-s₃ (succ₁ m) (succ₁ n)       ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n)
                                                 false (iszero-S n)
                                     ⟩
    gcd-s₄ (succ₁ m) (succ₁ n) false ≡⟨ proof₄₋₆ (succ₁ m) (succ₁ n) ⟩
    gcd-s₆ (succ₁ m) (succ₁ n)       ≡⟨ proof₆₋₈ (succ₁ m) (succ₁ n)
                                                 false (iszero-S m)
                                     ⟩
    gcd-s₈ (succ₁ m) (succ₁ n) false ≡⟨ proof₈₋₉ (succ₁ m) (succ₁ n) ⟩
    gcd-s₉ (succ₁ m) (succ₁ n)       ≡⟨ proof₉₋₁₀ (succ₁ m) (succ₁ n) true Sm>Sn ⟩
    gcd-s₁₀ (succ₁ m) (succ₁ n) true ≡⟨ proof₁₀₊  (succ₁ m) (succ₁ n) ⟩
    fix₁ gcdh · (succ₁ m ∸ succ₁ n) · succ₁ n
  ∎

-- Fifth equation.
gcd-S≯S : ∀ m n → NGT (succ₁ m) (succ₁ n) →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
gcd-S≯S m n Sm≯Sn =
  begin
    gcd (succ₁ m) (succ₁ n)           ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
    gcd-s₁ (succ₁ m) (succ₁ n)        ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
    gcd-s₂ (succ₁ m) · (succ₁ n)      ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
    gcd-s₃ (succ₁ m) (succ₁ n)        ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n)
                                                false (iszero-S n)
                                      ⟩
    gcd-s₄ (succ₁ m) (succ₁ n) false  ≡⟨ proof₄₋₆ (succ₁ m) (succ₁ n) ⟩
    gcd-s₆ (succ₁ m) (succ₁ n)        ≡⟨ proof₆₋₈ (succ₁ m) (succ₁ n)
                                                  false (iszero-S m)
                                      ⟩
    gcd-s₈ (succ₁ m) (succ₁ n) false  ≡⟨ proof₈₋₉ (succ₁ m) (succ₁ n) ⟩
    gcd-s₉ (succ₁ m) (succ₁ n)        ≡⟨ proof₉₋₁₀ (succ₁ m) (succ₁ n)
                                                   false
                                                   Sm≯Sn
                                      ⟩
    gcd-s₁₀ (succ₁ m) (succ₁ n) false ≡⟨ proof₁₀₋ (succ₁ m) (succ₁ n) ⟩
    fix₁ gcdh · succ₁ m · (succ₁ n ∸ succ₁ m)
  ∎
