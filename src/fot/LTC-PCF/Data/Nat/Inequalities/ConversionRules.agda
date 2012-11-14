------------------------------------------------------------------------------
-- Conversion rules for inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.ConversionRules where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------

private

  -- Before to prove some properties for lt it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (lt-s₁,
  -- lt-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q, e.g.
  --
  -- proof₁→proof₂ : ∀ m n → lt-s₂ m n → lt-s₃ m n.

  -- The terms lt-00, lt-0S, lt-S0, and lt-SS show the use of the
  -- states lt-s₁, lt-s₂, ..., and the proofs associated with the
  -- execution steps.

  ----------------------------------------------------------------------
  -- The steps of lt.

  -- Initially, the conversion rule fix-eq is applied.
  lt-s₁ : D → D → D
  lt-s₁ m n = lth (fix lth) · m · n

  -- First argument application.
  lt-s₂ : D → D
  lt-s₂ m = lam (λ n →
               if (iszero₁ n)
                  then false
                  else (if (iszero₁ m)
                           then true
                           else (fix lth · pred₁ m · pred₁ n)))


  -- Second argument application.
  lt-s₃ : D → D → D
  lt-s₃ m n = if (iszero₁ n)
                 then false
                 else (if (iszero₁ m)
                          then true
                          else (fix lth · pred₁ m · pred₁ n))

  -- Reduction iszero₁ n ≡ b.
  lt-s₄ : D → D → D → D
  lt-s₄ m n b = if b
                   then false
                   else (if (iszero₁ m)
                            then true
                            else (fix lth · pred₁ m · pred₁ n))

  -- Reduction iszero₁ n ≡ true.
  -- It should be
  -- lt-s₅ : D → D → D
  -- lt-s₅ m n = false
  -- but we do not give a name to this step.

  -- Reduction iszero₁ n ≡ false.
  lt-s₅ : D → D → D
  lt-s₅ m n = if (iszero₁ m)
                 then true
                 else (fix lth · pred₁ m · pred₁ n)


  -- Reduction iszero₁ m ≡ b.
  lt-s₆ : D → D → D → D
  lt-s₆ m n b = if b
                   then true
                   else (fix lth · pred₁ m · pred₁ n)

  -- Reduction iszero₁ m ≡ true.
  -- It should be
  -- lt-s₇ : D → D → D
  -- lt-s₇ m n = true
  -- but we do not give a name to this step.

   -- Reduction iszero₁ m ≡ false.
  lt-s₇ : D → D → D
  lt-s₇ m n = fix lth · pred₁ m · pred₁ n

  -- Reduction pred₁ (succ m) ≡ m.
  lt-s₈ : D → D → D
  lt-s₈ m n = fix lth · m · pred₁ n

  -- Reduction pred₁ (succ n) ≡ n.
  lt-s₉ : D → D → D
  lt-s₉ m n = fix lth · m · n

  ----------------------------------------------------------------------
  -- The execution steps

  {-

    To prove the execution steps, e.g.

    proof₃→proof₄ : ∀ m n → lt-s₃ m n → lt-s₄ m n)

    we usually need to prove that

                         C [m] ≡ C [n]    (1)

    given that
                             m ≡ n,       (2)

    where (2) is a conversion rule usually.

    We prove (1) using

    subst : ∀ {x y} (A : D → Set) → x ≡ y → A x → A y

    where
      • P is given by λ t → C [m] ≡ C [t],
      • x ≡ y is given m ≡ n, and
      • P x is given by C [m] ≡ C [m] (i.e. refl).
  -}

  -- Application of the conversion rule fix-eq.
  proof₀₋₁ : ∀ m n → fix lth · m · n  ≡ lt-s₁ m n
  proof₀₋₁ m n = subst (λ x → x · m · n  ≡
                              lth (fix lth) · m · n )
                       (sym (fix-eq lth ))
                       refl

  -- Application of the first argument.
  proof₁₋₂ : ∀ m n → lt-s₁ m n ≡ lt-s₂ m · n
  proof₁₋₂ m n = subst (λ x → x · n ≡ lt-s₂ m · n)
                       (sym (beta lt-s₂ m))
                       refl

  -- Application of the second argument.
  proof₂₋₃ : ∀ m n → lt-s₂ m · n ≡ lt-s₃ m n
  proof₂₋₃ m n = beta (lt-s₃ m) n


  -- Reduction isZero n ≡ b using that proof.
  proof₃₋₄ : ∀ m n b → iszero₁ n ≡ b → lt-s₃ m n ≡ lt-s₄ m n b
  proof₃₋₄ m n b prf = subst (λ x → lt-s₄ m n x ≡ lt-s₄ m n b )
                             (sym prf )
                             refl

  -- Reduction of iszero₁ n ≡ true using the conversion rule if-true.
  proof₄₊ : ∀ m n → lt-s₄ m n true ≡ false
  proof₄₊ m n = if-true false

  -- Reduction of iszero₁ n ≡ false ... using the conversion rule
  -- if-false.
  proof₄₋₅ : ∀ m n → lt-s₄ m n false ≡ lt-s₅ m n
  proof₄₋₅ m n = if-false (lt-s₅ m n)


  -- Reduction iszero₁ m ≡ b using that proof.
  proof₅₋₆ : ∀ m n b → iszero₁ m ≡ b → lt-s₅ m n ≡ lt-s₆ m n b
  proof₅₋₆ m n b prf = subst (λ x → lt-s₆ m n x ≡ lt-s₆ m n b )
                             (sym prf )
                             refl

  -- Reduction of iszero₁ m ≡ true using the conversion rule if-true.
  proof₆₊ : ∀ m n → lt-s₆ m n true ≡ true
  proof₆₊ m n = if-true true

  -- Reduction of iszero₁ m ≡ false ... using the conversion rule
  -- if-false.
  proof₆₋₇ : ∀ m n → lt-s₆ m n false ≡ lt-s₇ m n
  proof₆₋₇ m n = if-false (lt-s₇ m n)

  -- Reduction pred (succ m) ≡ m using the conversion rule pred-S.
  proof₇₋₈ : ∀ m n → lt-s₇ (succ₁ m) n  ≡ lt-s₈ m n
  proof₇₋₈ m n = subst (λ x → lt-s₈ x n ≡ lt-s₈ m n)
                       (sym (pred-S m ))
                       refl

  -- Reduction pred (succ n) ≡ n using the conversion rule pred-S.
  proof₈₋₉ : ∀ m n → lt-s₈ m (succ₁ n)  ≡ lt-s₉ m n
  proof₈₋₉ m n = subst (λ x → lt-s₉ m x ≡ lt-s₉ m n)
                       (sym (pred-S n ))
                       refl

------------------------------------------------------------------------------

private
  X≮0 : ∀ n → n ≮ zero
  X≮0 n = fix lth · n · zero  ≡⟨ proof₀₋₁ n zero ⟩
          lt-s₁ n zero        ≡⟨ proof₁₋₂ n zero ⟩
          lt-s₂ n · zero      ≡⟨ proof₂₋₃ n zero ⟩
          lt-s₃ n zero        ≡⟨ proof₃₋₄ n zero true iszero-0 ⟩
          lt-s₄ n zero true   ≡⟨ proof₄₊ n zero ⟩
          false              ∎

lt-00 : zero ≮ zero
lt-00 = X≮0 zero

lt-0S : ∀ n → zero < succ₁ n
lt-0S n =
  fix lth · zero · (succ₁ n)    ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
  lt-s₁ zero (succ₁ n)          ≡⟨ proof₁₋₂ zero (succ₁ n) ⟩
  lt-s₂ zero · (succ₁ n)        ≡⟨ proof₂₋₃ zero (succ₁ n) ⟩
  lt-s₃ zero (succ₁ n)          ≡⟨ proof₃₋₄ zero (succ₁ n) false (iszero-S n) ⟩
  lt-s₄ zero (succ₁ n) false    ≡⟨ proof₄₋₅ zero (succ₁ n) ⟩
  lt-s₅ zero (succ₁ n)          ≡⟨ proof₅₋₆ zero (succ₁ n) true iszero-0 ⟩
  lt-s₆ zero (succ₁ n) true     ≡⟨ proof₆₊  zero (succ₁ n) ⟩
  true                         ∎

lt-S0 : ∀ n → succ₁ n ≮ zero
lt-S0 n = X≮0 (succ₁ n)

lt-SS : ∀ m n → lt (succ₁ m) (succ₁ n) ≡ lt m n
lt-SS m n =
  fix lth · (succ₁ m) · (succ₁ n)  ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  lt-s₁ (succ₁ m) (succ₁ n)        ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
  lt-s₂ (succ₁ m) · (succ₁ n)      ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
  lt-s₃ (succ₁ m) (succ₁ n)        ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  lt-s₄ (succ₁ m) (succ₁ n) false  ≡⟨ proof₄₋₅ (succ₁ m) (succ₁ n) ⟩
  lt-s₅ (succ₁ m) (succ₁ n)        ≡⟨ proof₅₋₆ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  lt-s₆ (succ₁ m) (succ₁ n) false  ≡⟨ proof₆₋₇ (succ₁ m) (succ₁ n) ⟩
  lt-s₇ (succ₁ m) (succ₁ n)        ≡⟨ proof₇₋₈ m (succ₁ n) ⟩
  lt-s₈ m (succ₁ n)                ≡⟨ proof₈₋₉ m n ⟩
  lt-s₉ m n                        ∎
