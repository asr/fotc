------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.EquationsI where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------

private

  -- Before to prove some properties for _<_ it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (<-s₁,
  -- <-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q, e.g.
  --
  -- proof₁→proof₂ : ∀ m n → <-s₂ m n → <-s₃ m n.

  -- The terms <-00, <-0S, <-S0, and <-SS show the use of the states
  -- <-s₁, <-s₂, ..., and the proofs associated with the execution
  -- steps.

  ----------------------------------------------------------------------
  -- The steps of _<_.

  -- Initially, the conversion rule fix-eq is applied.
  <-s₁ : D → D → D
  <-s₁ m n = lth (fix lth) · m · n

  -- First argument application.
  <-s₂ : D → D
  <-s₂ m = lam (λ n →
               if (iszero₁ n) then false
                  else (if (iszero₁ m) then true
                           else ((fix lth) · (pred₁ m) · (pred₁ n))))


  -- Second argument application.
  <-s₃ : D → D → D
  <-s₃ m n = if (iszero₁ n) then false
                else (if (iszero₁ m) then true
                         else ((fix lth) · (pred₁ m) · (pred₁ n)))

  -- Reduction iszero₁ n ≡ b.
  <-s₄ : D → D → D → D
  <-s₄ m n b = if b then false
                  else (if (iszero₁ m) then true
                           else ((fix lth) · (pred₁ m) · (pred₁ n)))

  -- Reduction iszero₁ n ≡ true.
  -- It should be
  -- <-s₅ : D → D → D
  -- <-s₅ m n = false
  -- but we do not give a name to this step.

  -- Reduction iszero₁ n ≡ false.
  <-s₅ : D → D → D
  <-s₅ m n = if (iszero₁ m) then true
                 else ((fix lth) · (pred₁ m) · (pred₁ n))


  -- Reduction iszero₁ m ≡ b.
  <-s₆ : D → D → D → D
  <-s₆ m n b = if b then true
                  else ((fix lth) · (pred₁ m) · (pred₁ n))

  -- Reduction iszero₁ m ≡ true.
  -- It should be
  -- <-s₇ : D → D → D
  -- <-s₇ m n = true
  -- but we do not give a name to this step.

   -- Reduction iszero₁ m ≡ false.
  <-s₇ : D → D → D
  <-s₇ m n = (fix lth) · (pred₁ m) · (pred₁ n)

  -- Reduction pred₁ (succ m) ≡ m.
  <-s₈ : D → D → D
  <-s₈ m n = (fix lth) · m · (pred₁ n)

  -- Reduction pred₁ (succ n) ≡ n.
  <-s₉ : D → D → D
  <-s₉ m n = (fix lth) · m · n

  ----------------------------------------------------------------------
  -- The execution steps

  {-

    To prove the execution steps, e.g.

    proof₃→proof₄ : ∀ m n → <-s₃ m n → <-s₄ m n)

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
  proof₀₋₁ : (m n : D) → fix lth · m · n  ≡ <-s₁ m n
  proof₀₋₁ m n = subst (λ x → x · m · n  ≡
                              lth (fix lth) · m · n )
                       (sym (fix-eq lth ))
                       refl

  -- Application of the first argument.
  proof₁₋₂ : (m n : D) → <-s₁ m n ≡ <-s₂ m · n
  proof₁₋₂ m n = subst (λ x → x · n ≡ <-s₂ m · n)
                       (sym (beta <-s₂ m))
                       refl

  -- Application of the second argument.
  proof₂₋₃ : (m n : D) → <-s₂ m · n ≡ <-s₃ m n
  proof₂₋₃ m n = beta (<-s₃ m) n


  -- Reduction isZero n ≡ b using that proof.
  proof₃₋₄ : (m n b : D) → iszero₁ n ≡ b →
             <-s₃ m n ≡ <-s₄ m n b
  proof₃₋₄ m n b prf = subst (λ x → <-s₄ m n x ≡ <-s₄ m n b )
                             (sym prf )
                             refl

  -- Reduction of iszero₁ n ≡ true using the conversion rule if-true.
  proof₄₊ : (m n : D) → <-s₄ m n true ≡ false
  proof₄₊ m n = if-true false

  -- Reduction of iszero₁ n ≡ false ... using the conversion rule
  -- if-false.
  proof₄₋₅ : (m n : D) → <-s₄ m n false ≡ <-s₅ m n
  proof₄₋₅ m n = if-false (<-s₅ m n)


  -- Reduction iszero₁ m ≡ b using that proof.
  proof₅₋₆ : (m n b : D) → iszero₁ m ≡ b →
             <-s₅ m n ≡ <-s₆ m n b
  proof₅₋₆ m n b prf = subst (λ x → <-s₆ m n x ≡ <-s₆ m n b )
                             (sym prf )
                             refl

  -- Reduction of iszero₁ m ≡ true using the conversion rule if-true.
  proof₆₊ : (m n : D) → <-s₆ m n true ≡ true
  proof₆₊ m n = if-true true

  -- Reduction of iszero₁ m ≡ false ... using the conversion rule
  -- if-false.
  proof₆₋₇ : (m n : D) → <-s₆ m n false ≡ <-s₇ m n
  proof₆₋₇ m n = if-false (<-s₇ m n)

  -- Reduction pred (succ m) ≡ m using the conversion rule pred-S.
  proof₇₋₈ : (m n : D) → <-s₇ (succ₁ m) n  ≡ <-s₈ m n
  proof₇₋₈ m n = subst (λ x → <-s₈ x n ≡ <-s₈ m n)
                       (sym (pred-S m ))
                       refl

  -- Reduction pred (succ n) ≡ n using the conversion rule pred-S.
  proof₈₋₉ : (m n : D) → <-s₈ m (succ₁ n)  ≡ <-s₉ m n
  proof₈₋₉ m n = subst (λ x → <-s₉ m x ≡ <-s₉ m n)
                       (sym (pred-S n ))
                       refl

------------------------------------------------------------------------------

private
  -- NB. This property is true for *any* n.
  X≮0 : ∀ n → NLT n zero
  X≮0 n = fix lth · n · zero ≡⟨ proof₀₋₁ n zero ⟩
          <-s₁ n zero        ≡⟨ proof₁₋₂ n zero ⟩
          <-s₂ n · zero      ≡⟨ proof₂₋₃ n zero ⟩
          <-s₃ n zero        ≡⟨ proof₃₋₄ n zero true iszero-0 ⟩
          <-s₄ n zero true   ≡⟨ proof₄₊ n zero ⟩
          false              ∎

<-00 : NLT zero zero
<-00 = X≮0 zero

<-0S : ∀ n → LT zero (succ₁ n)
<-0S n =
  fix lth · zero · (succ₁ n)   ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
  <-s₁ zero (succ₁ n)          ≡⟨ proof₁₋₂ zero (succ₁ n) ⟩
  <-s₂ zero · (succ₁ n)        ≡⟨ proof₂₋₃ zero (succ₁ n) ⟩
  <-s₃ zero (succ₁ n)          ≡⟨ proof₃₋₄ zero (succ₁ n) false (iszero-S n) ⟩
  <-s₄ zero (succ₁ n) false    ≡⟨ proof₄₋₅ zero (succ₁ n) ⟩
  <-s₅ zero (succ₁ n)          ≡⟨ proof₅₋₆ zero (succ₁ n) true iszero-0 ⟩
  <-s₆ zero (succ₁ n) true     ≡⟨ proof₆₊  zero (succ₁ n) ⟩
  true                         ∎

<-S0 : ∀ n → NLT (succ₁ n) zero
<-S0 n = X≮0 (succ₁ n)

<-SS : ∀ m n → succ₁ m < succ₁ n ≡ m < n
<-SS m n =
  fix lth · (succ₁ m) · (succ₁ n) ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  <-s₁ (succ₁ m) (succ₁ n)        ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
  <-s₂ (succ₁ m) · (succ₁ n)      ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
  <-s₃ (succ₁ m) (succ₁ n)        ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  <-s₄ (succ₁ m) (succ₁ n) false  ≡⟨ proof₄₋₅ (succ₁ m) (succ₁ n) ⟩
  <-s₅ (succ₁ m) (succ₁ n)        ≡⟨ proof₅₋₆ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  <-s₆ (succ₁ m) (succ₁ n) false  ≡⟨ proof₆₋₇ (succ₁ m) (succ₁ n) ⟩
  <-s₇ (succ₁ m) (succ₁ n)        ≡⟨ proof₇₋₈ m (succ₁ n) ⟩
  <-s₈ m (succ₁ n)                ≡⟨ proof₈₋₉ m n ⟩
  <-s₉ m n                        ∎
